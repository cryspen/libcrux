use crate::{
    constants::COEFFICIENTS_IN_RING_ELEMENT, encoding, polynomial::PolynomialRingElement,
    simd::traits::Operations, VerificationError,
};

#[inline(always)]
#[hax_lib::fstar::verification_status(panic_free)]
pub(crate) fn serialize<SIMDUnit: Operations>(
    commitment_hash: &[u8],
    signer_response: &[PolynomialRingElement<SIMDUnit>],
    hint: &[[i32; COEFFICIENTS_IN_RING_ELEMENT]],
    commitment_hash_size: usize,
    columns_in_a: usize,
    rows_in_a: usize,
    gamma1_exponent: usize,
    gamma1_ring_element_size: usize,
    max_ones_in_hint: usize,
    signature: &mut [u8],
) {
    hax_lib::fstar!("admit ()");
    let mut offset = 0;

    signature[offset..offset + commitment_hash_size].copy_from_slice(commitment_hash);
    offset += commitment_hash_size;

    for i in 0..columns_in_a {
        encoding::gamma1::serialize::<SIMDUnit>(
            &signer_response[i],
            &mut signature[offset..offset + gamma1_ring_element_size],
            gamma1_exponent,
        );
        offset += gamma1_ring_element_size;
    }

    let mut true_hints_seen = 0;

    // FIPS 204 §7.2 Algorithm 20 (HintBitPack) requires that bytes in
    // y[Index..ω] (between the last written hint index and the start of
    // the per-row offsets) are zero, and HintBitUnpack rejects nonzero
    // padding (§7.2 Algorithm 21).  Explicitly zero the range we'll
    // write into so we don't depend on the caller having pre-zeroed the
    // signature buffer.
    for k in 0..(max_ones_in_hint + rows_in_a) {
        signature[offset + k] = 0;
    }

    // Unfortunately the following does not go through hax:
    //
    //     let hint_serialized = &mut signature[offset..];
    //
    // Instead, we have to mutate signature[offset + ..] directly.
    for i in 0..rows_in_a {
        // for (j, hint) in self.hint[i].into_iter().enumerate() {
        for j in 0..hint[i].len() {
            if hint[i][j] == 1 {
                signature[offset + true_hints_seen] = j as u8;
                true_hints_seen += 1;
            }
        }
        signature[offset + max_ones_in_hint + i] = true_hints_seen as u8;
    }
}

#[inline(always)]
#[hax_lib::fstar::verification_status(panic_free)]
#[hax_lib::fstar::before(r#"#push-options "--z3rlimit 1500 --fuel 2 --ifuel 4 --split_queries always""#)]
#[hax_lib::fstar::after(r#"#pop-options"#)]
// FIPS 204 §7.2 (sigDecode) sizing: the serialized signature is the
// concatenation `commitment_hash || signer_response || hint`, with
// `|signer_response| = columns_in_a * gamma1_ring_element_size` and
// `|hint| = max_ones_in_hint + rows_in_a`.  The output buffers must
// match the per-vector dimensions.  `gamma1_exponent ∈ {17, 19}` and
// `gamma1_ring_element_size == 32 * (1 + gamma1_exponent)` are
// required by the inner `gamma1::deserialize` callee.
#[hax_lib::requires(fstar!(r#"
    (v $gamma1_exponent == 17 \/ v $gamma1_exponent == 19) /\
    v $gamma1_ring_element_size == 32 * (1 + v $gamma1_exponent) /\
    v $rows_in_a > 0 /\
    v $signature_size ==
        v $commitment_hash_size +
        v $gamma1_ring_element_size * v $columns_in_a +
        v $max_ones_in_hint + v $rows_in_a /\
    Seq.length $serialized == v $signature_size /\
    Seq.length $out_commitment_hash >= v $commitment_hash_size /\
    Seq.length $out_signer_response == v $columns_in_a /\
    Seq.length $out_hint == v $rows_in_a"#))]
pub(crate) fn deserialize<SIMDUnit: Operations>(
    columns_in_a: usize,
    rows_in_a: usize,
    commitment_hash_size: usize,
    gamma1_exponent: usize,
    gamma1_ring_element_size: usize,
    max_ones_in_hint: usize,
    signature_size: usize,
    serialized: &[u8],
    out_commitment_hash: &mut [u8],
    out_signer_response: &mut [PolynomialRingElement<SIMDUnit>],
    out_hint: &mut [[i32; COEFFICIENTS_IN_RING_ELEMENT]],
) -> Result<(), VerificationError> {
    #[cfg(not(eurydice))]
    debug_assert!(serialized.len() == signature_size);

    let (commitment_hash, rest_of_serialized) = serialized.split_at(commitment_hash_size);
    out_commitment_hash[0..commitment_hash_size].copy_from_slice(commitment_hash);

    let (signer_response_serialized, hint_serialized) =
        rest_of_serialized.split_at(gamma1_ring_element_size * columns_in_a);
    // Anchor the post-split lengths so the loop invariants below can
    // refer to `Seq.length signer_response_serialized` and
    // `Seq.length hint_serialized` directly.
    hax_lib::fstar!(r#"
        assert (Seq.length $rest_of_serialized ==
                  v $signature_size - v $commitment_hash_size);
        assert (Seq.length $signer_response_serialized ==
                  v $gamma1_ring_element_size * v $columns_in_a);
        assert (Seq.length $hint_serialized ==
                  v $max_ones_in_hint + v $rows_in_a)"#);

    for i in 0..columns_in_a {
        hax_lib::loop_invariant!(|i: usize| fstar!(r#"
            v $i <= v $columns_in_a /\
            (v $gamma1_exponent == 17 \/ v $gamma1_exponent == 19) /\
            v $gamma1_ring_element_size == 32 * (1 + v $gamma1_exponent) /\
            Seq.length $signer_response_serialized ==
                v $gamma1_ring_element_size * v $columns_in_a /\
            Seq.length $out_signer_response == v $columns_in_a"#));
        encoding::gamma1::deserialize::<SIMDUnit>(
            gamma1_exponent,
            &signer_response_serialized
                [i * gamma1_ring_element_size..(i + 1) * gamma1_ring_element_size],
            &mut out_signer_response[i],
        );
    }

    // Initialise out_hint to all-zeros up front, so that on the Err path
    // the function has a well-defined post-state (each [i][j] is 0 or 1,
    // never an unrelated value carried over from a recycled buffer).
    // Combined with gating set_hint on `!malformed_hint` below, this gives
    // the F* post a clean shape: Err ⇒ out_hint contains a prefix of the
    // spec decoding followed by zeros, which is what `verify_internal`'s
    // proof obligation needs.
    for i in 0..rows_in_a {
        hax_lib::loop_invariant!(|i: usize| fstar!(r#"
            v $i <= v $rows_in_a /\ Seq.length $out_hint == v $rows_in_a"#));
        for j in 0..COEFFICIENTS_IN_RING_ELEMENT {
            hax_lib::loop_invariant!(|j: usize| fstar!(r#"
                v $j <= 256 /\
                v $i < v $rows_in_a /\
                Seq.length $out_hint == v $rows_in_a"#));
            out_hint[i][j] = 0;
        }
    }
    // While there are several ways to encode the same hint vector, we
    // allow only one such encoding, to ensure strong unforgeability.
    // Two helpers carry the FIPS-mandated panic-freedom obligation
    // that PR 1348 fixed; the validate pass establishes the per-row
    // counter bounds, and the write pass commits the indices into
    // `out_hint`.  Splitting this way keeps each helper's loop
    // accumulator small (and so its fold_range init-state subtyping
    // check tractable).
    let (mut malformed_hint, previous_true_hints_seen) =
        validate_hint_rows(hint_serialized, max_ones_in_hint, rows_in_a);
    if !malformed_hint {
        write_hint_rows(hint_serialized, out_hint, max_ones_in_hint, rows_in_a);
    }

    for j in previous_true_hints_seen..max_ones_in_hint {
        hax_lib::loop_invariant!(|j: usize| fstar!(r#"
            v $j >= v $previous_true_hints_seen /\
            v $j <= v $max_ones_in_hint /\
            v $previous_true_hints_seen <= v $max_ones_in_hint /\
            Seq.length $hint_serialized == v $max_ones_in_hint + v $rows_in_a /\
            v $rows_in_a > 0"#));
        if hint_serialized[j] != 0 {
            // ensures padding indices are zero
            // return Err(VerificationError::MalformedHintError);
            malformed_hint = true;
            break;
        }
    }

    if malformed_hint {
        Err(VerificationError::MalformedHintError)
    } else {
        Ok(())
    }
}

#[inline(always)]
#[hax_lib::requires(i < out_hint.len() && j < 256)]
fn set_hint(out_hint: &mut [[i32; 256]], i: usize, j: usize) {
    out_hint[i][j] = 1
}

/// Validate the hint section's per-row cumulative counters and
/// strict-increase ordering of indices.  Returns
/// `(malformed_hint, previous_true_hints_seen)` — the first is `true`
/// iff a FIPS 204 §7.2 Algorithm 22 check failed; the second is the
/// final cumulative counter (used by the caller to scan the padding
/// zeros).  Read-only on `hint_serialized`; the loop accumulator is
/// just `(bool, usize)` so the fold_range init-state subtyping check
/// closes cleanly.
///
/// PR 1348's bug: guarded `previous < max_ones_in_hint` instead of
/// `current > max_ones_in_hint`, letting `current` exceed ω and the
/// inner index loop run past the slice bound.  F* refuses
/// panic-freedom for the buggy variant on the inner
/// `hint_serialized[j]` access.
#[hax_lib::fstar::verification_status(panic_free)]
#[hax_lib::fstar::before(r#"#push-options "--z3rlimit 200 --ifuel 2""#)]
#[hax_lib::fstar::after(r#"#pop-options"#)]
#[hax_lib::requires(fstar!(r#"
    Seq.length $hint_serialized == v $max_ones_in_hint + v $rows_in_a"#))]
fn validate_hint_rows(
    hint_serialized: &[u8],
    max_ones_in_hint: usize,
    rows_in_a: usize,
) -> (bool, usize) {
    let mut previous_true_hints_seen = 0usize;
    let mut malformed_hint = false;

    for i in 0..rows_in_a {
        hax_lib::loop_invariant!(|i: usize| fstar!(r#"
            v $i <= v $rows_in_a /\
            v $previous_true_hints_seen <= v $max_ones_in_hint /\
            Seq.length $hint_serialized == v $max_ones_in_hint + v $rows_in_a"#));
        if !malformed_hint {
            let current_true_hints_seen = hint_serialized[max_ones_in_hint + i] as usize;

            if (current_true_hints_seen < previous_true_hints_seen)
                || (current_true_hints_seen > max_ones_in_hint)
            {
                malformed_hint = true;
            } else {
                for j in previous_true_hints_seen..current_true_hints_seen {
                    hax_lib::loop_invariant!(|j: usize| fstar!(r#"
                        v $j >= v $previous_true_hints_seen /\
                        v $j <= v $current_true_hints_seen /\
                        v $current_true_hints_seen <= v $max_ones_in_hint /\
                        Seq.length $hint_serialized ==
                            v $max_ones_in_hint + v $rows_in_a"#));
                    if j > previous_true_hints_seen
                        && hint_serialized[j] <= hint_serialized[j - 1]
                    {
                        malformed_hint = true;
                    }
                }
                if !malformed_hint {
                    previous_true_hints_seen = current_true_hints_seen;
                }
            }
        }
    }

    (malformed_hint, previous_true_hints_seen)
}

/// Write the per-row hint indices into `out_hint`, assuming the row
/// cumulative-count and ordering invariants from `validate_hint_rows`
/// have already been checked.  Loop accumulator is just `out_hint`,
/// so the fold_range init-state refinement check closes cleanly.
#[hax_lib::fstar::verification_status(panic_free)]
#[hax_lib::fstar::before(r#"#push-options "--z3rlimit 200 --ifuel 2""#)]
#[hax_lib::fstar::after(r#"#pop-options"#)]
#[hax_lib::requires(fstar!(r#"
    Seq.length $hint_serialized == v $max_ones_in_hint + v $rows_in_a /\
    Seq.length $out_hint == v $rows_in_a"#))]
fn write_hint_rows(
    hint_serialized: &[u8],
    out_hint: &mut [[i32; COEFFICIENTS_IN_RING_ELEMENT]],
    max_ones_in_hint: usize,
    rows_in_a: usize,
) {
    let mut previous_true_hints_seen = 0usize;

    for i in 0..rows_in_a {
        hax_lib::loop_invariant!(|i: usize| fstar!(r#"
            v $i <= v $rows_in_a /\
            v $previous_true_hints_seen <= v $max_ones_in_hint /\
            Seq.length $hint_serialized == v $max_ones_in_hint + v $rows_in_a /\
            Seq.length $out_hint == v $rows_in_a"#));
        let current_true_hints_seen = hint_serialized[max_ones_in_hint + i] as usize;
        // Guard duplicates the validate_hint_rows check; it is also
        // necessary as a pre for the inner slice access below.
        if (current_true_hints_seen < previous_true_hints_seen)
            || (current_true_hints_seen > max_ones_in_hint)
        {
            // Should not be reachable when called after a successful
            // validate_hint_rows; defensive only.
        } else {
            for j in previous_true_hints_seen..current_true_hints_seen {
                hax_lib::loop_invariant!(|j: usize| fstar!(r#"
                    v $j >= v $previous_true_hints_seen /\
                    v $j <= v $current_true_hints_seen /\
                    v $current_true_hints_seen <= v $max_ones_in_hint /\
                    Seq.length $hint_serialized == v $max_ones_in_hint + v $rows_in_a /\
                    Seq.length $out_hint == v $rows_in_a /\
                    v $i < v $rows_in_a"#));
                set_hint(out_hint, i, hint_serialized[j] as usize);
            }
            previous_true_hints_seen = current_true_hints_seen;
        }
    }
}
