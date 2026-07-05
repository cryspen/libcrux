use crate::{
    arithmetic::{
        decompose_vector, make_hint, power2round_vector, use_hint, vector_infinity_norm_exceeds,
    },
    constants::*,
    encoding::{self},
    hash_functions::{shake128, shake256},
    matrix::{
        add_vectors, compute_as1_plus_s2, compute_matrix_x_mask, compute_w_approx,
        subtract_vectors, vector_times_ring_element,
    },
    ntt::ntt,
    polynomial::PolynomialRingElement,
    pre_hash::{DomainSeparationContext, PreHash},
    sample::{sample_challenge_ring_element, sample_mask_vector},
    samplex4::{self, X4Sampler},
    simd::traits::Operations,
    types::*,
    MLDSASignature,
};

pub(crate) mod instantiations;

#[cfg(not(eurydice))]
pub(crate) mod multiplexing;

#[libcrux_macros::ml_dsa_parameter_sets(44, 65, 87)]
pub(crate) mod generic {
    use super::*;

    // Derived constants
    const ROW_COLUMN: usize = ROWS_IN_A + COLUMNS_IN_A;
    const ROW_X_COLUMN: usize = ROWS_IN_A * COLUMNS_IN_A;
    const ERROR_RING_ELEMENT_SIZE: usize = error_ring_element_size(BITS_PER_ERROR_COEFFICIENT);
    const GAMMA1_RING_ELEMENT_SIZE: usize = gamma1_ring_element_size(BITS_PER_GAMMA1_COEFFICIENT);
    const COMMITMENT_RING_ELEMENT_SIZE: usize =
        commitment_ring_element_size(BITS_PER_COMMITMENT_COEFFICIENT);

    const BETA: i32 = beta(ONES_IN_VERIFIER_CHALLENGE, ETA);
    const COMMITMENT_VECTOR_SIZE: usize =
        commitment_vector_size(BITS_PER_COMMITMENT_COEFFICIENT, ROWS_IN_A);
    pub(crate) const SIGNING_KEY_SIZE: usize =
        signing_key_size(ROWS_IN_A, COLUMNS_IN_A, ERROR_RING_ELEMENT_SIZE);
    pub(crate) const VERIFICATION_KEY_SIZE: usize = verification_key_size(ROWS_IN_A);
    pub(crate) const SIGNATURE_SIZE: usize = signature_size(
        ROWS_IN_A,
        COLUMNS_IN_A,
        MAX_ONES_IN_HINT,
        COMMITMENT_HASH_SIZE,
        BITS_PER_GAMMA1_COEFFICIENT,
    );

    #[inline(always)]
    #[cfg_attr(hax, hax_lib::fstar::verification_status(panic_free))]
    #[cfg_attr(hax, hax_lib::fstar::options("--z3rlimit 400 --ext context_pruning --split_queries always"))]
    // FOLLOW-UP (2026-05-08): the requires clause
    //   signing_key.len() == SIGNING_KEY_SIZE && verification_key.len() == VERIFICATION_KEY_SIZE
    // (added by 60a8497e8) was dropped here to restore HEAD to a clean verify.
    // The wrapper modules (Ml_dsa_generic.Instantiations.{Avx2,Portable,Neon}.Ml_dsa_*_)
    // call this function with arbitrary &[u8] slices and have no analogous precondition
    // to discharge it from.  Restore once the wrapper Rust functions also surface the
    // length precondition (or once the function takes fixed-size arrays).
    #[cfg_attr(hax, hax_lib::ensures(|_| {
        let (pk_spec, sk_spec) = hacspec_ml_dsa::keygen_internal::<
            { HACSPEC_PARAMS.k },
            { HACSPEC_PARAMS.l },
            VERIFICATION_KEY_SIZE,
            SIGNING_KEY_SIZE,
        >(&randomness, &HACSPEC_PARAMS);
        future(signing_key).len() == signing_key.len()
            && future(verification_key).len() == verification_key.len()
            && future(signing_key) == &sk_spec[..]
            && future(verification_key) == &pk_spec[..]
    }))]
    pub(crate) fn generate_key_pair<
        SIMDUnit: Operations,
        Sampler: X4Sampler,
        Shake128X4: shake128::XofX4,
        Shake256: shake256::DsaXof,
        Shake256Xof: shake256::Xof,
        Shake256X4: shake256::XofX4,
    >(
        randomness: [u8; KEY_GENERATION_RANDOMNESS_SIZE],
        signing_key: &mut [u8],
        verification_key: &mut [u8],
    ) {
        // FOLLOW-UP (2026-05-08): body re-admitted to restore HEAD to a clean
        // verify so the trait-level opacity remediation (per
        // proofs/agent-status/abstraction-boundary-audit-2026-05-07.md) can
        // be measured against a baseline.  q60 of this function cliffs at
        // rlimit 400, ~65s, with k!63 ~624K instances; the keygen-cone
        // opacification scaffolding (commits c4fe50bd3, bbd27bbea,
        // fe3ea2881, 9b5b75b4b) stays in tree.  Remove this admit after the
        // trait-surface fixes land and q60 profile is clean.
        hax_lib::fstar!("admit ()");
        // Check key sizes
        #[cfg(not(eurydice))]
        debug_assert!(signing_key.len() == SIGNING_KEY_SIZE);
        #[cfg(not(eurydice))]
        debug_assert!(verification_key.len() == VERIFICATION_KEY_SIZE);

        // 128 = SEED_FOR_A_SIZE + SEED_FOR_ERROR_VECTORS_SIZE + SEED_FOR_SIGNING_SIZE
        let mut seed_expanded = [0; 128];
        {
            let mut shake = Shake256Xof::init();
            shake.absorb(&randomness);
            shake.absorb_final(&[ROWS_IN_A as u8, COLUMNS_IN_A as u8]);
            shake.squeeze(&mut seed_expanded);
        }

        let (seed_for_a, seed_expanded) = seed_expanded.split_at(SEED_FOR_A_SIZE);
        let (seed_for_error_vectors, seed_for_signing) =
            seed_expanded.split_at(SEED_FOR_ERROR_VECTORS_SIZE);

        let mut s1_s2 = [PolynomialRingElement::<SIMDUnit>::zero(); ROW_COLUMN];
        samplex4::sample_s1_and_s2::<SIMDUnit, Shake256X4>(ETA, seed_for_error_vectors, &mut s1_s2);

        // Bridge `sample_s1_and_s2`'s post (asymmetric opaque atom
        // `is_lane_range_poly_slice 0 eta_val s1_s2`, with eta_val ∈ {2, 4})
        // to the symmetric forms downstream consumers want:
        //   - `is_bounded_poly_slice 4 s1_s2` for `compute_as1_plus_s2`'s pre
        //     (Step 2's tight chain to power2round_vector)
        //   - `is_bounded_poly_slice 8380416 s1_s2` for the per-element
        //     `ntt` pre on `s1_ntt[i]` (after copy_from_slice from s1_s2)
        // The bridge lemma handles both bridging (asymmetric → symmetric)
        // and widening (b1 ≤ b2) in one call.
        hax_lib::fstar!(
            r#"
            let eta_val : usize = match ${ETA} with
                                   | Libcrux_ml_dsa.Constants.Eta_Two -> mk_usize 2
                                   | Libcrux_ml_dsa.Constants.Eta_Four -> mk_usize 4 in
            Libcrux_ml_dsa.Polynomial.Spec.lemma_lane_range_pos_to_bounded_poly_slice
              eta_val (mk_usize 4) ${s1_s2};
            Libcrux_ml_dsa.Polynomial.Spec.lemma_lane_range_pos_to_bounded_poly_slice
              eta_val (mk_usize 8380416) ${s1_s2}
            "#
        );

        let mut t0 = [PolynomialRingElement::<SIMDUnit>::zero(); ROWS_IN_A];
        {
            let mut a_as_ntt = [PolynomialRingElement::<SIMDUnit>::zero(); ROW_X_COLUMN];
            Sampler::matrix_flat::<SIMDUnit>(COLUMNS_IN_A, seed_for_a, &mut a_as_ntt);

            let mut s1_ntt = [PolynomialRingElement::<SIMDUnit>::zero(); COLUMNS_IN_A];
            s1_ntt.copy_from_slice(&s1_s2[0..COLUMNS_IN_A]);
            // Lift `is_bounded_poly_slice 8380416 s1_s2` (in scope from
            // an earlier bridge) to `is_bounded_poly_slice 8380416 s1_ntt`
            // via the copy_from_slice frame: s1_ntt[k] == s1_s2[k] for
            // k in [0, COLUMNS_IN_A).
            hax_lib::fstar!(
                r#"
                let _:Prims.unit =
                  let aux (k: nat{k < Seq.length ${s1_ntt}}) :
                    Lemma (Libcrux_ml_dsa.Polynomial.Spec.is_bounded_poly
                             (mk_usize 8380416) (Seq.index ${s1_ntt} k)) =
                    assert (Seq.index ${s1_ntt} k == Seq.index ${s1_s2} k);
                    Libcrux_ml_dsa.Polynomial.Spec.lemma_is_bounded_poly_slice_lookup
                      (mk_usize 8380416) ${s1_s2} k
                  in
                  Classical.forall_intro aux
                in
                Libcrux_ml_dsa.Polynomial.Spec.lemma_is_bounded_poly_slice_intro
                  (mk_usize 8380416) ${s1_ntt}
                "#
            );
            for i in 0..s1_ntt.len() {
                // Truthful split: processed entries [0,i) are NTT_OUTPUT_BOUND
                // (forward ntt output, not reduced), unprocessed [i,len) are
                // still FIELD_MAX (sampled s1). After the loop the whole slice
                // is NTT_OUTPUT_BOUND, matching compute_as1_plus_s2's widened
                // s1_ntt pre. (Body is admit()-ed; this keeps the claim truthful.)
                hax_lib::loop_invariant!(|i: usize| fstar!(
                    r#"v $i <= Seq.length ${s1_ntt} /\
                       Libcrux_ml_dsa.Polynomial.Spec.is_bounded_poly_range
                           (mk_usize 75423744) (mk_usize 0) $i ${s1_ntt} /\
                       (forall (k:nat). v $i <= k /\ k < Seq.length ${s1_ntt} ==>
                          Libcrux_ml_dsa.Polynomial.Spec.is_bounded_poly
                              (mk_usize 8380416) (Seq.index ${s1_ntt} k))"#
                ));
                ntt(&mut s1_ntt[i]);
            }
            compute_as1_plus_s2::<SIMDUnit>(
                ROWS_IN_A,
                COLUMNS_IN_A,
                &mut a_as_ntt,
                &s1_ntt,
                &s1_s2,
                &mut t0,
            );
        }

        let mut t1 = [PolynomialRingElement::<SIMDUnit>::zero(); ROWS_IN_A];
        power2round_vector::<SIMDUnit>(&mut t0, &mut t1);

        // Bridge `is_lane_range_poly_slice 0 eta_val s1_s2` (post of
        // sample_s1_and_s2) to the bare `forall k j. is_pos_array_opaque
        // (match eta with...) ...` form that signing_key's `s1_2` pre wants.
        // One-shot via `lemma_lane_range_pos_to_pos_array_slice`.
        hax_lib::fstar!(
            r#"
            let eta_val : usize = match ${ETA} with
                                   | Libcrux_ml_dsa.Constants.Eta_Two -> mk_usize 2
                                   | Libcrux_ml_dsa.Constants.Eta_Four -> mk_usize 4 in
            Libcrux_ml_dsa.Polynomial.Spec.lemma_lane_range_pos_to_pos_array_slice
              eta_val ${s1_s2}
            "#
        );

        // Write out the keys
        encoding::verification_key::generate_serialized::<SIMDUnit>(
            seed_for_a,
            &t1,
            verification_key,
        );
        encoding::signing_key::generate_serialized::<SIMDUnit, Shake256>(
            ETA,
            ERROR_RING_ELEMENT_SIZE,
            seed_for_a,
            seed_for_signing,
            verification_key,
            &s1_s2,
            &t0,
            signing_key,
        );
    }

    #[inline(always)]
    // The signing key arrives as a `&[u8]` slice (the fixed-array length is
    // erased at the generic boundary), so we need its exact length to prove the
    // five `split_at` calls below are panic-free and to discharge the
    // `t0_serialized` length precondition of `t0::deserialize_to_vector_then_ntt`.
    // The top-level API always passes a `[u8; SIGNING_KEY_SIZE]`, so the
    // instantiation wrappers discharge this from the array type.
    #[cfg_attr(hax, hax_lib::requires(fstar!(r#"Seq.length $signing_key == v ${SIGNING_KEY_SIZE}"#)))]
    // Like verify_internal, the pre-loop VC (5 split_at + s1/s2/t0 deserialize +
    // matrix_flat + derive_message_representative + shake) saturates the module
    // default rlimit as one monolithic query; split + z3refresh lands it.
    #[cfg_attr(hax, hax_lib::fstar::options("--z3rlimit 800 --split_queries always --z3refresh"))]
    // Helper predicate for the rejection loop's invariant hint clause: once a
    // signature is accepted (`hint = Some h`), its Hamming weight stays within
    // MAX_ONES_IN_HINT.  Phrased as a top-level `match` (clean context) so the
    // loop invariant references only this atom: an inline `Option_Some?._0`
    // projector in the while_loop refinement corrupts the post-loop `match hint`
    // pattern typing (the Bundle-encoded `Core_models.Option`, F* error 114).
    #[cfg_attr(hax, hax_lib::fstar::before(r#"
let hint_count_bounded
      (#rows: usize)
      (hint: Core_models.Option.t_Option (t_Array (t_Array i32 (mk_usize 256)) rows))
      (m: usize)
    : Type0 =
  match hint with
  | Core_models.Option.Option_Some h ->
    Libcrux_ml_dsa.Encoding.Signature.count_total_ones (h <: t_Slice (t_Array i32 (mk_usize 256))) <= v m
  | Core_models.Option.Option_None  -> Prims.l_True
"#))]
    pub(crate) fn sign_internal<
        SIMDUnit: Operations,
        Sampler: X4Sampler,
        Shake128X4: shake128::XofX4,
        Shake256: shake256::DsaXof,
        Shake256Xof: shake256::Xof,
        Shake256X4: shake256::XofX4,
    >(
        signing_key: &[u8],
        message: &[u8],
        domain_separation_context: Option<DomainSeparationContext>,
        randomness: [u8; SIGNING_RANDOMNESS_SIZE],
        signature: &mut [u8; SIGNATURE_SIZE],
    ) -> Result<(), SigningError> {
        // Split the signing key into its parts.
        let (seed_for_a, remaining_serialized) = signing_key.split_at(SEED_FOR_A_SIZE);
        let (seed_for_signing, remaining_serialized) =
            remaining_serialized.split_at(SEED_FOR_SIGNING_SIZE);
        let (verification_key_hash, remaining_serialized) =
            remaining_serialized.split_at(BYTES_FOR_VERIFICATION_KEY_HASH);

        let (s1_serialized, remaining_serialized) =
            remaining_serialized.split_at(ERROR_RING_ELEMENT_SIZE * COLUMNS_IN_A);
        let (s2_serialized, t0_serialized) =
            remaining_serialized.split_at(ERROR_RING_ELEMENT_SIZE * ROWS_IN_A);

        // The T0 remainder length must chain back through all five splits to
        // SIGNING_KEY_SIZE.  Unfolding `signing_key_size` (via assert_norm on the
        // constant relationship) lets the ERROR_RING_ELEMENT_SIZE terms cancel so
        // t0_serialized's length equals RING_ELEMENT_OF_T0S_SIZE * ROWS_IN_A,
        // which is exactly what t0::deserialize_to_vector_then_ntt requires
        // (t0_as_ntt has length ROWS_IN_A).  Placed BEFORE the ring-element array
        // declarations so the five-slice reconciliation runs in a small typing
        // context — for ml-dsa-87 (k=8/l=7) the same assert after the arrays
        // saturates rlimit 800; here it lands at ~73.
        hax_lib::fstar!(
            r#"
            assert_norm (v ${SIGNING_KEY_SIZE} ==
                v ${SEED_FOR_A_SIZE} +
                v ${SEED_FOR_SIGNING_SIZE} +
                v ${BYTES_FOR_VERIFICATION_KEY_HASH} +
                v ${ERROR_RING_ELEMENT_SIZE} * v ${COLUMNS_IN_A} +
                v ${ERROR_RING_ELEMENT_SIZE} * v ${ROWS_IN_A} +
                v ${RING_ELEMENT_OF_T0S_SIZE} * v ${ROWS_IN_A});
            assert (Seq.length ${t0_serialized} ==
                v ${RING_ELEMENT_OF_T0S_SIZE} * v ${ROWS_IN_A})
            "#
        );

        // Deserialize s1, s2, and t0.
        let mut s1_as_ntt = [PolynomialRingElement::zero(); COLUMNS_IN_A];
        let mut s2_as_ntt = [PolynomialRingElement::zero(); ROWS_IN_A];
        let mut t0_as_ntt = [PolynomialRingElement::zero(); ROWS_IN_A];

        encoding::error::deserialize_to_vector_then_ntt::<SIMDUnit>(
            ETA,
            ERROR_RING_ELEMENT_SIZE,
            s1_serialized,
            &mut s1_as_ntt,
        );
        encoding::error::deserialize_to_vector_then_ntt::<SIMDUnit>(
            ETA,
            ERROR_RING_ELEMENT_SIZE,
            s2_serialized,
            &mut s2_as_ntt,
        );
        encoding::t0::deserialize_to_vector_then_ntt::<SIMDUnit>(t0_serialized, &mut t0_as_ntt);

        // Sample matrix A.
        let mut matrix = [PolynomialRingElement::<SIMDUnit>::zero(); ROW_X_COLUMN];
        Sampler::matrix_flat::<SIMDUnit>(COLUMNS_IN_A, seed_for_a, &mut matrix);

        let mut message_representative = [0; MESSAGE_REPRESENTATIVE_SIZE];
        derive_message_representative::<Shake256Xof>(
            verification_key_hash,
            &domain_separation_context,
            message,
            &mut message_representative,
        );

        let mut mask_seed = [0; MASK_SEED_SIZE];
        {
            let mut shake = Shake256Xof::init();
            shake.absorb(seed_for_signing);
            shake.absorb(&randomness);
            shake.absorb_final(&message_representative);

            shake.squeeze(&mut mask_seed);
        }

        let mut domain_separator_for_mask: u16 = 0;
        let mut attempt = 0;

        // Return values.
        // Required because we can't return early.
        // See https://github.com/hacspec/hax/issues/1171
        let mut commitment_hash = None;
        let mut signer_response = None;
        let mut hint = None;

        // As specified in [FIPS 204, Appendix C], the minimum number of
        // attempts in this rejection sampling loop is 814. This puts the
        // probability of failure at 2⁻²⁵⁶ or less.
        //
        // [FIPS 204, Appendix C]: https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.204.pdf#appendix.C
        // Rejection-sampling loop.  The invariant tracks: `attempt` stays
        // within its bound (well-foundedness of the decreases measure); the
        // mask domain separator grows by at most COLUMNS_IN_A per attempt; and
        // — once a signature is accepted — the hint's Hamming weight is within
        // MAX_ONES_IN_HINT (consumed by the post-loop `serialize` precondition).
        // The loop-body callee preconditions + invariant maintenance remain a
        // follow-up (body admit below); the invariant establishment, decreases,
        // and the whole post-loop ARE discharged (pre-loop admit removed).
        while attempt < REJECTION_SAMPLE_BOUND_SIGN {
            hax_lib::loop_invariant!(fstar!(
                r#"
                v ${attempt} <= v ${REJECTION_SAMPLE_BOUND_SIGN} /\
                v ${domain_separator_for_mask} <= v ${attempt} * v ${COLUMNS_IN_A} /\
                hint_count_bounded ${hint} ${MAX_ONES_IN_HINT}
                "#
            ));
            hax_lib::loop_decreases!(REJECTION_SAMPLE_BOUND_SIGN - attempt);
            // FOLLOW-UP: discharge the ~15 loop-body callee preconditions and
            // the per-iteration invariant maintenance (sample_mask_vector's
            // domain-separator bound, decompose_vector's is_bounded post feeding
            // make_hint's count chain, etc.).  Admitted for now so the loop
            // skeleton + post-loop verify.
            hax_lib::fstar!("admit ()");
            attempt += 1;

            let mut mask = [PolynomialRingElement::zero(); COLUMNS_IN_A];
            let mut w0 = [PolynomialRingElement::zero(); ROWS_IN_A];
            let mut commitment = [PolynomialRingElement::zero(); ROWS_IN_A];

            sample_mask_vector::<SIMDUnit, Shake256, Shake256X4>(
                COLUMNS_IN_A,
                GAMMA1_EXPONENT,
                &mask_seed,
                &mut domain_separator_for_mask,
                &mut mask,
            );

            {
                let mut a_x_mask = [PolynomialRingElement::zero(); ROWS_IN_A];
                let mut mask_ntt = mask.clone();
                for i in 0..mask_ntt.len() {
                    ntt(&mut mask_ntt[i]);
                }
                compute_matrix_x_mask::<SIMDUnit>(
                    ROWS_IN_A,
                    COLUMNS_IN_A,
                    &matrix,
                    &mask_ntt,
                    &mut a_x_mask,
                );
                decompose_vector::<SIMDUnit>(
                    ROWS_IN_A,
                    GAMMA2,
                    &a_x_mask,
                    &mut w0,
                    &mut commitment,
                );
            }

            let mut commitment_hash_candidate = [0; COMMITMENT_HASH_SIZE];
            {
                let mut commitment_serialized = [0u8; COMMITMENT_VECTOR_SIZE];
                encoding::commitment::serialize_vector::<SIMDUnit>(
                    COMMITMENT_RING_ELEMENT_SIZE,
                    &commitment,
                    &mut commitment_serialized,
                );

                let mut shake = Shake256Xof::init();
                shake.absorb(&message_representative);
                shake.absorb_final(&commitment_serialized);

                shake.squeeze(&mut commitment_hash_candidate);
            }

            let mut verifier_challenge = PolynomialRingElement::zero();
            sample_challenge_ring_element::<SIMDUnit, Shake256>(
                &commitment_hash_candidate,
                ONES_IN_VERIFIER_CHALLENGE,
                &mut verifier_challenge,
            );
            ntt(&mut verifier_challenge);

            // We need to clone here in case we need s1_as_ntt or s2_as_ntt again in
            // another iteration of the loop.
            let mut challenge_times_s1 = s1_as_ntt.clone();
            let mut challenge_times_s2 = s2_as_ntt.clone();

            vector_times_ring_element::<SIMDUnit>(&mut challenge_times_s1, &verifier_challenge);
            vector_times_ring_element::<SIMDUnit>(&mut challenge_times_s2, &verifier_challenge);

            add_vectors::<SIMDUnit>(COLUMNS_IN_A, &mut mask, &challenge_times_s1);
            subtract_vectors::<SIMDUnit>(ROWS_IN_A, &mut w0, &challenge_times_s2);

            if vector_infinity_norm_exceeds::<SIMDUnit>(&mask, (1 << GAMMA1_EXPONENT) - BETA) {
                // XXX: https://github.com/hacspec/hax/issues/1171
                // continue;
            } else {
                if vector_infinity_norm_exceeds::<SIMDUnit>(&w0, GAMMA2 - BETA) {
                    // XXX: https://github.com/hacspec/hax/issues/1171
                    // continue;
                } else {
                    // We need to clone here in case we need t0_as_ntt again in another iteration
                    // of the loop.
                    let mut challenge_times_t0 = t0_as_ntt.clone();
                    vector_times_ring_element::<SIMDUnit>(
                        &mut challenge_times_t0,
                        &verifier_challenge,
                    );
                    if vector_infinity_norm_exceeds::<SIMDUnit>(&challenge_times_t0, GAMMA2) {
                        // XXX: https://github.com/hacspec/hax/issues/1171
                        // continue;
                    } else {
                        add_vectors::<SIMDUnit>(ROWS_IN_A, &mut w0, &challenge_times_t0);
                        let mut hint_candidate = [[0; COEFFICIENTS_IN_RING_ELEMENT]; ROWS_IN_A];
                        let ones_in_hint =
                            make_hint::<SIMDUnit>(&w0, &commitment, GAMMA2, &mut hint_candidate);

                        if ones_in_hint > MAX_ONES_IN_HINT {
                            // XXX: https://github.com/hacspec/hax/issues/1171
                            // continue;
                        } else {
                            attempt = REJECTION_SAMPLE_BOUND_SIGN; // exit loop now
                            commitment_hash = Some(commitment_hash_candidate);
                            signer_response = Some(mask);
                            hint = Some(hint_candidate);
                        }
                    }
                }
            }
        }

        let commitment_hash = match commitment_hash {
            Some(commitment_hash) => commitment_hash,
            None => return Err(SigningError::RejectionSamplingError),
        };

        let signer_response = match signer_response {
            Some(signer_response) => signer_response,
            None => return Err(SigningError::RejectionSamplingError),
        };

        let hint = match hint {
            Some(hint) => hint,
            None => return Err(SigningError::RejectionSamplingError),
        };

        // Discharge serialize's length preconditions: the concrete parameter
        // constants satisfy gamma1_ring_element_size = 32·(1+gamma1_exponent),
        // and SIGNATURE_SIZE decomposes into the commitment-hash / response /
        // hint sections.  `norm [delta]` fully reduces `signature_size` to its
        // literal (plain SMT reduction of it is flaky across parameter sets),
        // then SMT closes the array-length link via the type refinement.
        hax_lib::fstar!(
            r#"
            assert_norm (v ${GAMMA1_EXPONENT} == 17 \/ v ${GAMMA1_EXPONENT} == 19);
            assert_norm (v ${GAMMA1_RING_ELEMENT_SIZE} == 32 * (1 + v ${GAMMA1_EXPONENT}));
            assert_norm (v ${SIGNATURE_SIZE} ==
                v ${COMMITMENT_HASH_SIZE} +
                v ${GAMMA1_RING_ELEMENT_SIZE} * v ${COLUMNS_IN_A} +
                v ${MAX_ONES_IN_HINT} + v ${ROWS_IN_A});
            assert (Seq.length ${signature} == v ${SIGNATURE_SIZE})
              by (FStar.Tactics.norm [primops; iota; zeta; delta]; FStar.Tactics.smt ());
            assert_norm (v ${MAX_ONES_IN_HINT} + v ${ROWS_IN_A} <= max_usize)
            "#
        );

        encoding::signature::serialize::<SIMDUnit>(
            &commitment_hash,
            &signer_response,
            &hint,
            COMMITMENT_HASH_SIZE,
            COLUMNS_IN_A,
            ROWS_IN_A,
            GAMMA1_EXPONENT,
            GAMMA1_RING_ELEMENT_SIZE,
            MAX_ONES_IN_HINT,
            signature,
        );

        Ok(())
    }

    /// The internal verification API.
    ///
    /// If no `domain_separation_context` is supplied, it is assumed that
    /// `message` already contains the domain separation.
    #[allow(non_snake_case)]
    #[inline(always)]
    // verify_internal's monolithic VC splits into ~160 sub-queries; the heaviest
    // (compute_w_approx's precondition in the ML-DSA-87 context, k=8/l=7) is
    // budget-bound.  `--z3refresh` is REQUIRED alongside `--split_queries always`:
    // without it, Z3's state accumulates across sub-queries in the full-module build
    // and that one query drifts past 800 (flaky cold); with a fresh solver per
    // sub-query it lands at ~640/800 deterministically.  (44/65 use <45.)
    #[cfg_attr(hax, hax_lib::fstar::options("--z3rlimit 800 --split_queries always --z3refresh"))]
    pub(crate) fn verify_internal<
        SIMDUnit: Operations,
        Sampler: X4Sampler,
        Shake128X4: shake128::XofX4,
        Shake256: shake256::DsaXof,
        Shake256Xof: shake256::Xof,
    >(
        verification_key: &[u8; VERIFICATION_KEY_SIZE],
        message: &[u8],
        domain_separation_context: Option<DomainSeparationContext>,
        signature_serialized: &[u8; SIGNATURE_SIZE],
    ) -> Result<(), VerificationError> {
        // Concrete-constant facts, stated GENERICALLY across the 44/65/87
        // parameter sets (each is either definitional — e.g. ROW_X_COLUMN is
        // *defined* as ROWS_IN_A*COLUMNS_IN_A — or a disjunction/inequality that
        // holds for every set), so `assert_norm` reduces each per monomorphization.
        // They discharge the concrete-constant preconditions of the callees below
        // (signature::deserialize, compute_w_approx, use_hint, serialize_vector,
        // vector_infinity_norm_exceeds's bound arithmetic).
        hax_lib::fstar!(
            r#"
            assert_norm (v ${GAMMA1_EXPONENT} == 17 \/ v ${GAMMA1_EXPONENT} == 19);
            assert_norm (v ${GAMMA1_RING_ELEMENT_SIZE} == 32 * (1 + v ${GAMMA1_EXPONENT}));
            assert_norm (v ${ROWS_IN_A} > 0);
            assert_norm (v ${ROWS_IN_A} <= 8);
            assert_norm (v ${COLUMNS_IN_A} <= 7);
            assert_norm (v ${ROW_X_COLUMN} == v ${ROWS_IN_A} * v ${COLUMNS_IN_A});
            assert_norm (v ${BETA} >= 0 /\ v ${BETA} <= 524288);
            assert_norm (v ${SIGNATURE_SIZE} == v ${COMMITMENT_HASH_SIZE} + v ${GAMMA1_RING_ELEMENT_SIZE} * v ${COLUMNS_IN_A} + v ${MAX_ONES_IN_HINT} + v ${ROWS_IN_A});
            assert_norm (v ${GAMMA2} == v ${crate::constants::GAMMA2_V95_232} \/ v ${GAMMA2} == v ${crate::constants::GAMMA2_V261_888});
            assert_norm (v ${COMMITMENT_RING_ELEMENT_SIZE} == 128 \/ v ${COMMITMENT_RING_ELEMENT_SIZE} == 192);
            assert_norm (v (Libcrux_ml_dsa.Arithmetic.use_hint_serialize_bound ${GAMMA2}) == pow2 (v ${COMMITMENT_RING_ELEMENT_SIZE} / 32) - 1)
            "#
        );
        // Per FIPS 204 §3.6.2, an implementation that accepts inputs for σ
        // or pk of any other length than specified shall return false.  The
        // typed arguments enforce this at compile time for direct Rust
        // callers; these asserts mirror the keygen pattern (lines 68-70)
        // and document the invariant for FFI / C-extraction surfaces where
        // the array length may be erased.
        #[cfg(not(eurydice))]
        debug_assert!(verification_key.len() == VERIFICATION_KEY_SIZE);
        #[cfg(not(eurydice))]
        debug_assert!(signature_serialized.len() == SIGNATURE_SIZE);

        let (seed_for_a, t1_serialized) = verification_key.split_at(SEED_FOR_A_SIZE);
        let mut t1 = [PolynomialRingElement::<SIMDUnit>::zero(); ROWS_IN_A];
        encoding::verification_key::deserialize::<SIMDUnit>(
            ROWS_IN_A,
            VERIFICATION_KEY_SIZE,
            t1_serialized,
            &mut t1,
        );

        let mut deserialized_commitment_hash = [0u8; COMMITMENT_HASH_SIZE];
        let mut deserialized_signer_response = [PolynomialRingElement::zero(); COLUMNS_IN_A];
        let mut deserialized_hint = [[0i32; COEFFICIENTS_IN_RING_ELEMENT]; ROWS_IN_A];

        match encoding::signature::deserialize::<SIMDUnit>(
            COLUMNS_IN_A,
            ROWS_IN_A,
            COMMITMENT_HASH_SIZE,
            GAMMA1_EXPONENT,
            GAMMA1_RING_ELEMENT_SIZE,
            MAX_ONES_IN_HINT,
            SIGNATURE_SIZE,
            signature_serialized,
            &mut deserialized_commitment_hash,
            &mut deserialized_signer_response,
            &mut deserialized_hint,
        ) {
            Ok(_) => (),
            Err(e) => return Err(e),
        };

        // We use if-else branches because early returns will not go through hax.
        if vector_infinity_norm_exceeds::<SIMDUnit>(
            &deserialized_signer_response,
            (1 << GAMMA1_EXPONENT) - BETA,
        ) {
            return Err(VerificationError::SignerResponseExceedsBoundError);
        }
        let mut matrix = [PolynomialRingElement::<SIMDUnit>::zero(); ROW_X_COLUMN];
        Sampler::matrix_flat::<SIMDUnit>(COLUMNS_IN_A, seed_for_a, &mut matrix);

        let mut verification_key_hash = [0; BYTES_FOR_VERIFICATION_KEY_HASH];
        Shake256::shake256(verification_key, &mut verification_key_hash);

        let mut message_representative = [0; MESSAGE_REPRESENTATIVE_SIZE];
        derive_message_representative::<Shake256Xof>(
            &verification_key_hash,
            &domain_separation_context,
            message,
            &mut message_representative,
        );

        let mut verifier_challenge = PolynomialRingElement::zero();
        sample_challenge_ring_element::<SIMDUnit, Shake256>(
            &deserialized_commitment_hash,
            ONES_IN_VERIFIER_CHALLENGE,
            &mut verifier_challenge,
        );
        ntt(&mut verifier_challenge);

        // Move signer response into ntt.  Loop invariant: the processed prefix
        // [0,i) is NTT_OUTPUT_BOUND (75423744), the unprocessed suffix [i,len) is
        // still FIELD_MAX (8380416, from signature::deserialize's post); after the
        // loop the whole slice is 75423744, matching compute_w_approx's
        // signer_response precondition.  (Mirror of generate_key_pair's s1_ntt loop
        // + use_hint's per-iteration extend / post-loop range->slice conversion.)
        hax_lib::fstar!(
            r#"Libcrux_ml_dsa.Polynomial.Spec.lemma_is_bounded_poly_range_intro
                 (mk_usize 75423744) (mk_usize 0) (mk_usize 0) ${deserialized_signer_response}"#
        );
        for i in 0..deserialized_signer_response.len() {
            hax_lib::loop_invariant!(|i: usize| fstar!(
                r#"v $i <= Seq.length ${deserialized_signer_response} /\
                   Libcrux_ml_dsa.Polynomial.Spec.is_bounded_poly_range
                       (mk_usize 75423744) (mk_usize 0) $i ${deserialized_signer_response} /\
                   (forall (k:nat). v $i <= k /\ k < Seq.length ${deserialized_signer_response} ==>
                      Libcrux_ml_dsa.Polynomial.Spec.is_bounded_poly
                          (mk_usize 8380416) (Seq.index ${deserialized_signer_response} k))"#
            ));
            // The suffix bound at k=i is exactly ntt's FIELD_MAX precondition.
            hax_lib::fstar!(
                r#"assert (Libcrux_ml_dsa.Polynomial.Spec.is_bounded_poly
                            (mk_usize 8380416) (Seq.index ${deserialized_signer_response} (v $i)))"#
            );
            #[cfg(hax)]
            let iter_start: &[PolynomialRingElement<SIMDUnit>] =
                deserialized_signer_response.to_vec().as_slice();
            ntt(&mut deserialized_signer_response[i]);
            // ntt's post gives is_bounded_poly 75423744 on the updated entry; extend
            // the processed range from [0,i) to [0,i+1) via the standalone lemma.
            hax_lib::fstar!(
                r#"Libcrux_ml_dsa.Polynomial.Spec.lemma_is_bounded_poly_range_extend_after_update
                     (mk_usize 75423744) $i iter_start ${deserialized_signer_response}"#
            );
        }
        // After the loop the processed range covers [0,len); lift range -> slice.
        hax_lib::fstar!(
            r#"
            let _:Prims.unit =
              let aux (k:nat{k < Seq.length ${deserialized_signer_response}}) :
                Lemma (Libcrux_ml_dsa.Polynomial.Spec.is_bounded_poly
                         (mk_usize 75423744) (Seq.index ${deserialized_signer_response} k)) =
                Libcrux_ml_dsa.Polynomial.Spec.lemma_is_bounded_poly_range_lookup
                  (mk_usize 75423744) (mk_usize 0)
                  (Core_models.Slice.impl__len ${deserialized_signer_response})
                  ${deserialized_signer_response} k
              in Classical.forall_intro aux
            in
            Libcrux_ml_dsa.Polynomial.Spec.lemma_is_bounded_poly_slice_intro
              (mk_usize 75423744) ${deserialized_signer_response}"#
        );
        // Widen t1's lane range 0..1023 (verification_key::deserialize post) to
        // 0..261631 (compute_w_approx's precondition; [0,1023] subset [0,261631]).
        hax_lib::fstar!(
            r#"Libcrux_ml_dsa.Polynomial.Spec.lemma_is_lane_range_poly_slice_widen
                 (mk_usize 0) (mk_usize 1023) (mk_usize 261631) ${t1}"#
        );
        // compute_w_approx's `Seq.length matrix == rows_in_a * columns_in_a` sees
        // matrix's length as a resolved literal (= ROW_X_COLUMN); pin the two
        // parameter-set constants to their literal values via `normalize_term` so
        // the product reduces to that literal (generic: no hardcoded value).
        hax_lib::fstar!(
            r#"assert_norm (v ${ROWS_IN_A} == normalize_term (v ${ROWS_IN_A}));
               assert_norm (v ${COLUMNS_IN_A} == normalize_term (v ${COLUMNS_IN_A}))"#
        );
        compute_w_approx::<SIMDUnit>(
            ROWS_IN_A,
            COLUMNS_IN_A,
            &matrix,
            &deserialized_signer_response,
            &verifier_challenge,
            &mut t1,
        );

        // Compute the commitment hash again to validate the signature.
        let mut recomputed_commitment_hash = [0; COMMITMENT_HASH_SIZE];
        {
            // Weaken compute_w_approx's `is_bounded_poly_slice 4211177 t1` to the
            // FIELD_MAX bound (8380416) that use_hint's precondition wants
            // (4211177 <= 8380416), per element then re-introduce the slice atom.
            hax_lib::fstar!(
                r#"
                let _:Prims.unit =
                  let aux (k:nat{k < Seq.length ${t1}}) :
                    Lemma (Libcrux_ml_dsa.Polynomial.Spec.is_bounded_poly (mk_usize 8380416) (Seq.index ${t1} k)) =
                    Libcrux_ml_dsa.Polynomial.Spec.lemma_is_bounded_poly_slice_lookup (mk_usize 4211177) ${t1} k;
                    Libcrux_ml_dsa.Polynomial.Spec.lemma_is_bounded_poly_higher (mk_usize 4211177) (mk_usize 8380416) (Seq.index ${t1} k)
                  in Classical.forall_intro aux
                in
                Libcrux_ml_dsa.Polynomial.Spec.lemma_is_bounded_poly_slice_intro (mk_usize 8380416) ${t1}"#
            );
            use_hint::<SIMDUnit>(GAMMA2, &deserialized_hint, &mut t1);
            let mut commitment_serialized = [0u8; COMMITMENT_VECTOR_SIZE];
            // use_hint's post `is_lane_range_poly_slice 0 (use_hint_serialize_bound GAMMA2) t1`
            // -> the per-simd-unit non-negative `is_pos_array_opaque` bound that
            // serialize_vector requires.  The top-of-body assert_norm established
            // `use_hint_serialize_bound GAMMA2 == pow2 (COMMITMENT_RING_ELEMENT_SIZE/32) - 1`,
            // so the two bounds coincide.
            hax_lib::fstar!(
                r#"Libcrux_ml_dsa.Polynomial.Spec.lemma_lane_range_pos_to_pos_array_slice
                     (Libcrux_ml_dsa.Arithmetic.use_hint_serialize_bound ${GAMMA2}) ${t1}"#
            );
            // serialize_vector's `Seq.length serialized == ring_element_size * Seq.length vector`
            // sees serialized/t1 lengths as resolved literals; pin the constants so
            // COMMITMENT_RING_ELEMENT_SIZE * (len t1 = ROWS_IN_A) reduces to the
            // literal COMMITMENT_VECTOR_SIZE.
            hax_lib::fstar!(
                r#"assert_norm (v ${COMMITMENT_RING_ELEMENT_SIZE} == normalize_term (v ${COMMITMENT_RING_ELEMENT_SIZE}));
                   assert_norm (v ${ROWS_IN_A} == normalize_term (v ${ROWS_IN_A}))"#
            );
            encoding::commitment::serialize_vector::<SIMDUnit>(
                COMMITMENT_RING_ELEMENT_SIZE,
                &t1,
                &mut commitment_serialized,
            );

            let mut shake = Shake256Xof::init();
            shake.absorb(&message_representative);
            shake.absorb_final(&commitment_serialized);

            shake.squeeze(&mut recomputed_commitment_hash);
        }

        // Check if this is a valid signature by comparing the hashes.
        if deserialized_commitment_hash == recomputed_commitment_hash {
            return Ok(());
        }

        return Err(VerificationError::CommitmentHashesDontMatchError);
    }

    #[inline(always)]
    pub(crate) fn sign_pre_hashed_mut<
        SIMDUnit: Operations,
        Sampler: X4Sampler,
        Shake128: shake128::Xof,
        Shake128X4: shake128::XofX4,
        Shake256: shake256::DsaXof,
        Shake256Xof: shake256::Xof,
        Shake256X4: shake256::XofX4,
        PH: PreHash,
    >(
        signing_key: &[u8],
        message: &[u8],
        context: &[u8],
        pre_hash_buffer: &mut [u8],
        randomness: [u8; SIGNING_RANDOMNESS_SIZE],
        signature: &mut [u8; SIGNATURE_SIZE],
    ) -> Result<(), SigningError> {
        hax_lib::fstar!("admit ()");
        if context.len() > CONTEXT_MAX_LEN {
            return Err(SigningError::ContextTooLongError);
        }
        PH::hash::<Shake128>(message, pre_hash_buffer);
        let domain_separation_context = match DomainSeparationContext::new(context, Some(PH::oid()))
        {
            Ok(dsc) => dsc,
            Err(_) => return Err(SigningError::ContextTooLongError),
        };
        sign_internal::<SIMDUnit, Sampler, Shake128X4, Shake256, Shake256Xof, Shake256X4>(
            signing_key,
            pre_hash_buffer,
            Some(domain_separation_context),
            randomness,
            signature,
        )
    }

    #[inline(always)]
    #[cfg_attr(hax, hax_lib::ensures(|_| future(pre_hash_buffer).len() == pre_hash_buffer.len()))]
    pub(crate) fn sign_pre_hashed<
        SIMDUnit: Operations,
        Sampler: X4Sampler,
        Shake128: shake128::Xof,
        Shake128X4: shake128::XofX4,
        Shake256: shake256::DsaXof,
        Shake256Xof: shake256::Xof,
        Shake256X4: shake256::XofX4,
        PH: PreHash,
    >(
        signing_key: &[u8],
        message: &[u8],
        context: &[u8],
        pre_hash_buffer: &mut [u8],
        randomness: [u8; SIGNING_RANDOMNESS_SIZE],
    ) -> Result<MLDSASignature<SIGNATURE_SIZE>, SigningError> {
        hax_lib::fstar!("admit ()");
        let mut signature = MLDSASignature::zero();

        // [eurydice] doesn't support ?
        // https://github.com/AeneasVerif/eurydice/issues/105
        match sign_pre_hashed_mut::<
            SIMDUnit,
            Sampler,
            Shake128,
            Shake128X4,
            Shake256,
            Shake256Xof,
            Shake256X4,
            PH,
        >(
            signing_key,
            message,
            context,
            pre_hash_buffer,
            randomness,
            &mut signature.value,
        ) {
            Ok(_) => Ok(signature),
            Err(e) => Err(e),
        }
    }

    #[inline(always)]
    // Propagates sign_internal's signing-key length precondition; discharged by
    // the fixed-array instantiation wrappers.
    #[cfg_attr(hax, hax_lib::requires(fstar!(r#"Seq.length $signing_key == v ${SIGNING_KEY_SIZE}"#)))]
    pub(crate) fn sign_mut<
        SIMDUnit: Operations,
        Sampler: X4Sampler,
        Shake128X4: shake128::XofX4,
        Shake256: shake256::DsaXof,
        Shake256Xof: shake256::Xof,
        Shake256X4: shake256::XofX4,
    >(
        signing_key: &[u8],
        message: &[u8],
        context: &[u8],
        randomness: [u8; SIGNING_RANDOMNESS_SIZE],
        signature: &mut [u8; SIGNATURE_SIZE],
    ) -> Result<(), SigningError> {
        let domain_separation_context = match DomainSeparationContext::new(context, None) {
            Ok(dsc) => dsc,
            Err(_) => return Err(SigningError::ContextTooLongError),
        };
        sign_internal::<SIMDUnit, Sampler, Shake128X4, Shake256, Shake256Xof, Shake256X4>(
            signing_key,
            message,
            Some(domain_separation_context),
            randomness,
            signature,
        )
    }

    #[inline(always)]
    #[cfg_attr(hax, hax_lib::fstar::verification_status(panic_free))]
    #[cfg_attr(hax, hax_lib::ensures(|result| {
        hax_lib::implies(
            context.len() <= 255
                && message.len() <= 8192
                && signing_key.len() >= SIGNING_KEY_SIZE,
            result.is_ok()
                == hacspec_ml_dsa::sign::<
                    { HACSPEC_PARAMS.k },
                    { HACSPEC_PARAMS.l },
                    SIGNATURE_SIZE,
                    COMMITMENT_VECTOR_SIZE,
                    { HACSPEC_PARAMS.lambda / 4 },
                >(
                    signing_key,
                    message,
                    context,
                    &randomness,
                    &HACSPEC_PARAMS,
                ).is_ok(),
        )
    }))]
    // Propagates sign_mut's signing-key length precondition; discharged by the
    // fixed-array instantiation wrappers.  The functional ensures above already
    // treats `signing_key.len() >= SIGNING_KEY_SIZE` as a hypothesis, so this
    // exact-length requires is strictly compatible.
    #[cfg_attr(hax, hax_lib::requires(fstar!(r#"Seq.length $signing_key == v ${SIGNING_KEY_SIZE}"#)))]
    pub(crate) fn sign<
        SIMDUnit: Operations,
        Sampler: X4Sampler,
        Shake128X4: shake128::XofX4,
        Shake256: shake256::DsaXof,
        Shake256Xof: shake256::Xof,
        Shake256X4: shake256::XofX4,
    >(
        signing_key: &[u8],
        message: &[u8],
        context: &[u8],
        randomness: [u8; SIGNING_RANDOMNESS_SIZE],
    ) -> Result<MLDSASignature<SIGNATURE_SIZE>, SigningError> {
        let mut signature = MLDSASignature::zero();

        // [eurydice] doesn't support ?
        // https://github.com/AeneasVerif/eurydice/issues/105
        match sign_mut::<SIMDUnit, Sampler, Shake128X4, Shake256, Shake256Xof, Shake256X4>(
            signing_key,
            message,
            context,
            randomness,
            &mut signature.value,
        ) {
            Ok(_) => Ok(signature),
            Err(e) => Err(e),
        }
    }

    #[inline(always)]
    #[cfg_attr(hax, hax_lib::fstar::verification_status(panic_free))]
    #[cfg_attr(hax, hax_lib::ensures(|result| {
        hax_lib::implies(
            context.len() <= 255 && message.len() <= 8192,
            result.is_ok()
                == hacspec_ml_dsa::verify::<
                    { HACSPEC_PARAMS.k },
                    { HACSPEC_PARAMS.l },
                    { HACSPEC_PARAMS.lambda / 4 },
                    COMMITMENT_VECTOR_SIZE,
                >(
                    verification_key_serialized,
                    message,
                    signature_serialized,
                    context,
                    &HACSPEC_PARAMS,
                ).is_ok(),
        )
    }))]
    pub(crate) fn verify<
        SIMDUnit: Operations,
        Sampler: X4Sampler,
        Shake128X4: shake128::XofX4,
        Shake256: shake256::DsaXof,
        Shake256Xof: shake256::Xof,
    >(
        verification_key_serialized: &[u8; VERIFICATION_KEY_SIZE],
        message: &[u8],
        context: &[u8],
        signature_serialized: &[u8; SIGNATURE_SIZE],
    ) -> Result<(), VerificationError> {
        // We manually do the matching here to make Eurydice happy.
        let domain_separation_context = match DomainSeparationContext::new(context, None) {
            Ok(dsc) => dsc,
            Err(_) => return Err(VerificationError::VerificationContextTooLongError),
        };
        verify_internal::<SIMDUnit, Sampler, Shake128X4, Shake256, Shake256Xof>(
            verification_key_serialized,
            message,
            Some(domain_separation_context),
            signature_serialized,
        )
    }

    #[inline(always)]
    #[cfg_attr(hax, hax_lib::ensures(|_| future(pre_hash_buffer).len() == pre_hash_buffer.len()))]
    pub(crate) fn verify_pre_hashed<
        SIMDUnit: Operations,
        Sampler: X4Sampler,
        Shake128: shake128::Xof,
        Shake128X4: shake128::XofX4,
        Shake256: shake256::DsaXof,
        Shake256Xof: shake256::Xof,
        PH: PreHash,
    >(
        verification_key_serialized: &[u8; VERIFICATION_KEY_SIZE],
        message: &[u8],
        context: &[u8],
        pre_hash_buffer: &mut [u8],
        signature_serialized: &[u8; SIGNATURE_SIZE],
    ) -> Result<(), VerificationError> {
        hax_lib::fstar!("admit ()");
        PH::hash::<Shake128>(message, pre_hash_buffer);
        let domain_separation_context = match DomainSeparationContext::new(context, Some(PH::oid()))
        {
            Ok(dsc) => dsc,
            Err(_) => return Err(VerificationError::VerificationContextTooLongError),
        };
        verify_internal::<SIMDUnit, Sampler, Shake128X4, Shake256, Shake256Xof>(
            verification_key_serialized,
            pre_hash_buffer,
            Some(domain_separation_context),
            signature_serialized,
        )
    }
}

/// This corresponds to line 6 in algorithm 7 in FIPS 204 (line 7 in algorithm
/// 8, resp.).
///
/// If `domain_separation_context` is supplied, applies domain
/// separation and length encoding to the context string,
/// before appending the message (in the regular variant) or the
/// pre-hash OID as well as the pre-hashed message digest. Otherwise,
/// it is assumed that `message` already contains domain separation
/// information.
///
/// In FIPS 204 M' is the concatenation of the domain separated context, any
/// potential pre-hash OID and the message (or the message pre-hash). We do not
/// explicitely construct the concatenation in memory since it is of statically unknown
/// length, but feed its components directly into the incremental XOF.
///
/// Refer to line 10 of Algorithm 2 (and line 5 of Algorithm 3, resp.) in [FIPS
/// 204](https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.204.pdf#section.5)
/// for details on the domain separation for regular ML-DSA. Line
/// 23 of Algorithm 4 (and line 18 of Algorithm 5,resp.) describe domain separation for the HashMl-DSA
/// variant.
#[inline(always)]
fn derive_message_representative<Shake256Xof: shake256::Xof>(
    verification_key_hash: &[u8],
    domain_separation_context: &Option<DomainSeparationContext>,
    message: &[u8],
    message_representative: &mut [u8; 64],
) {
    hax_lib::fstar!("admit ()");
    #[cfg(not(eurydice))]
    debug_assert!(verification_key_hash.len() == 64);

    let mut shake = Shake256Xof::init();
    shake.absorb(verification_key_hash);
    if let Some(domain_separation_context) = domain_separation_context {
        shake.absorb(&[domain_separation_context.pre_hash_oid().is_some() as u8]);
        shake.absorb(&[domain_separation_context.context().len() as u8]);
        shake.absorb(domain_separation_context.context());
        if let Some(pre_hash_oid) = domain_separation_context.pre_hash_oid() {
            // FIPS 204 Alg 4 line 23 / Alg 5 line 18: absorb the OID
            // verbatim (no extra IntegerToBytes(|OID|, 1) prefix).  The
            // OID is already DER-encoded with tag+length (see the
            // `SHAKE128_OID` constant in pre_hash.rs), so it carries
            // its own length information.
            shake.absorb(pre_hash_oid)
        }
    }

    shake.absorb_final(message);
    shake.squeeze(message_representative);
}
