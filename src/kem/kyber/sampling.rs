use super::{
    arithmetic::{FieldElement, PolynomialRingElement},
    constants::{COEFFICIENTS_IN_RING_ELEMENT, FIELD_MODULUS, REJECTION_SAMPLING_SEED_SIZE},
};
use crate::{cloop, hax_utils::hax_debug_assert};

fn rejection_sampling_panic_with_diagnostic() {
    panic!()
    //    We would instead prefer to do the following:
    //    panic!("5 blocks of SHAKE128 output were extracted from the seed for rejection sampling, but not all of them could be sampled.\nWe would appreciate it if you could report this error by opening an issue at https://github.com/cryspen/libcrux/issues");
}

/// If `bytes` contains a set of uniformly random bytes, this function
/// uniformly samples a ring element `â` that is treated as being the NTT representation
/// of the corresponding polynomial `a`.
///
/// Since rejection sampling is used, it is possible the supplied bytes are
/// not enough to sample the element, in which case an `Err` is returned and the
/// caller must try again with a fresh set of bytes.
///
/// This function <strong>partially</strong> implements <strong>Algorithm 6</strong> of the NIST FIPS 203 standard,
/// We say "partially" because this implementation only accepts a finite set of
/// bytes as input and returns an error if the set is not enough; Algorithm 6 of
/// the FIPS 203 standard on the other hand samples from an infinite stream of bytes
/// until the ring element is filled. Algorithm 6 is reproduced below:
///
/// ```plaintext
/// Input: byte stream B ∈ 𝔹*.
/// Output: array â ∈ ℤ₂₅₆.
///
/// i ← 0
/// j ← 0
/// while j < 256 do
///     d₁ ← B[i] + 256·(B[i+1] mod 16)
///     d₂ ← ⌊B[i+1]/16⌋ + 16·B[i+2]
///     if d₁ < q then
///         â[j] ← d₁
///         j ← j + 1
///     end if
///     if d₂ < q and j < 256 then
///         â[j] ← d₂
///         j ← j + 1
///     end if
///     i ← i + 3
/// end while
/// return â
/// ```
///
/// The NIST FIPS 203 standard can be found at
/// <https://csrc.nist.gov/pubs/fips/203/ipd>.
pub fn sample_from_uniform_distribution(
    randomness: [u8; REJECTION_SAMPLING_SEED_SIZE],
) -> PolynomialRingElement {
    let mut sampled_coefficients: usize = 0;
    let mut out: PolynomialRingElement = PolynomialRingElement::ZERO;

    // This loop is written the way it is since reasoning about early returns,
    // breaks, and continues is not well supported in Fstar at the moment. Rewriting
    // this code to use an early return is being tracked in:
    // https://github.com/cryspen/libcrux/issues/134
    let mut done = false;
    for bytes in randomness.chunks(3) {
        if !done {
            let b1 = bytes[0] as i32;
            let b2 = bytes[1] as i32;
            let b3 = bytes[2] as i32;

            let d1 = ((b2 & 0xF) << 8) | b1;
            let d2 = (b3 << 4) | (b2 >> 4);

            if d1 < FIELD_MODULUS && sampled_coefficients < COEFFICIENTS_IN_RING_ELEMENT {
                out.coefficients[sampled_coefficients] = d1;
                sampled_coefficients += 1
            }
            if d2 < FIELD_MODULUS && sampled_coefficients < COEFFICIENTS_IN_RING_ELEMENT {
                out.coefficients[sampled_coefficients] = d2;
                sampled_coefficients += 1;
            }
            if sampled_coefficients == COEFFICIENTS_IN_RING_ELEMENT {
                done = true;
            }
        }
    }

    if !done {
        // Requiring more than 5 blocks to sample a ring element should be very
        // unlikely according to:
        // https://eprint.iacr.org/2023/708.pdf
        rejection_sampling_panic_with_diagnostic();
    }

    hax_debug_assert!(out
        .coefficients
        .into_iter()
        .all(|coefficient| coefficient >= 0 && coefficient < FIELD_MODULUS));
    out
}

/// Given a series of uniformly random bytes in `randomness`, for some number `eta`,
/// the `sample_from_binomial_distribution_{eta}` functions sample
/// a ring element from a binomial distribution centered at 0 that uses two sets
/// of `eta` coin flips. If, for example,
/// `eta = ETA`, each ring coefficient is a value `v` such
/// such that `v ∈ {-ETA, -ETA + 1, ..., 0, ..., ETA + 1, ETA}` and:
///
/// ```plaintext
/// - If v < 0, Pr[v] = Pr[-v]
/// - If v >= 0, Pr[v] = BINOMIAL_COEFFICIENT(2 * ETA; ETA - v) / 2 ^ (2 * ETA)
/// ```
///
/// The values `v < 0` are mapped to the appropriate `KyberFieldElement`.
///
/// The expected value is:
///
/// ```plaintext
/// E[X] = (-ETA)Pr[-ETA] + (-(ETA - 1))Pr[-(ETA - 1)] + ... + (ETA - 1)Pr[ETA - 1] + (ETA)Pr[ETA]
///      = 0 since Pr[-v] = Pr[v] when v < 0.
/// ```
///
/// And the variance is:
///
/// ```plaintext
/// Var(X) = E[(X - E[X])^2]
///        = E[X^2]
///        = sum_(v=-ETA to ETA)v^2 * (BINOMIAL_COEFFICIENT(2 * ETA; ETA - v) / 2^(2 * ETA))
///        = ETA / 2
/// ```
///
/// This function implements <strong>Algorithm 7</strong> of the NIST FIPS 203 standard, which is
/// reproduced below:
///
/// ```plaintext
/// Input: byte array B ∈ 𝔹^{64η}.
/// Output: array f ∈ ℤ₂₅₆.
///
/// b ← BytesToBits(B)
/// for (i ← 0; i < 256; i++)
///     x ← ∑(j=0 to η - 1) b[2iη + j]
///     y ← ∑(j=0 to η - 1) b[2iη + η + j]
///     f[i] ← x−y mod q
/// end for
/// return f
/// ```
///
/// The NIST FIPS 203 standard can be found at
/// <https://csrc.nist.gov/pubs/fips/203/ipd>.

#[cfg_attr(hax, hax_lib_macros::requires(randomness.len() == 2 * 64))]
#[cfg_attr(hax, hax_lib_macros::ensures(|result|
    hax_lib::forall(|i:usize|
        hax_lib::implies(i < result.coefficients.len(), || result.coefficients[i].abs() <= 2
))))]
fn sample_from_binomial_distribution_2(randomness: &[u8]) -> PolynomialRingElement {
    let mut sampled: PolynomialRingElement = PolynomialRingElement::ZERO;

    cloop! {
        for (chunk_number, byte_chunk) in randomness.chunks_exact(4).enumerate() {
            let random_bits_as_u32: u32 = (byte_chunk[0] as u32)
                | (byte_chunk[1] as u32) << 8
                | (byte_chunk[2] as u32) << 16
                | (byte_chunk[3] as u32) << 24;

            let even_bits = random_bits_as_u32 & 0x55555555;
            let odd_bits = (random_bits_as_u32 >> 1) & 0x55555555;

            let coin_toss_outcomes = even_bits + odd_bits;

            cloop! {
                for outcome_set in (0..u32::BITS).step_by(4) {
                    let outcome_1 = ((coin_toss_outcomes >> outcome_set) & 0x3) as FieldElement;
                    let outcome_2 = ((coin_toss_outcomes >> (outcome_set + 2)) & 0x3) as FieldElement;

                    let offset = (outcome_set >> 2) as usize;
                    sampled.coefficients[8 * chunk_number + offset] = outcome_1 - outcome_2;
                }
            }
        }
    }

    hax_debug_assert!(sampled
        .coefficients
        .into_iter()
        .all(|coefficient| coefficient >= -2 && coefficient <= 2));
    sampled
}

#[cfg_attr(hax, hax_lib_macros::requires(randomness.len() == 3 * 64))]
#[cfg_attr(hax, hax_lib_macros::ensures(|result|
    hax_lib::forall(|i:usize|
        hax_lib::implies(i < result.coefficients.len(), || result.coefficients[i].abs() <= 3
))))]
fn sample_from_binomial_distribution_3(randomness: &[u8]) -> PolynomialRingElement {
    let mut sampled: PolynomialRingElement = PolynomialRingElement::ZERO;

    cloop! {
        for (chunk_number, byte_chunk) in randomness.chunks_exact(3).enumerate() {
            let random_bits_as_u24: u32 =
                (byte_chunk[0] as u32) | (byte_chunk[1] as u32) << 8 | (byte_chunk[2] as u32) << 16;

            let first_bits = random_bits_as_u24 & 0x00249249;
            let second_bits = (random_bits_as_u24 >> 1) & 0x00249249;
            let third_bits = (random_bits_as_u24 >> 2) & 0x00249249;

            let coin_toss_outcomes = first_bits + second_bits + third_bits;

            cloop! {
                for outcome_set in (0..24).step_by(6) {
                    let outcome_1 = ((coin_toss_outcomes >> outcome_set) & 0x7) as FieldElement;
                    let outcome_2 = ((coin_toss_outcomes >> (outcome_set + 3)) & 0x7) as FieldElement;

                    let offset = (outcome_set / 6) as usize;
                    sampled.coefficients[4 * chunk_number + offset] = outcome_1 - outcome_2;
                }
            }
        }
    }

    hax_debug_assert!(sampled
        .coefficients
        .into_iter()
        .all(|coefficient| coefficient >= -3 && coefficient <= 3));
    sampled
}

#[inline(always)]
pub(super) fn sample_from_binomial_distribution<const ETA: usize>(
    randomness: &[u8],
) -> PolynomialRingElement {
    hax_debug_assert!(randomness.len() == ETA * 64);

    match ETA as u32 {
        2 => sample_from_binomial_distribution_2(randomness),
        3 => sample_from_binomial_distribution_3(randomness),
        _ => unreachable!(),
    }
}
