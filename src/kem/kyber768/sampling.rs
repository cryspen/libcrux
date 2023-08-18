use crate::kem::kyber768::{
    arithmetic::{fe_sub, KyberPolynomialRingElement},
    parameters::{COEFFICIENTS_IN_RING_ELEMENT, FIELD_MODULUS, REJECTION_SAMPLING_SEED_SIZE},
    BadRejectionSamplingRandomnessError,
};

pub fn sample_from_uniform_distribution(
    randomness: [u8; REJECTION_SAMPLING_SEED_SIZE],
) -> Result<KyberPolynomialRingElement, BadRejectionSamplingRandomnessError> {
    let mut sampled_coefficients: usize = 0;
    let mut out: KyberPolynomialRingElement = KyberPolynomialRingElement::ZERO;

    for bytes in randomness.chunks(3) {
        let b = i16::from(bytes[0]);
        let b1 = i16::from(bytes[1]);
        let b2 = i16::from(bytes[2]);

        let d1 = b + (256 * (b1 % 16));

        // Integer division is flooring in Rust.
        let d2 = (b1 / 16) + (16 * b2);

        if d1 < FIELD_MODULUS && sampled_coefficients < COEFFICIENTS_IN_RING_ELEMENT {
            out[sampled_coefficients] = d1 as i16;
            sampled_coefficients += 1
        }
        if d2 < FIELD_MODULUS && sampled_coefficients < COEFFICIENTS_IN_RING_ELEMENT {
            out[sampled_coefficients] = d2 as i16;
            sampled_coefficients += 1;
        }

        if sampled_coefficients == COEFFICIENTS_IN_RING_ELEMENT {
            return Ok(out);
        }
    }

    Err(BadRejectionSamplingRandomnessError)
}

/// Given a series of uniformly random bytes in `|randomness|`, sample
/// a ring element from a binomial distribution centered at 0 that uses two sets
/// of `|sampling_coins|` coin flips. If, for example,
/// `|sampling_coins| = ETA`, each ring coefficient is a value `v` such
/// such that `v ∈ {-ETA, -ETA + 1, ..., 0, ..., ETA + 1, ETA}` and:
///
/// - If v < 0, Pr\[v\] = Pr[-v]
/// - If v >= 0, Pr\[v\] = BINOMIAL_COEFFICIENT(2 * ETA; ETA - v) / 2 ^ (2 * ETA)
///
/// The values v < 0 are mapped to the appropriate
/// `|parameters::KyberFieldElement|`.
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
/// This function implements Algorithm 2 of the Kyber Round 3 specification with
/// ETA set to 2.
///
/// The Kyber Round 3 specification can be found at:
/// <https://pq-crystals.org/kyber/data/kyber-specification-round3-20210131.pdf>
pub fn sample_from_binomial_distribution_2(randomness: [u8; 128]) -> KyberPolynomialRingElement {
    let mut sampled: KyberPolynomialRingElement = KyberPolynomialRingElement::ZERO;

    for (chunk_number, byte_chunk) in randomness.chunks_exact(4).enumerate() {
        let random_bits_as_u32: u32 = (byte_chunk[0] as u32)
            | (byte_chunk[1] as u32) << 8
            | (byte_chunk[2] as u32) << 16
            | (byte_chunk[3] as u32) << 24;

        let even_bits = random_bits_as_u32 & 0x55555555;
        let odd_bits = (random_bits_as_u32 >> 1) & 0x55555555;

        let coin_toss_outcomes = even_bits + odd_bits;

        for outcome_set in (0..u32::BITS).step_by(4) {
            let outcome_1 = ((coin_toss_outcomes >> outcome_set) & 0x3) as i16;
            let outcome_2 = ((coin_toss_outcomes >> (outcome_set + 2)) & 0x3) as i16;

            let offset = (outcome_set >> 2) as usize;
            sampled[8 * chunk_number + offset] = fe_sub(outcome_1, outcome_2);
        }
    }

    sampled
}
