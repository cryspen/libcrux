use crate::kem::kyber768::{
    parameters::{self, KyberPolynomialRingElement},
    BadRejectionSamplingRandomnessError,
};
use crate::kem::kyber768::field_element::KyberFieldElement;

pub fn sample_from_uniform_distribution(
    randomness: [u8; parameters::REJECTION_SAMPLING_SEED_SIZE],
) -> Result<KyberPolynomialRingElement, BadRejectionSamplingRandomnessError> {
    let mut sampled_coefficients: usize = 0;
    let mut out: KyberPolynomialRingElement = KyberPolynomialRingElement::ZERO;

    for bytes in randomness.chunks(3) {
        let b = u16::from(bytes[0]);
        let b1 = u16::from(bytes[1]);
        let b2 = u16::from(bytes[2]);

        let d1 = b + (256 * (b1 % 16));

        // Integer division is flooring in Rust.
        let d2 = (b1 / 16) + (16 * b2);

        if d1 < parameters::FIELD_MODULUS && sampled_coefficients < out.len() {
            out[sampled_coefficients] = KyberFieldElement { value : d1 };
            sampled_coefficients += 1
        }
        if d2 < parameters::FIELD_MODULUS && sampled_coefficients < out.len() {
            out[sampled_coefficients] = KyberFieldElement { value : d2 };
            sampled_coefficients += 1;
        }

        if sampled_coefficients == out.len() {
            return Ok(out);
        }
    }

    Err(BadRejectionSamplingRandomnessError)
}

pub fn sample_from_binomial_distribution_with_2_coins(
    randomness: [u8; 128],
) -> KyberPolynomialRingElement {
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
            let outcome_1: u8 = ((coin_toss_outcomes >> outcome_set) & 0x3) as u8;
            let outcome_1: KyberFieldElement = outcome_1.into();

            let outcome_2: u8 = ((coin_toss_outcomes >> (outcome_set + 2)) & 0x3) as u8;
            let outcome_2: KyberFieldElement = outcome_2.into();

            let offset = (outcome_set >> 2) as usize;
            sampled[8 * chunk_number + offset] = outcome_1 - outcome_2;
        }
    }

    sampled
}
