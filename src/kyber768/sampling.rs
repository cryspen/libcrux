use crate::kyber768::{
    parameters::{self, KyberFieldElement, KyberPolynomialRingElement},
    BadRejectionSamplingRandomnessError,
    utils::bit_vector::LittleEndianBitStream
};

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
            out[sampled_coefficients] = d1.into();
            sampled_coefficients += 1
        }
        if d2 < parameters::FIELD_MODULUS && sampled_coefficients < out.len() {
            out[sampled_coefficients] = d2.into();
            sampled_coefficients += 1;
        }

        if sampled_coefficients == out.len() {
            return Ok(out);
        }
    }

    Err(BadRejectionSamplingRandomnessError)
}

pub fn sample_from_binomial_distribution(
    sampling_coins: usize,
    randomness: &[u8],
) -> KyberPolynomialRingElement {
    assert_eq!(randomness.len(), sampling_coins * 64);

    let mut sampled: KyberPolynomialRingElement = KyberPolynomialRingElement::ZERO;

    for i in 0..sampled.len() {
        let mut coin_tosses: u8 = 0;
        for j in 0..sampling_coins
        {
            coin_tosses += randomness.nth_bit(i * sampling_coins + j);

        }
        let coin_tosses_a: KyberFieldElement = coin_tosses.into();

        coin_tosses = 0;
        for j in 0..sampling_coins
        {
            coin_tosses += randomness.nth_bit((i + 1) * sampling_coins + j);

        }
        let coin_tosses_b: KyberFieldElement = coin_tosses.into();

        sampled[i] = coin_tosses_a - coin_tosses_b;
    }

    sampled
}
