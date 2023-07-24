use crate::parameters;
use crate::BadRejectionSamplingRandomnessError;

use crate::parameters::KyberFieldElement;
use crate::parameters::KyberPolynomialRingElement;

use crate::helpers::bit_vector::BitVector;

impl KyberPolynomialRingElement {
    pub fn sample_from_uniform_distribution(
        randomness: [u8; parameters::REJECTION_SAMPLING_SEED_SIZE],
    ) -> Result<KyberPolynomialRingElement, BadRejectionSamplingRandomnessError> {
        let mut j: usize = 0;
        let mut sampled: KyberPolynomialRingElement = KyberPolynomialRingElement::ZERO;

        for bytes in randomness.chunks(3) {
            let b = u16::from(bytes[0]);
            let b1 = u16::from(bytes[1]);
            let b2 = u16::from(bytes[2]);

            let d1 = b + (256 * (b1 % 16));

            // Integer division is flooring in Rust.
            let d2 = (b1 / 16) + (16 * b2);

            if d1 < parameters::FIELD_MODULUS && j < sampled.coefficients.len() {
                sampled.coefficients[j] = d1.into();
                j += 1
            }
            if d2 < parameters::FIELD_MODULUS && j < sampled.coefficients.len() {
                sampled.coefficients[j] = d2.into();
                j += 1;
            }
            // In an efficient implementation, we'd break when
            // j == sampled.coefficients.len, but we've forgone this to make
            // the implementation easier to read.
        }

        if j == sampled.coefficients.len() {
            Ok(sampled)
        } else {
            Err(BadRejectionSamplingRandomnessError)
        }
    }

    pub fn sample_from_binomial_distribution(
        sampling_coins: usize,
        randomness: &[u8],
    ) -> KyberPolynomialRingElement {
        let random_bits: BitVector = randomness.into();
        let mut random_bits = random_bits.chunks(sampling_coins);

        let mut sampled: KyberPolynomialRingElement = KyberPolynomialRingElement::ZERO;

        for i in 0..sampled.coefficients.len() {
            let mut coin_tosses: u8 = 0;
            for bit in random_bits.next().unwrap() {
                coin_tosses += bit;
            }
            let coin_tosses_a: KyberFieldElement = coin_tosses.into();

            coin_tosses = 0;
            for bit in random_bits.next().unwrap() {
                coin_tosses += bit;
            }
            let coin_tosses_b: KyberFieldElement = coin_tosses.into();

            sampled.coefficients[i] = coin_tosses_a - coin_tosses_b;
        }

        sampled
    }
}
