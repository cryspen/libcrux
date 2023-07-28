use crate::helpers::bit_vector::BitVector;
use crate::parameters::{self, KyberFieldElement, KyberPolynomialRingElement};
use crate::BadRejectionSamplingRandomnessError;

impl KyberPolynomialRingElement {
    ///
    /// Given a series of uniformly random bytes in `|randomness|`, sample uniformly
    /// at random a ring element rˆ, which is treated as being the NTT representation
    /// of a corresponding polynomial r.
    ///
    /// This implementation uses rejection sampling; it is therefore possible the
    /// supplied randomness is not enough to sample the element, in which case
    /// an Err is returned and the caller must try again with fresh randomness.
    ///
    /// This function implements Algorithm 1 of the Kyber Round 3 specification,
    /// which is reproduced below:
    ///
    /// ```plaintext
    /// Input: Byte stream B = b_0, b_1, b_2 ... ∈ B^{*}
    /// Output: NTT-representation aˆ ∈ R_q of a ∈ R_q
    /// i := 0
    /// j := 0
    /// while j < n do
    ///     d_1 := b_i + 256·(b_{i+1} mod^{+}16)
    ///     d_2 := ⌊b_{i+1}/16⌋ + 16·b_{i+2}
    ///     if d_1 < q then
    ///         aˆ_{j} := d_1
    ///         j := j + 1
    ///     end if
    ///     if d_2 < q and j < n then
    ///         aˆ_{j} := d_2
    ///         j := j + 1
    ///     end if
    ///     i := i + 3
    /// end while
    /// return aˆ0 + aˆ1X + · · · + aˆ{n−1}X^{n−1}
    /// ```
    ///
    /// The Kyber Round 3 specification can be found at:
    /// https://pq-crystals.org/kyber/data/kyber-specification-round3-20210131.pdf
    ///
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

            if d1 < parameters::FIELD_MODULUS && sampled_coefficients < out.coefficients.len() {
                out.coefficients[sampled_coefficients] = d1.into();
                sampled_coefficients += 1
            }
            if d2 < parameters::FIELD_MODULUS && sampled_coefficients < out.coefficients.len() {
                out.coefficients[sampled_coefficients] = d2.into();
                sampled_coefficients += 1;
            }

            if sampled_coefficients == out.coefficients.len() {
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
    /// - If v < 0, Pr[v] = Pr[-v]
    /// - If v >= 0, Pr[v] = BINOMIAL_COEFFICIENT(2 * ETA; ETA - v) / 2 ^ (2 * ETA)
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
    /// This function implements Algorithm 2 of the Kyber Round 3 specification,
    /// which is reproduced below:
    ///
    /// ```plaintext
    /// Input: Byte array B = (b_0, b_1, . . . , b_{64η−1}) ∈ B^{64η}
    /// Output: Polynomial f ∈ R_q
    /// (β_0, . . . , β_{512η−1}) := BytesToBits(B)
    /// for i from 0 to 255 do
    ///     a := sum(j = 0 to η−1)(β_{2iη+j})
    ///     b := sum(j = 0 to η−1)(β_{2iη+η+j})
    ///     fi := a − b
    /// end for
    /// return f_0 +f_1X +f_2X^2 +···+f_255X^255
    /// ```
    ///
    /// The Kyber Round 3 specification can be found at:
    /// https://pq-crystals.org/kyber/data/kyber-specification-round3-20210131.pdf
    ///
    /// TODO: This requires a different parameter ETA = 3 only when Kyber-512 is
    /// used; generalize it.
    pub fn sample_from_binomial_distribution(
        sampling_coins: usize,
        randomness: &[u8],
    ) -> KyberPolynomialRingElement {
        assert_eq!(randomness.len(), sampling_coins * 64);

        let randomness_bytes = randomness.to_vec();
        let mut random_bytes = randomness_bytes.chunks(sampling_coins);
        let random_bits: BitVector = randomness.into();
        let mut random_bits = random_bits.chunks(sampling_coins);

        let mut sampled: KyberPolynomialRingElement = KyberPolynomialRingElement::ZERO;

        for i in 0..sampled.coefficients.len() {
            let mut coin_tosses: u8 = 0;
            for bit in random_bits
                .next()
                .expect("the assertion ensures there are enough sampling coins")
            {
                // assert_eq!(randomness_bytes.bit(7), bit);
                coin_tosses += bit;
            }
            let coin_tosses_a: KyberFieldElement = coin_tosses.into();

            coin_tosses = 0;
            for bit in random_bits
                .next()
                .expect("the assertion ensures there are enough sampling coins")
            {
                coin_tosses += bit;
            }
            let coin_tosses_b: KyberFieldElement = coin_tosses.into();

            sampled.coefficients[i] = coin_tosses_a - coin_tosses_b;
        }

        sampled
    }
}

#[cfg(test)]
mod tests {
    use proptest::collection::vec;
    use proptest::prelude::*;

    use super::*;

    fn field_coefficient_to_binomial_sample(sampling_coins: usize, coefficient: u16) -> f64 {
        if sampling_coins == 2 {
            match coefficient {
                3327 => -2.0,
                3328 => -1.0,
                0 => 0.0,
                1 => 1.0,
                2 => 2.0,
                other => panic!(
                    "{} should not be a coefficient when ETA = {}.",
                    other, sampling_coins
                ),
            }
        } else if sampling_coins == 3 {
            match coefficient {
                3326 => -3.0,
                3327 => -2.0,
                3328 => -1.0,
                0 => 0.0,
                1 => 1.0,
                2 => 2.0,
                3 => 3.0,
                other => panic!(
                    "{} should not be a coefficient when ETA = {}.",
                    other, sampling_coins
                ),
            }
        } else {
            panic!("ETA is neither 2 nor 3.");
        }
    }

    fn percentage_error(actual: f64, expected: f64) -> f64 {
        ((actual - expected).abs() / expected.abs()) * 100.0
    }

    const REJECTION_SAMPLING_ATTEMPTS: usize = 3;

    #[test]
    fn uniform_sample_from_all_zeros() {
        let r = KyberPolynomialRingElement::sample_from_uniform_distribution(
            [0; parameters::REJECTION_SAMPLING_SEED_SIZE],
        )
        .unwrap();

        for coefficient in r.coefficients.iter() {
            assert_eq!(coefficient.value, 0);
        }
    }

    #[test]
    #[should_panic]
    fn uniform_sample_from_all_u8_max() {
        let _ = KyberPolynomialRingElement::sample_from_uniform_distribution(
            [u8::MAX; parameters::REJECTION_SAMPLING_SEED_SIZE],
        )
        .unwrap();
    }

    proptest! {
        #[test]
        fn uniform_sampler_mean_and_variance(randomness in vec(any::<u8>(), REJECTION_SAMPLING_ATTEMPTS * parameters::REJECTION_SAMPLING_SEED_SIZE)) {
            let mut sampled_ring_element = KyberPolynomialRingElement::ZERO;

            let mut sampling_attempts = (0..REJECTION_SAMPLING_ATTEMPTS).peekable();
            while let Some(attempt) = sampling_attempts.next() {
                let sampled = KyberPolynomialRingElement::sample_from_uniform_distribution(randomness[attempt*parameters::REJECTION_SAMPLING_SEED_SIZE..(attempt+1)*parameters::REJECTION_SAMPLING_SEED_SIZE].try_into().unwrap());

                if sampled.is_ok() {
                    sampled_ring_element = sampled.unwrap();
                    break;
                } else if sampling_attempts.peek().is_none() {
                    panic!("Unable to uniformly sample a ring element with the given randomness.");
                }
            }

            // Mean = (a + b) / 2 = (0 + 3328) / 2
            let expected_mean : f64 = 1664.0;

            // Variance = (n^2 - 1) / 12 where:
            // n = b - a + 1 = 3328 - 0 + 1 = 3329
            let expected_variance : f64 = 923_520.0;

            let mut mean : f64 = 0.0;
            let mut variance : f64 = 0.0;

            for coefficient in sampled_ring_element.coefficients {
                mean += f64::from(coefficient.value);
            }
            mean /= sampled_ring_element.coefficients.len() as f64;

            for coefficient in sampled_ring_element.coefficients {
                let coefficient_value : f64 = coefficient.value.try_into().unwrap();
                variance += (coefficient_value - mean) * (coefficient_value - mean);
            }
            variance /= (sampled_ring_element.coefficients.len() - 1) as f64;

            // We use looser tolerances as compared to in the binomial
            // sampling test since we're not sampling as many elements here
            // (we can never be sure what randomness we have will allow for
            // a ring element to be sampled uniformly).
            assert!(percentage_error(mean, expected_mean) < 25.0, "The variance is {}.", variance);
            assert!(percentage_error(variance, expected_variance) < 25.0, "The variance is {}.", variance);
        }

        #[test]
        fn binomial_sampler_mean_and_variance(
            randomness in vec(any::<u8>(), 2 * 2 * 64)
            )
            {
            // TODO: Generalize sampling coins to be in {2, 3}
            let sampling_coins : usize = 2;
            let expected_variance : f64 = (sampling_coins as f64) / 2.0;

            let mut mean : f64 = 0.0;
            let mut variance : f64 = 0.0;

            let ring_element_1 = KyberPolynomialRingElement::sample_from_binomial_distribution(sampling_coins, &randomness[0..sampling_coins * 64]);
            let ring_element_2 = KyberPolynomialRingElement::sample_from_binomial_distribution(sampling_coins, &randomness[sampling_coins * 64..]);

            let all_coefficients = ring_element_1.coefficients
                                   .into_iter()
                                   .chain(ring_element_2.coefficients.into_iter())
                                   .collect::<Vec<KyberFieldElement>>();

            for coefficient in &all_coefficients {
                mean += field_coefficient_to_binomial_sample(sampling_coins, coefficient.value);
            }
            mean /= all_coefficients.len() as f64;

            for coefficient in &all_coefficients {
                let binomial_sample = field_coefficient_to_binomial_sample(sampling_coins, coefficient.value);
                variance += (binomial_sample - mean) * (binomial_sample - mean);
            }
            variance /= (all_coefficients.len() - 1) as f64;

            assert!(mean < 0.3, "The mean is {}.", mean); // The expected mean is 0
            assert!(percentage_error(variance, expected_variance) < 25.0, "The variance is {}.", variance);
        }
    }
}
