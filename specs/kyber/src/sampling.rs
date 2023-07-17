use crate::bit_vector::bytes_to_bit_vector;
use crate::field::FieldElement;
use crate::parameters;
use crate::ring::RingElement;
use crate::BadRejectionSamplingRandomnessError;

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
pub(crate) fn sample_ring_element_uniform(
    randomness: [u8; parameters::REJECTION_SAMPLING_SEED_SIZE],
) -> Result<RingElement, BadRejectionSamplingRandomnessError> {
    let mut j: usize = 0;
    let mut sampled: RingElement = RingElement::ZERO;

    for i in (0..randomness.len()).step_by(3) {
        let byte = u16::from(randomness[i]);
        let byte1 = u16::from(randomness[i + 1]);
        let byte2 = u16::from(randomness[i + 2]);

        let d1 = byte + (256 * (byte1 % 16));

        // Integer division is flooring in Rust.
        let d2 = (byte1 / 16) + (16 * byte2);

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

///
/// Given a series of uniformly random bytes in `|randomness|`, sample
/// a ring element from a binomial distribution centered at 0 that uses two sets
/// of `|BINOMIAL_SAMPLING_COINS|` coin flips. If, for example,
/// `|BINOMIAL_SAMPLING_COINS| = ETA`, each ring coefficient is a value `v` such
/// such that `v ∈ {-ETA, -ETA + 1, ..., 0, ..., ETA + 1, ETA}` and:
///
/// - If v < 0, Pr[v] = Pr[-v]
/// - If v >= 0, Pr[v] = BINOMIAL_COEFFICIENT(2 * ETA; ETA - v) / 2 ^ (2 * ETA)
///
/// The values v < 0 are mapped to the appropriate representative in
/// [0, `|parameters::MODULUS|`).
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
pub(crate) fn sample_ring_element_binomial(
    randomness: [u8; parameters::BINOMIAL_SAMPLING_COINS * 64],
) -> RingElement {
    let random_bits = bytes_to_bit_vector(&randomness[..]);
    assert_eq!(
        random_bits.len(),
        parameters::BINOMIAL_SAMPLING_COINS * 64 * (u8::BITS as usize)
    );

    let mut sampled: RingElement = RingElement::ZERO;

    for i in 0..sampled.coefficients.len() {
        let mut coin_tosses: u8 = 0;
        for j in 0..parameters::BINOMIAL_SAMPLING_COINS {
            coin_tosses += random_bits[(2 * i) * parameters::BINOMIAL_SAMPLING_COINS + j];
        }
        let coin_tosses_a: FieldElement = coin_tosses.into();

        coin_tosses = 0;
        for j in 0..parameters::BINOMIAL_SAMPLING_COINS {
            coin_tosses += random_bits[(2 * i + 1) * parameters::BINOMIAL_SAMPLING_COINS + j];
        }
        let coin_tosses_b: FieldElement = coin_tosses.into();

        sampled.coefficients[i] = coin_tosses_a - coin_tosses_b;
    }

    sampled
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
        let r = sample_ring_element_uniform([0; parameters::REJECTION_SAMPLING_SEED_SIZE]).unwrap();

        for coefficient in r.coefficients.iter() {
            assert_eq!(coefficient.value, 0);
        }
    }

    #[test]
    #[should_panic]
    fn uniform_sample_from_all_u8_max() {
        let _ = sample_ring_element_uniform([u8::MAX; parameters::REJECTION_SAMPLING_SEED_SIZE])
            .unwrap();
    }

    proptest! {

        #[test]
        fn test_uniform_sampler_mean_and_variance(randomness in vec(any::<u8>(), REJECTION_SAMPLING_ATTEMPTS * parameters::REJECTION_SAMPLING_SEED_SIZE)) {
            let mut sampled_ring_element = RingElement::ZERO;

            let mut sampling_attempts = (0..REJECTION_SAMPLING_ATTEMPTS).peekable();
            while let Some(attempt) = sampling_attempts.next() {
                let sampled = sample_ring_element_uniform(randomness[attempt*parameters::REJECTION_SAMPLING_SEED_SIZE..(attempt+1)*parameters::REJECTION_SAMPLING_SEED_SIZE].try_into().unwrap());

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

            // We use looser tolerances here as compared to in the binomial
            // sampling test since we're not sampling as many elements here
            // (we can never be sure that what randomness we have will allow for
            // a ring element to be sampled uniformly).
            assert!(percentage_error(mean, expected_mean) < 25.0, "The variance is {}.", variance);
            assert!(percentage_error(variance, expected_variance) < 25.0, "The variance is {}.", variance);
        }

        #[test]
        fn test_binomial_sampler_mean_and_variance(randomness in vec(any::<u8>(), 2 * (parameters::BINOMIAL_SAMPLING_COINS * 64))) {

            let expected_variance : f64 = (parameters::BINOMIAL_SAMPLING_COINS as f64) / 2.0;

            let mut mean : f64 = 0.0;
            let mut variance : f64 = 0.0;

            let ring_element_1 = sample_ring_element_binomial(randomness[0..parameters::BINOMIAL_SAMPLING_COINS * 64].try_into().unwrap());
            let ring_element_2 = sample_ring_element_binomial(randomness[parameters::BINOMIAL_SAMPLING_COINS * 64..].try_into().unwrap());

            let total_samples = ring_element_1.coefficients.len() + ring_element_2.coefficients.len();

            let ring_elements_chained = ring_element_1.coefficients
                                        .iter()
                                        .chain(ring_element_2.coefficients.iter());

            for coefficient in ring_elements_chained.clone() {
                mean += field_coefficient_to_binomial_sample(parameters::BINOMIAL_SAMPLING_COINS, coefficient.value);
            }
            mean /= total_samples as f64;

            for coefficient in ring_elements_chained {
                let binomial_sample = field_coefficient_to_binomial_sample(parameters::BINOMIAL_SAMPLING_COINS, coefficient.value);
                variance += (binomial_sample - mean) * (binomial_sample - mean);
            }
            variance /= (total_samples - 1) as f64;

            // The expected mean is 0.
            assert!(mean < 0.3, "The mean is {}.", mean);
            assert!(percentage_error(variance, expected_variance) < 20.0, "The variance is {}.", variance);
        }
    }
}
