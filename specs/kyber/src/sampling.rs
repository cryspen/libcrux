use crate::bit_vector::bytes_to_bit_vector;
use crate::field::FieldElement;
use crate::parameters;
use crate::ring::RingElement;

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
) -> Result<RingElement, &'static str> {
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
            sampled.coefficients[j] = FieldElement::from_u16(d1);
            j += 1
        }
        if d2 < parameters::FIELD_MODULUS && j < sampled.coefficients.len() {
            sampled.coefficients[j] = FieldElement::from_u16(d2);
            j += 1;
        }
        // In an efficient implementation, we'd break when
        // j == sampled.coefficients.len, but we've forgone this to make
        // the implementation easier to read.
    }

    if j == sampled.coefficients.len() {
        Ok(sampled)
    } else {
        Err("Not enough randomness to sample the ring element.")
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
/// - If v >= 0, Pr[v] = BINOMIAL_COEFFICIENT(2 * ETA; ETA + i) / 2 ^ (2 * ETA)
///
/// where -2 denotes the representative `|MODULUS| - 2`, and -1 the representative
/// `|MODULUS| - 1`.
///
/// This function implements Algorithm 2 of the Kyber Round 3 specification,
/// which is reproduced below:
///
/// ```plaintext
/// Input: Byte array B = (b0, b1, . . . , b64η−1) ∈ B64η
/// Output: Polynomial f ∈ Rq
/// (β0, . . . , β512η−1) := BytesToBits(B)
/// for i from 0 to 255 do
///     a := sum(j = 0 to η−1)(β2iη+j)
///     b := sum(j = 0 to η−1)(β2iη+η+j)
///     fi := a − b
/// end for
/// return f0 +f1X +f2X2 +···+f255X255
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
        let coin_tosses_a = FieldElement::from_u8(coin_tosses);

        coin_tosses = 0;
        for j in 0..parameters::BINOMIAL_SAMPLING_COINS {
            coin_tosses += random_bits[(2 * i + 1) * parameters::BINOMIAL_SAMPLING_COINS + j];
        }
        let coin_tosses_b = FieldElement::from_u8(coin_tosses);

        sampled.coefficients[i] = coin_tosses_a.subtract(&coin_tosses_b);
    }

    sampled
}

#[cfg(test)]
mod tests {
    use proptest::prelude::*;
    use proptest::collection::vec;

    use super::*;
    use parameters::REJECTION_SAMPLING_SEED_SIZE;

    #[test]
    fn uniform_sample_from_all_zeros() {
        let r = sample_ring_element_uniform([0; REJECTION_SAMPLING_SEED_SIZE]).unwrap();

        for coefficient in r.coefficients.iter() {
            assert_eq!(coefficient.value, 0);
        }
    }

    #[test]
    #[should_panic]
    fn uniform_sample_from_all_u8_max() {
        let _ = sample_ring_element_uniform([u8::MAX; REJECTION_SAMPLING_SEED_SIZE]).unwrap();
    }

    proptest! {

        fn binomial_sampler_calculate_variance(sampling_coins : usize) {

        }

        #[test]
        fn test_binomial_sampler_mean_and_variance(randomness in vec(any::<u8>(), 2 * (parameters::BINOMIAL_SAMPLING_COINS * 64))) {
            // TODO: Make this function general.
            assert_eq!(parameters::BINOMIAL_SAMPLING_COINS, 2);

            let mut expected_mean : f64 = 0.0;
            let mut expected_variance : f64 = 0.0;

            let mut mean : f64 = 0.0;
            let mut variance : f64 = 0.0;

            let ring_element_1 = sample_ring_element_binomial(randomness[0..parameters::BINOMIAL_SAMPLING_COINS * 64].try_into().unwrap());
            let ring_element_2 = sample_ring_element_binomial(randomness[parameters::BINOMIAL_SAMPLING_COINS * 64..].try_into().unwrap());

            let ring_elements_chained = ring_element_1.coefficients
                                        .iter()
                                        .chain(ring_element_2.coefficients.iter());

            for coefficient in ring_elements_chained.clone() {
                mean += match coefficient.value {
                            3327 => -2.0,
                            3328 => -1.0,
                            0 => 0.0,
                            1 => 1.0,
                            2 => 2.0,
                            other => panic!("{} should not be a coefficient.", other)
                        }
            }
            mean /= (ring_element_1.coefficients.len() + ring_element_2.coefficients.len()) as f64;

            for coefficient in ring_elements_chained {
                let (coefficient_value, coefficient_probability) = match coefficient.value {
                            3327 => (-2.0, 0.0625),
                            3328 => (-1.0, 0.25),
                            0 => (0.0, 0.375),
                            1 => (1.0, 0.25),
                            2 => (2.0, 0.0625),
                            other => panic!("{} should not be a coefficient.", other)
                        };
                variance += (coefficient_value - mean) * (coefficient_value - mean);
                variance *= coefficient_probability;
            }

            // The expected mean is 0.
            // If we sampled more elements, we could use a tighter tolerance.
            assert!(mean < 1.0, "The mean is {}.", mean);

            // The expected variance is 1.
            // If we sampled more elements, we could use a tighter tolerance.
            assert!((variance - 1.0).abs() < 1.0, "The variance is {}.", variance);
        }
    }

}
