use crate::ring::RingElement;
use crate::field::FieldElement;
use crate::bit_vector::bytes_to_bits;
use crate::parameters;

///
/// Given a series of uniformly random bytes in |randomness|, sample uniformly
/// at random a ring element r_, which is treated as being the NTT representation
/// of a corresponding polynomial r.
///
/// This implementation uses rejection sampling; it is therefore possible the
/// supplied randomness is not enough to sample the element, in which case
/// an Err is returned and the caller must try again with fresh randomness.
///
/// This function implements Algorithm 1 of the Kyber Round 3 specification,
/// which is reproduced below:
///
/// Input: Byte stream B = b_0, b_1, b_2 ... ∈ B^*
/// Output: NTT-representation aˆ ∈ Rq of a ∈ Rq
/// i := 0
/// j := 0
/// while j < n do
///     d1 := bi + 256 · (bi+1 mod+16) d2 := ⌊bi+1/16⌋ + 16 · bi+2
///     if d1 < q then
///         aˆ j : = d 1
///         j := j + 1
///     end if
///     if d2 < q and j < n then aˆ j : = d 2
///         j := j + 1
///     end if
///     i := i + 3
/// end while
/// return aˆ0 + aˆ1X + · · · + aˆn−1Xn−1
///
/// The Kyber Round 3 specification can be found at:
/// https://pq-crystals.org/kyber/data/kyber-specification-round3-20210131.pdf
///
pub(crate) fn sample_ring_element_uniform(randomness : [u8; parameters::REJECTION_SAMPLING_BYTES]) -> Result<RingElement, &'static str> {
    let mut j : usize = 0;
    let mut sampled : RingElement = RingElement::ZERO;

    for i in (0..randomness.len()).step_by(3) {
        let byte = u16::from(randomness[i]);
        let byte1 = u16::from(randomness[i + 1]);
        let byte2 = u16::from(randomness[i + 2]);

        let d1 = byte + (256 * (byte1 % 16));

        // Integer division is flooring in Rust.
        let d2 = (byte1 / 16) + (16 * byte2); 

        if d1 < parameters::Q && j < sampled.coefficients.len() {
            sampled.coefficients[j] = FieldElement::from_u16(d1);
            j += 1
        }
        if d2 < parameters::Q && j < sampled.coefficients.len() { 
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
/// Given a series of uniformly random bytes in |randomness|, sample
/// a ring element from a binomial distribution centered at 0 that uses two sets
/// of |parameters::ETA| coin flips.
///
/// This function implements Algorithm 2 of the Kyber Round 3 specification,
/// which is reproduced below:
///
/// Input: Byte array B = (b0, b1, . . . , b64η−1) ∈ B64η
/// Output: Polynomial f ∈ Rq
/// (β0, . . . , β512η−1) := BytesToBits(B)
/// for i from 0 to 255 do
///     a := sum(j = 0 to η−1)(β2iη+j)
///     b := sum(j = 0 to η−1)(β2iη+η+j)
///     fi := a − b
/// end for
/// return f0 +f1X +f2X2 +···+f255X255
///
/// The Kyber Round 3 specification can be found at:
/// https://pq-crystals.org/kyber/data/kyber-specification-round3-20210131.pdf
///
pub(crate) fn sample_ring_element_binomial(randomness : [u8; parameters::ETA * 64]) -> RingElement {
    let random_bits = bytes_to_bits(&randomness[..]);
    assert_eq!(random_bits.len(), parameters::ETA * 64 * (u8::BITS as usize));

    let mut sampled : RingElement = RingElement::ZERO;

    for i in 0..sampled.coefficients.len() {
        let mut a : u8 = 0;
        for j in 0..parameters::ETA {
            a += random_bits[2 * i * parameters::ETA + j];
        }
        let a = FieldElement::from_u16(u16::from(a));

        let mut b : u8 = 0;
        for j in 0..parameters::ETA {
            b += random_bits[2 * i * parameters::ETA + parameters::ETA + j];
        }
        let b = FieldElement::from_u16(u16::from(b));

        sampled.coefficients[i] = a.subtract(&b);
    }

    sampled
}

#[cfg(test)]
mod tests {
    use super::*;
    use parameters::REJECTION_SAMPLING_BYTES;

    #[test]
    fn uniform_sample_from_all_zeros() {
        let r = sample_ring_element_uniform([0; REJECTION_SAMPLING_BYTES]).unwrap();

        for coefficient in r.coefficients.iter() {
            assert_eq!(coefficient.value, 0);
        }
    }

    #[test]
    #[should_panic]
    fn uniform_sample_from_all_u8_max() {
        let _ = sample_ring_element_uniform([u8::MAX; REJECTION_SAMPLING_BYTES]).unwrap();
    }

    // TODO: Add distribution testing.
}
