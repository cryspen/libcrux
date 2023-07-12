use crate::ring::RingElement;
use crate::field::FieldElement;
use crate::bit_vector::*;
use crate::parameters;

///
/// Given a series of bytes representing a ring element in |ring_element_bytes|,
/// first convert them into a vector of bits in little-endian order; i.e.
/// the least significant |BITS_PER_COEFFICIENT| of |ring_element_bytes[0]|
/// are the first set of bits in the bitstream.

/// This vector is deserialized into a RingElement structure. The first
/// |BITS_PER_COEFFICIENT| represent the first coefficient of the ring element,
/// the second |BITS_PER_COEFFICIENT| the second coefficient, and so on.
///
/// This function implements Algorithm 3 of the Kyber Round 3 specification,
/// which is reproduced below:
///
/// Input: Byte array B ∈ B32l
/// Output: Polynomial f ∈ Rq
/// (β0, . . . , β256l−1) := BytesToBits(B)
/// for i from 0 to 255 do
///     fi := sum(j = 0 to l−1)(βil+j 2j)
/// end for
/// return f0 +f1X +f2X2 +···+f255X255
///
/// The Kyber Round 3 specification can be found at:
/// https://pq-crystals.org/kyber/data/kyber-specification-round3-20210131.pdf
///
pub(crate) fn decode(ring_element_bytes : [u8; parameters::BITS_PER_RING_ELEMENT / 8]) -> RingElement {
    let ring_element_bits = bytes_to_bits(&ring_element_bytes[..]);
    assert_eq!(ring_element_bits.len(), parameters::BITS_PER_RING_ELEMENT);

    let mut out : RingElement = RingElement::ZERO;

    for i in 0..out.coefficients.len() {
        let coefficient = bits_to_u16(&ring_element_bits[i*parameters::BITS_PER_COEFFICIENT..(i + 1)*parameters::BITS_PER_COEFFICIENT]);
        out.coefficients[i] = FieldElement::from_u16(coefficient);
    }
    out
}

///
/// Given a |ring_element|, convert it into a vector of |BITS_PER_RING_ELEMENT|
/// bits, and output this vector as a byte array such that the first 8 bits of
/// the vector represent the first byte of the output, and so on.
///
pub(crate) fn encode(ring_element : &RingElement) -> [u8; parameters::BITS_PER_RING_ELEMENT / 8] {
    let ring_element_bits = ring_element_to_bits(ring_element);
    assert_eq!(ring_element_bits.len(), parameters::BITS_PER_RING_ELEMENT);

    let mut out = [0u8; parameters::BITS_PER_RING_ELEMENT / 8];

    for i in 0..out.len() {
        out[i] = bits_to_u8(&ring_element_bits[i*8..(i+1)*8]);
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    quickcheck! {
        fn decode_is_left_inverse_of_encode(ring_element: RingElement) -> bool {
            ring_element == decode(encode(&ring_element))
        }
    }

    // TODO: Look at encode(decode(x)) == x
}
