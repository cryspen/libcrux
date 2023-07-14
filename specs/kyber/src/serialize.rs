use crate::bit_vector::*;
use crate::field::FieldElement;
use crate::parameters;
use crate::ring::RingElement;

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
/// ```plaintext
/// Input: Byte array B ∈ B32l
/// Output: Polynomial f ∈ Rq
/// (β0, . . . , β256l−1) := BytesToBits(B)
/// for i from 0 to 255 do
///     fi := sum(j = 0 to l−1)(βil+j 2j)
/// end for
/// return f0 +f1X +f2X2 +···+f255X255
/// ```
///
/// The Kyber Round 3 specification can be found at:
/// https://pq-crystals.org/kyber/data/kyber-specification-round3-20210131.pdf
///
pub(crate) fn deserialize_ring_element(
    ring_element_bytes: [u8; parameters::BITS_PER_RING_ELEMENT / 8],
) -> RingElement {
    let ring_element_bits = bytes_to_bit_vector(&ring_element_bytes[..]);
    assert_eq!(ring_element_bits.len(), parameters::BITS_PER_RING_ELEMENT);

    let mut ring_element: RingElement = RingElement::ZERO;

    for i in 0..ring_element.coefficients.len() {
        let coefficient = ring_coefficient_bits_as_u16(
            &ring_element_bits
                [i * parameters::BITS_PER_COEFFICIENT..(i + 1) * parameters::BITS_PER_COEFFICIENT]
                .try_into()
                .unwrap(),
        );
        ring_element.coefficients[i] = FieldElement::from_u16(coefficient);
    }
    ring_element
}

///
/// Given a |ring_element|, convert it into a vector of |BITS_PER_RING_ELEMENT|
/// bits, and output this vector as a byte array such that the first 8 bits of
/// the vector represent the first byte of the output, and so on.
///
/// N.B.: While the specification states that serialize_ring_element is the inverse of deserialize_ring_element,
/// this is strictly speaking not the case in this implementation: While deserialize_ring_element
/// is the left inverse of serialize_ring_element, since deserialize_ring_element operates on 12 bits at a
/// time, it is not injective: the values 3329 + 1 and 1 for example both fit
/// into 12 bits and map to the same field representative. Since deserialize_ring_element is not
/// injective, it has no left inverse.
///
pub(crate) fn serialize_ring_element(
    ring_element: &RingElement,
) -> [u8; parameters::BITS_PER_RING_ELEMENT / 8] {
    let ring_element_bits = ring_element_to_bit_vector(ring_element);

    let mut serialized = [0u8; parameters::BITS_PER_RING_ELEMENT / 8];

    for i in 0..serialized.len() {
        serialized[i] =
            bit_vector_as_u8(&ring_element_bits[i * 8..(i + 1) * 8].try_into().unwrap());
    }
    serialized
}

#[cfg(test)]
mod tests {
    use super::*;
    /*use crate::parameters;
    use quickcheck::Arbitrary;

    impl Arbitrary for [u8; parameters::BITS_PER_RING_ELEMENT / 8] {
        fn arbitrary(g: &mut quickcheck::Gen) -> [u8; parameters::BITS_PER_RING_ELEMENT / 8] {
            let rng = g.new(u8::BITS);
            let out = [0u8; parameters::BITS_PER_RING_ELEMENT / 8];

            for i in 0..out.len() {
                out[i] = g.gen::<u8>();
            }

            out
        }
    }*/

    quickcheck! {
        fn deserialize_is_left_inverse_of_serialize(ring_element: RingElement) -> bool {
            ring_element == deserialize_ring_element(serialize_ring_element(&ring_element))
        }

        // TODO: Figure out how to make this work.
        /*fn encode_is_sometimes_the_left_inverse_of_deserialize_ring_element(ring_element_bytes: [u8; parameters::BITS_PER_RING_ELEMENT / 8]) -> bool {
            let coefficients_less_than_modulus = true;
            let ring_element_bits = bytes_to_bits(&ring_element_bytes[..]);

            for i in 0..parameters::COEFFICIENTS_IN_RING_ELEMENT {
                let coefficient = bits_to_u16(&ring_element_bits[i*parameters::BITS_PER_COEFFICIENT..(i + 1)*parameters::BITS_PER_COEFFICIENT]);
                if coefficient >= parameters::FIELD_MODULUS {
                    coefficients_less_than_modulus = false;
                }
            }

            // coefficients_less_than_modulus => encode(deserialize_ring_element(x)) = x
            !coefficients_less_than_modulus || encode(deserialize_ring_element(ring_element_bytes))
        }*/
    }
}
