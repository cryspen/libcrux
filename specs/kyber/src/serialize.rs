use crate::bit_vector::*;
use crate::field::FieldElement;
use crate::parameters;
use crate::ring::RingElement;

///
/// Given a series of bytes representing a ring element in `|ring_element_bytes|`,
/// first convert them into a vector of bits in little-endian order; i.e.
/// the least significant `|BITS_PER_COEFFICIENT|` of `|ring_element_bytes[0]|`
/// are the first set of bits in the bitstream.

/// This vector is deserialized into a RingElement structure. The first
/// `|BITS_PER_COEFFICIENT|` represent the first coefficient of the ring element,
/// the second `|BITS_PER_COEFFICIENT|` the second coefficient, and so on.
///
/// This function implements Algorithm 3 of the Kyber Round 3 specification,
/// which is reproduced below:
///
/// ```plaintext
/// Input: Byte array B ∈ B^{32*l}
/// Output: Polynomial f ∈ R_q
/// (β_0, . . . , β_{256l−1}) := BytesToBits(B)
/// for i from 0 to 255 do
///     f_i := sum(j = 0 to l−1)(β_{il+j}*2^{j})
/// end for
/// return f0 +f_1X +f_2X^2 +···+f_255X^255
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
                .expect("Slice have length parameters::BITS_PER_COEFFICIENT elements."),
        );
        ring_element.coefficients[i] = FieldElement::from_u16(coefficient);
    }
    ring_element
}

///
/// Given a `|ring_element|`, convert it into a vector of `|BITS_PER_RING_ELEMENT|`
/// bits, and output this vector as a byte array such that the first 8 bits of
/// the vector represent the first byte of the output, and so on.
///
/// N.B.: While the specification states that `serialize_ring_element` is the
/// inverse of `deserialize_ring_element`, this is strictly speaking not the case
/// in this implementation: While `deserialize_ring_element` is the left inverse
/// of `serialize_ring_element`, since `deserialize_ring_element` operates on
/// `|BITS_PER_COEFFICIENT|` bits at a time, it is not injective:
/// the values 3329 + 1 and 1 for example both fit into `|BITS_PER_COEFFICIENT|`
/// bits and map to the same field representative. Since `deserialize_ring_element`
/// is not injective, it has no left inverse.
///
pub(crate) fn serialize_ring_element(
    ring_element: &RingElement,
) -> [u8; parameters::BITS_PER_RING_ELEMENT / 8] {
    let ring_element_bits = ring_element_to_bit_vector(ring_element);

    let mut serialized = [0u8; parameters::BITS_PER_RING_ELEMENT / 8];

    for i in 0..serialized.len() {
        serialized[i] =
            bit_vector_as_u8(&ring_element_bits[i * 8..(i + 1) * 8].try_into().expect("Slice should have 8 elements."));
    }
    serialized
}

#[cfg(test)]
mod tests {
    use proptest::prelude::*;

    use super::*;
    use crate::ring::testing::arb_ring_element;

    proptest! {
        #[test]
        fn deserialize_is_left_inverse_of_serialize(ring_element in arb_ring_element()) {
            assert_eq!(ring_element, deserialize_ring_element(serialize_ring_element(&ring_element)));
        }

        #[test]
        fn serialize_is_sometimes_left_inverse_of_deserialize(ring_element in arb_ring_element()) {
            let ring_element_serialized = serialize_ring_element(&ring_element);
            assert_eq!(ring_element_serialized, serialize_ring_element(&deserialize_ring_element(ring_element_serialized)));
        }
    }
}
