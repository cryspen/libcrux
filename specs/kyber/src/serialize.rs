use hacspec_lib::{bit_vector::BitVector, ring::Bits};

use crate::parameters::{KyberFieldElement, KyberPolynomialRingElement, BITS_PER_COEFFICIENT};

fn to_little_endian_bit_vector(
    re: KyberPolynomialRingElement,
    bits_per_coefficient: usize,
) -> Vec<u8> {
    let mut ring_element_bits: Vec<u8> = Vec::new();
    for bits in re.coefficients().bits_chunks(bits_per_coefficient) {
        ring_element_bits.extend_from_slice(&bits);
    }

    ring_element_bits
}

/// Convert the associated ring element into a vector of
/// `|parameters::COEFFICIENTS_IN_RING_ELEMENT| * |bits_per_coefficient|`
/// bits, and output this vector as a byte array such that the first 8 bits of
/// the vector represent the first byte of the output, the next 8 bits the
/// next byte of the output, and so on ...
///
/// N.B.: While the specification states that `serialize_little_endian` is
/// the inverse of `deserialize_little_endian`, this is only the case for
/// this implementation when:
///
/// - each ring coefficient can fit into |bits_per_coefficient| (otherwise
///   lossy compression takes place)
/// - `|bits_per_coefficient| < |parameters::BITS_PER_COEFFICIENT|`, since
///   otherwise when `deserialize_little_endian` operates on 12 bits at a time,
///   it is not injective: the values 3329 + 1 and 1 for example both fit into
///   12 bits and map to the same `KyberFieldElement`
///
/// Otherwise `deserialize_little_endian` is not injective and therefore has
/// no left inverse.
pub fn serialize_little_endian(
    re: KyberPolynomialRingElement,
    bits_per_coefficient: usize,
) -> Vec<u8> {
    let mut serialized: Vec<u8> = Vec::new();

    for bit_vector in to_little_endian_bit_vector(re, bits_per_coefficient).chunks(8) {
        let mut byte_value: u8 = 0;
        for (i, &bit) in bit_vector.iter().enumerate() {
            byte_value |= bit << i;
        }

        serialized.push(byte_value);
    }

    serialized
}

fn field_element_from_little_endian_bit_vector(bit_vector: BitVector) -> KyberFieldElement {
    let mut value: u16 = 0;
    for (i, bit) in bit_vector.into_iter().enumerate() {
        value |= u16::from(bit) << i;
    }

    value.into()
}

/// Given a series of bytes representing a ring element in `|ring_element_bytes|`,
/// first convert them into a vector of bits in little-endian order; i.e.
/// the least significant `|bits_per_coefficient|` of `|ring_element_bytes[0]|`
/// are the first set of bits in the bitstream.
///
/// This vector is deserialized into a KyberPolynomialRingElement structure.
/// The first `|bits_per_coefficient|` represent the first coefficient of
/// the ring element, the second `|bits_per_coefficient|` the second coefficient,
/// and so on.
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
pub fn deserialize_little_endian(
    bits_per_coefficient: usize,
    ring_element_bytes: &[u8],
) -> KyberPolynomialRingElement {
    assert!(bits_per_coefficient <= BITS_PER_COEFFICIENT);

    // FIXME: rewrite like serialization without the `BitVector`.
    let ring_element_bits: BitVector = ring_element_bytes.into();
    let mut ring_element_bits = ring_element_bits.chunks(bits_per_coefficient);

    let mut deserialized = KyberPolynomialRingElement::ZERO;

    for i in 0..deserialized.len() {
        deserialized[i] =
            field_element_from_little_endian_bit_vector(ring_element_bits.next().unwrap());
    }

    deserialized
}

#[cfg(test)]
mod tests {
    use proptest::prelude::*;

    use super::*;
    use crate::compress::tests::arb_ring_element;

    proptest! {
        // TODO: Generalize this to sizes other than 12.
        #[test]
        fn deserialize_is_left_inverse_of_serialize_when_no_compression(ring_element in arb_ring_element(12)) {
            let ring_element_serialized = serialize_little_endian(ring_element, 12);
            assert_eq!(ring_element, deserialize_little_endian(12, &ring_element_serialized));
        }

        #[test]
        fn serialize_is_sometimes_left_inverse_of_deserialize_when_no_compression(ring_element in arb_ring_element(12)) {
            let ring_element_serialized = serialize_little_endian(ring_element, 12);
            assert_eq!(ring_element_serialized, serialize_little_endian(deserialize_little_endian(12, &ring_element_serialized), 12));
        }
    }
}
