use crate::ring::RingElement;

///
/// Given an array of `|bytes|`, convert it into a bit vector of u8s such that
/// each u8 stores a 0 or a 1. The output bits are written in little-endian order,
/// i.e., if the output vector is `|out|`, then
/// - the least significant bit of `|bytes[0]|` is `|out[0]|`
/// - the next least significant bit of `|bytes[0]|` is `|out[1]|`
/// ... and so on.
///
pub(crate) fn bytes_to_bit_vector(bytes: &[u8]) -> Vec<u8> {
    let mut out = Vec::with_capacity(bytes.len() * 8);

    for byte in bytes {
        for j in 0..u8::BITS {
            out.push((byte >> j) & 1);
        }
    }
    out
}

///
/// Given a RingElement `|ring_element|`, convert it into a bit vector of u8s
/// such that each u8 stores a 0 or a 1. The output bits are written in
/// little-endian order, i.e., if the output vector is `|out|`, then:
///
/// - the least significant bit of `|r.coefficients.value[0]|` is `|out[0]|`
/// - the next least significant bit of `|r.coefficients.value[0]|` is `|out[1]|`
/// ... and so on.
///
pub(crate) fn ring_element_to_bit_vector(
    bits_per_coefficient : usize,
    ring_element: &RingElement,
) -> Vec<u8> {
    let mut out : Vec<u8> = Vec::new();

    for coefficient in ring_element.coefficients.iter() {
        for j in 0..bits_per_coefficient {
            out.push(((coefficient.value >> j) & 1).try_into().expect(
                "u16 -> u8 conversion should succeed since, for any x, x & 1 is either 0 or 1.",
            ));
        }
    }
    out
}

///
/// Given a ring coefficient stored as a bit vector in `|ring_coefficient_bits|`,
/// output the value it represents as a u16. The coefficient is assumed to be
/// stored in `|ring_coefficient_bits|` in little-endian order.
///
pub(crate) fn ring_coefficient_bits_as_u16(
    bits_per_coefficient : usize,
    ring_coefficient_bits: &[u8],
) -> u16 {
    assert!(bits_per_coefficient <= u16::BITS.try_into().unwrap());
    assert_eq!(ring_coefficient_bits.len(), bits_per_coefficient);

    let mut ring_coefficient: u16 = 0;
    for (i, bit) in ring_coefficient_bits.iter().enumerate() {
        ring_coefficient |= u16::from(*bit) << i;
    }
    ring_coefficient
}

///
/// Given a byte stored as a bit vector in `|bit_vector|`, output the value it
/// represents as a u8. The byte is assumed to be stored in `|bit_vector|` in
/// little-endian order.
///
pub(crate) fn bit_vector_as_u8(bit_vector: &[u8; 8]) -> u8 {
    let mut byte_value: u8 = 0;

    for (i, bit) in bit_vector.iter().enumerate() {
        byte_value |= *bit << i;
    }

    byte_value
}

#[cfg(test)]
mod tests {
    use proptest::array;
    use proptest::prelude::*;

    use super::*;
    use crate::ring::testing::arb_ring_element;
    use crate::parameters;

    proptest! {
        #[test]
        fn bytes_to_bit_vector_and_back(bytes in array::uniform32(any::<u8>())) {

            let bit_vector : [u8; 32 * 8] = bytes_to_bit_vector(&bytes).try_into().unwrap();
            for (i, byte) in bytes.into_iter().enumerate() {
                let bit_vector_of_byte : [u8; 8] = bit_vector[i*8..(i+1)*8].try_into().unwrap();
                assert_eq!(byte, bit_vector_as_u8(&bit_vector_of_byte));
            }
        }

        #[test]
        fn ring_element_to_bit_vector_and_back(ring_element in arb_ring_element()) {
            let ring_element_as_bits = ring_element_to_bit_vector(12, &ring_element);

            for (i, coefficient) in ring_element.coefficients.into_iter().enumerate() {
                let bit_vector_of_ring_coefficient = &ring_element_as_bits[i*parameters::BITS_PER_COEFFICIENT..(i+1)*parameters::BITS_PER_COEFFICIENT];

                assert_eq!(coefficient.value, ring_coefficient_bits_as_u16(12, bit_vector_of_ring_coefficient.try_into().unwrap()));
            }
        }
    }
}
