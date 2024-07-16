// Functions for serializing and deserializing an error ring element.

use crate::{
    ntt::ntt,
    polynomial::{PolynomialRingElement, SIMDPolynomialRingElement},
    simd::{portable::PortableSIMDUnit, traits::Operations},
};

#[inline(always)]
pub(crate) fn serialize<const ETA: usize, const OUTPUT_SIZE: usize>(
    re: PolynomialRingElement,
) -> [u8; OUTPUT_SIZE] {
    let mut serialized = [0u8; OUTPUT_SIZE];

    let v_re = SIMDPolynomialRingElement::<PortableSIMDUnit>::from_polynomial_ring_element(re);

    match ETA {
        2 => {
            const OUTPUT_BYTES_PER_SIMD_UNIT: usize = 3;

            for (i, simd_unit) in v_re.simd_units.iter().enumerate() {
                serialized[i * OUTPUT_BYTES_PER_SIMD_UNIT..(i + 1) * OUTPUT_BYTES_PER_SIMD_UNIT]
                    .copy_from_slice(&PortableSIMDUnit::error_serialize::<
                        OUTPUT_BYTES_PER_SIMD_UNIT,
                    >(*simd_unit));
            }

            serialized
        }
        4 => {
            const OUTPUT_BYTES_PER_SIMD_UNIT: usize = 4;

            for (i, simd_unit) in v_re.simd_units.iter().enumerate() {
                serialized[i * OUTPUT_BYTES_PER_SIMD_UNIT..(i + 1) * OUTPUT_BYTES_PER_SIMD_UNIT]
                    .copy_from_slice(&PortableSIMDUnit::error_serialize::<
                        OUTPUT_BYTES_PER_SIMD_UNIT,
                    >(*simd_unit));
            }

            serialized
        }
        _ => unreachable!(),
    }
}

#[inline(always)]
fn deserialize<const ETA: usize>(serialized: &[u8]) -> PolynomialRingElement {
    let mut serialized_chunks = match ETA {
        2 => serialized.chunks(3),
        4 => serialized.chunks(4),
        _ => unreachable!(),
    };

    let mut result = SIMDPolynomialRingElement::ZERO();

    for i in 0..result.simd_units.len() {
        result.simd_units[i] =
            PortableSIMDUnit::error_deserialize::<ETA>(&serialized_chunks.next().unwrap());
    }

    result.to_polynomial_ring_element()
}

#[inline(always)]
pub(crate) fn deserialize_to_vector_then_ntt<
    const DIMENSION: usize,
    const ETA: usize,
    const RING_ELEMENT_SIZE: usize,
>(
    serialized: &[u8],
) -> [PolynomialRingElement; DIMENSION] {
    let mut ring_elements = [PolynomialRingElement::ZERO; DIMENSION];

    for (i, bytes) in serialized.chunks(RING_ELEMENT_SIZE).enumerate() {
        ring_elements[i] = ntt(deserialize::<ETA>(bytes));
    }

    ring_elements
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_deserialize_when_eta_is_2() {
        let serialized = [
            220, 24, 44, 136, 134, 36, 11, 195, 72, 82, 34, 144, 36, 33, 9, 196, 22, 70, 100, 148,
            65, 32, 163, 1, 210, 40, 14, 224, 38, 72, 33, 41, 136, 156, 146, 80, 25, 37, 50, 92,
            66, 140, 227, 144, 96, 9, 64, 141, 193, 50, 1, 140, 20, 141, 92, 32, 97, 2, 25, 42, 34,
            66, 50, 193, 72, 113, 202, 8, 16, 209, 54, 44, 129, 194, 48, 144, 20, 141, 228, 166,
            141, 228, 20, 144, 146, 54, 12, 99, 4, 140, 226, 18, 12, 194, 38, 97,
        ];

        let expected_coefficients = [
            -2, -1, -1, -2, 1, 2, -1, 1, 2, 1, 0, -1, 2, 1, 1, 1, -1, 1, -2, 1, -2, 1, 0, 0, 0, 0,
            1, 1, 0, 2, -2, -2, -2, -2, -2, 2, 0, 0, 0, 2, -2, 2, -1, -1, 1, -2, 1, 0, -2, -2, 1,
            0, 1, -1, 2, 0, 2, -2, -2, 1, 0, -1, 2, 2, 0, 0, -1, -2, 0, -2, -1, 2, 2, -2, -1, -1,
            0, 2, 0, 0, 1, -2, -2, -2, 0, 2, 0, -2, -2, -1, 0, 1, 1, 1, -2, 0, 1, -1, -2, 0, 0, -2,
            -2, 1, -2, -1, 1, 1, -2, 2, -1, -2, -1, -2, -1, 2, 1, 1, 2, -1, 1, 1, 2, 2, -2, 0, -1,
            -2, 1, 2, -1, 1, -1, 0, 2, 2, -2, 1, 0, 0, 1, 0, -1, -2, -2, -1, 1, 2, 0, 0, 2, -1, 0,
            2, -2, -2, 1, -2, 0, 1, 0, -2, 2, 1, -2, -2, -2, 1, 1, 2, -1, -2, -2, 0, -2, -1, 0, 1,
            -1, -2, 2, 2, -2, 2, 1, 0, -1, -1, -1, 2, -1, 1, 1, 2, 0, 1, -2, 1, -2, 1, 2, 0, 0, 0,
            1, 0, -1, -2, -2, -2, -1, -1, 0, -1, -1, -2, -2, -2, -1, 0, 1, 2, -2, -2, 0, 0, 0, -1,
            -1, 2, -1, 2, -1, -2, 1, 0, 2, 2, -1, -2, 0, -2, -1, 1, 1, 2, -1, 2, 0, 2, -1, -1, 0,
            0, 2, -1,
        ];

        assert_eq!(
            deserialize::<2>(&serialized).coefficients,
            expected_coefficients
        );
    }

    #[test]
    fn test_deserialize_when_eta_is_4() {
        let serialized = [
            22, 103, 55, 49, 34, 65, 50, 129, 52, 65, 21, 85, 82, 69, 3, 55, 52, 101, 80, 64, 114,
            136, 53, 8, 135, 67, 64, 71, 131, 21, 117, 81, 23, 99, 17, 84, 51, 23, 117, 56, 52, 85,
            131, 17, 22, 117, 85, 68, 34, 113, 87, 24, 65, 81, 2, 80, 118, 53, 34, 8, 32, 51, 51,
            82, 24, 2, 69, 0, 80, 68, 129, 133, 134, 17, 134, 82, 18, 21, 37, 114, 55, 87, 83, 8,
            80, 52, 103, 1, 84, 82, 99, 16, 86, 48, 16, 133, 17, 2, 67, 51, 120, 71, 19, 5, 72, 19,
            21, 103, 114, 115, 69, 36, 97, 68, 115, 56, 18, 83, 99, 32, 83, 88, 37, 71, 35, 82, 24,
            19,
        ];

        let expected_coefficients = [
            -2, 3, -3, -2, -3, 1, 3, 1, 2, 2, 3, 0, 2, 1, 3, -4, 0, 1, 3, 0, -1, 3, -1, -1, 2, -1,
            -1, 0, 1, 4, -3, 1, 0, 1, -1, -2, 4, -1, 4, 0, 2, -3, -4, -4, -1, 1, -4, 4, -3, -4, 1,
            0, 4, 0, -3, 0, 1, -4, -1, 3, -1, -3, 3, -1, -3, 3, 1, -2, 3, 3, 0, -1, 1, 1, -3, 3,
            -1, -3, -4, 1, 0, 1, -1, -1, 1, -4, 3, 3, -2, 3, -1, -3, -1, -1, 0, 0, 2, 2, 3, -3, -3,
            -1, -4, 3, 3, 0, 3, -1, 2, 4, 4, -1, -2, -3, -1, 1, 2, 2, -4, 4, 4, 2, 1, 1, 1, 1, 2,
            -1, -4, 3, 2, 4, -1, 0, 4, 4, 4, -1, 0, 0, 3, -4, -1, -4, -2, -4, 3, 3, -2, -4, 2, -1,
            2, 3, -1, 3, -1, 2, 2, -3, -3, 1, -3, -1, 1, -1, -4, 4, 4, -1, 0, 1, -3, -2, 3, 4, 0,
            -1, 2, -1, 1, -2, 4, 3, -2, -1, 4, 1, 4, 3, -1, -4, 3, 3, 2, 4, 1, 0, 1, 1, -4, -3, -3,
            0, 1, 3, -1, 4, -4, 0, 1, 3, -1, 3, -3, -2, 2, -3, 1, -3, -1, 0, 0, 2, 3, -2, 0, 0, 1,
            -3, -4, 1, 2, 3, 1, -1, 1, -2, 4, 2, 1, -1, -4, -1, -1, 2, -3, 0, 1, 2, 2, -1, -4, 3,
            1, 3,
        ];

        assert_eq!(
            deserialize::<4>(&serialized).coefficients,
            expected_coefficients
        );
    }
}
