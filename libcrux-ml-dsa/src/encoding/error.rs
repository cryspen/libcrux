// ---------------------------------------------------------------------------
// Functions for serializing and deserializing an error ring element.
// ---------------------------------------------------------------------------

use crate::{arithmetic::PolynomialRingElement, ntt::ntt};

#[inline(always)]
fn serialize_when_eta_is_2<const OUTPUT_SIZE: usize>(
    re: PolynomialRingElement,
) -> [u8; OUTPUT_SIZE] {
    let mut serialized = [0u8; OUTPUT_SIZE];
    const ETA: i32 = 2;

    for (i, coefficients) in re.coefficients.chunks_exact(8).enumerate() {
        let coefficient0 = (ETA - coefficients[0]) as u8;
        let coefficient1 = (ETA - coefficients[1]) as u8;
        let coefficient2 = (ETA - coefficients[2]) as u8;
        let coefficient3 = (ETA - coefficients[3]) as u8;
        let coefficient4 = (ETA - coefficients[4]) as u8;
        let coefficient5 = (ETA - coefficients[5]) as u8;
        let coefficient6 = (ETA - coefficients[6]) as u8;
        let coefficient7 = (ETA - coefficients[7]) as u8;

        serialized[3 * i + 0] = (coefficient2 << 6) | (coefficient1 << 3) | coefficient0;
        serialized[3 * i + 1] =
            (coefficient5 << 7) | (coefficient4 << 4) | (coefficient3 << 1) | (coefficient2 >> 2);
        serialized[3 * i + 2] = (coefficient7 << 5) | (coefficient6 << 2) | (coefficient5 >> 1);
    }

    serialized
}

#[inline(always)]
fn serialize_when_eta_is_4<const OUTPUT_SIZE: usize>(
    re: PolynomialRingElement,
) -> [u8; OUTPUT_SIZE] {
    let mut serialized = [0u8; OUTPUT_SIZE];
    const ETA: i32 = 4;

    for (i, coefficients) in re.coefficients.chunks_exact(2).enumerate() {
        let coefficient0 = (ETA - coefficients[0]) as u8;
        let coefficient1 = (ETA - coefficients[1]) as u8;
        serialized[i] = (coefficient1 << 4) | coefficient0;
    }

    serialized
}

#[inline(always)]
pub(crate) fn serialize<const ETA: usize, const OUTPUT_SIZE: usize>(
    re: PolynomialRingElement,
) -> [u8; OUTPUT_SIZE] {
    match ETA {
        2 => serialize_when_eta_is_2::<OUTPUT_SIZE>(re),
        4 => serialize_when_eta_is_4::<OUTPUT_SIZE>(re),
        _ => unreachable!(),
    }
}

#[inline(always)]
fn deserialize_when_eta_is_2(serialized: &[u8]) -> PolynomialRingElement {
    let mut re = PolynomialRingElement::ZERO;
    const ETA: i32 = 2;

    for (i, bytes) in serialized.chunks_exact(3).enumerate() {
        let byte0 = bytes[0] as i32;
        let byte1 = bytes[1] as i32;
        let byte2 = bytes[2] as i32;

        re.coefficients[8 * i + 0] = (byte0 >> 0) & 7;
        re.coefficients[8 * i + 1] = (byte0 >> 3) & 7;
        re.coefficients[8 * i + 2] = ((byte0 >> 6) | (byte1 << 2)) & 7;
        re.coefficients[8 * i + 3] = (byte1 >> 1) & 7;
        re.coefficients[8 * i + 4] = (byte1 >> 4) & 7;
        re.coefficients[8 * i + 5] = ((byte1 >> 7) | (byte2 << 1)) & 7;
        re.coefficients[8 * i + 6] = (byte2 >> 2) & 7;
        re.coefficients[8 * i + 7] = (byte2 >> 5) & 7;

        re.coefficients[8 * i + 0] = ETA - re.coefficients[8 * i + 0];
        re.coefficients[8 * i + 1] = ETA - re.coefficients[8 * i + 1];
        re.coefficients[8 * i + 2] = ETA - re.coefficients[8 * i + 2];
        re.coefficients[8 * i + 3] = ETA - re.coefficients[8 * i + 3];
        re.coefficients[8 * i + 4] = ETA - re.coefficients[8 * i + 4];
        re.coefficients[8 * i + 5] = ETA - re.coefficients[8 * i + 5];
        re.coefficients[8 * i + 6] = ETA - re.coefficients[8 * i + 6];
        re.coefficients[8 * i + 7] = ETA - re.coefficients[8 * i + 7];
    }

    re
}

#[inline(always)]
fn deserialize_when_eta_is_4(serialized: &[u8]) -> PolynomialRingElement {
    let mut re = PolynomialRingElement::ZERO;
    const ETA: i32 = 4;

    for (i, byte) in serialized.into_iter().enumerate() {
        re.coefficients[2 * i + 0] = ETA - ((byte & 0xF) as i32);
        re.coefficients[2 * i + 1] = ETA - ((byte >> 4) as i32);
    }

    re
}

#[inline(always)]
fn deserialize<const ETA: usize>(serialized: &[u8]) -> PolynomialRingElement {
    match ETA {
        2 => deserialize_when_eta_is_2(serialized),
        4 => deserialize_when_eta_is_4(serialized),
        _ => unreachable!(),
    }
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
