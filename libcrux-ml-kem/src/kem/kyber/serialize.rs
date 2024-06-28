use super::{
    arithmetic::{to_unsigned_representative, FieldElement, PolynomialRingElement},
    compress::{
        compress_ciphertext_coefficient, compress_message_coefficient,
        decompress_ciphertext_coefficient, decompress_message_coefficient,
    },
    constants::{BYTES_PER_RING_ELEMENT, SHARED_SECRET_SIZE},
    helper::cloop,
};
use crate::hax_utils::hax_debug_assert;

#[inline(always)]
pub(super) fn compress_then_serialize_message(
    re: PolynomialRingElement,
) -> [u8; SHARED_SECRET_SIZE] {
    let mut serialized = [0u8; SHARED_SECRET_SIZE];

    cloop! {
        for (i, coefficients) in re.coefficients.chunks_exact(8).enumerate() {
            cloop! {
                for (j, coefficient) in coefficients.iter().enumerate() {
                    let coefficient = to_unsigned_representative(*coefficient);

                    let coefficient_compressed = compress_message_coefficient(coefficient);

                    serialized[i] |= coefficient_compressed << j
                }
            }
        }
    }

    serialized
}
#[inline(always)]
pub(super) fn deserialize_then_decompress_message(
    serialized: [u8; SHARED_SECRET_SIZE],
) -> PolynomialRingElement {
    let mut re = PolynomialRingElement::ZERO;

    cloop! {
        for (i, byte) in serialized.into_iter().enumerate() {
            for j in 0..8 {
                let coefficient_compressed = ((byte >> j) & 0x1) as FieldElement;
                re.coefficients[8 * i + j] = decompress_message_coefficient(coefficient_compressed);
            }
        }
    }

    re
}

#[inline(always)]
pub(super) fn serialize_uncompressed_ring_element(
    re: PolynomialRingElement,
) -> [u8; BYTES_PER_RING_ELEMENT] {
    let mut serialized = [0u8; BYTES_PER_RING_ELEMENT];

    cloop! {
        for (i, coefficients) in re.coefficients.chunks_exact(2).enumerate() {
            let coefficient1 = to_unsigned_representative(coefficients[0]);
            let coefficient2 = to_unsigned_representative(coefficients[1]);

            let (coef1, coef2, coef3) = compress_coefficients_3(coefficient1, coefficient2);
            serialized[3 * i] = coef1;
            serialized[3 * i + 1] = coef2;
            serialized[3 * i + 2] = coef3;
        }
    }

    serialized
}

#[inline(always)]
fn compress_coefficients_3(coefficient1: u16, coefficient2: u16) -> (u8, u8, u8) {
    let coef1 = (coefficient1 & 0xFF) as u8;
    let coef2 = ((coefficient1 >> 8) | ((coefficient2 & 0x0F) << 4)) as u8;
    let coef3 = ((coefficient2 >> 4) & 0xFF) as u8;
    (coef1, coef2, coef3)
}

#[inline(always)]
pub(super) fn deserialize_to_uncompressed_ring_element(serialized: &[u8]) -> PolynomialRingElement {
    hax_debug_assert!(serialized.len() == BYTES_PER_RING_ELEMENT);

    let mut re = PolynomialRingElement::ZERO;

    cloop! {
        for (i, bytes) in serialized.chunks_exact(3).enumerate() {
            let byte1 = bytes[0] as FieldElement;
            let byte2 = bytes[1] as FieldElement;
            let byte3 = bytes[2] as FieldElement;

            re.coefficients[2 * i] = (byte2 & 0x0F) << 8 | (byte1 & 0xFF);
            re.coefficients[2 * i + 1] = (byte3 << 4) | ((byte2 >> 4) & 0x0F);
        }
    }

    re
}

/// Only use with public values.
///
/// This MUST NOT be used with secret inputs, like its caller `deserialize_ring_elements_reduced`.
#[inline(always)]
fn deserialize_to_reduced_ring_element(ring_element: &[u8]) -> PolynomialRingElement {
    hax_debug_assert!(ring_element.len() == BYTES_PER_RING_ELEMENT);

    let mut re = PolynomialRingElement::ZERO;

    cloop! {
        for (i, bytes) in ring_element.chunks_exact(3).enumerate() {
            let byte1 = bytes[0] as FieldElement;
            let byte2 = bytes[1] as FieldElement;
            let byte3 = bytes[2] as FieldElement;

            // The modulus here is ok because the input must be public.
            // XXX: The awkward code here is necessary to work around Charon shortcomings.
            re.coefficients[2 * i] = (byte2 & 0x0F) << 8 | (byte1 & 0xFF);
            let tmp = re.coefficients[2 * i] % 3329; // FIELD_MODULUS
            re.coefficients[2 * i] = tmp;

            re.coefficients[2 * i + 1] = (byte3 << 4) | ((byte2 >> 4) & 0x0F);
            let tmp = re.coefficients[2 * i + 1] % 3329; // FIELD_MODULUS
            re.coefficients[2 * i + 1] = tmp;
        }
    }

    re
}

/// This function deserializes ring elements and reduces the result by the field
/// modulus.
///
/// This function MUST NOT be used on secret inputs.
#[inline(always)]
pub(super) fn deserialize_ring_elements_reduced<const PUBLIC_KEY_SIZE: usize, const K: usize>(
    public_key: &[u8],
) -> [PolynomialRingElement; K] {
    let mut deserialized_pk = [PolynomialRingElement::ZERO; K];
    cloop! {
        for (i, ring_element) in public_key
            .chunks_exact(BYTES_PER_RING_ELEMENT)
            .enumerate()
        {
            deserialized_pk[i] =deserialize_to_reduced_ring_element(ring_element);
        }
    }
    deserialized_pk
}

#[inline(always)]
fn compress_then_serialize_10<const OUT_LEN: usize>(re: PolynomialRingElement) -> [u8; OUT_LEN] {
    let mut serialized = [0u8; OUT_LEN];

    cloop! {
        for (i, coefficients) in re.coefficients.chunks_exact(4).enumerate() {
            let coefficient1 =
                compress_ciphertext_coefficient(10, to_unsigned_representative(coefficients[0]));
            let coefficient2 =
                compress_ciphertext_coefficient(10, to_unsigned_representative(coefficients[1]));
            let coefficient3 =
                compress_ciphertext_coefficient(10, to_unsigned_representative(coefficients[2]));
            let coefficient4 =
                compress_ciphertext_coefficient(10, to_unsigned_representative(coefficients[3]));

            let (coef1, coef2, coef3, coef4, coef5) =
                compress_coefficients_10(coefficient1, coefficient2, coefficient3, coefficient4);
            serialized[5 * i] = coef1;
            serialized[5 * i + 1] = coef2;
            serialized[5 * i + 2] = coef3;
            serialized[5 * i + 3] = coef4;
            serialized[5 * i + 4] = coef5;
        }
    }

    serialized
}

#[inline(always)]
fn compress_coefficients_10(
    coefficient1: i32,
    coefficient2: i32,
    coefficient3: i32,
    coefficient4: i32,
) -> (u8, u8, u8, u8, u8) {
    let coef1 = (coefficient1 & 0xFF) as u8;
    let coef2 = ((coefficient2 & 0x3F) as u8) << 2 | ((coefficient1 >> 8) & 0x03) as u8;
    let coef3 = ((coefficient3 & 0x0F) as u8) << 4 | ((coefficient2 >> 6) & 0x0F) as u8;
    let coef4 = ((coefficient4 & 0x03) as u8) << 6 | ((coefficient3 >> 4) & 0x3F) as u8;
    let coef5 = ((coefficient4 >> 2) & 0xFF) as u8;
    (coef1, coef2, coef3, coef4, coef5)
}

#[inline(always)]
fn compress_then_serialize_11<const OUT_LEN: usize>(re: PolynomialRingElement) -> [u8; OUT_LEN] {
    let mut serialized = [0u8; OUT_LEN];

    cloop! {
        for (i, coefficients) in re.coefficients.chunks_exact(8).enumerate() {
            let coefficient1 =
                compress_ciphertext_coefficient(11, to_unsigned_representative(coefficients[0]));
            let coefficient2 =
                compress_ciphertext_coefficient(11, to_unsigned_representative(coefficients[1]));
            let coefficient3 =
                compress_ciphertext_coefficient(11, to_unsigned_representative(coefficients[2]));
            let coefficient4 =
                compress_ciphertext_coefficient(11, to_unsigned_representative(coefficients[3]));
            let coefficient5 =
                compress_ciphertext_coefficient(11, to_unsigned_representative(coefficients[4]));
            let coefficient6 =
                compress_ciphertext_coefficient(11, to_unsigned_representative(coefficients[5]));
            let coefficient7 =
                compress_ciphertext_coefficient(11, to_unsigned_representative(coefficients[6]));
            let coefficient8 =
                compress_ciphertext_coefficient(11, to_unsigned_representative(coefficients[7]));

            let (coef1, coef2, coef3, coef4, coef5, coef6, coef7, coef8, coef9, coef10, coef11) =
                compress_coefficients_11(
                    coefficient1,
                    coefficient2,
                    coefficient3,
                    coefficient4,
                    coefficient5,
                    coefficient6,
                    coefficient7,
                    coefficient8,
                );
            serialized[11 * i] = coef1;
            serialized[11 * i + 1] = coef2;
            serialized[11 * i + 2] = coef3;
            serialized[11 * i + 3] = coef4;
            serialized[11 * i + 4] = coef5;
            serialized[11 * i + 5] = coef6;
            serialized[11 * i + 6] = coef7;
            serialized[11 * i + 7] = coef8;
            serialized[11 * i + 8] = coef9;
            serialized[11 * i + 9] = coef10;
            serialized[11 * i + 10] = coef11;
        }
    }

    serialized
}

#[inline(always)]
fn compress_coefficients_11(
    coefficient1: i32,
    coefficient2: i32,
    coefficient3: i32,
    coefficient4: i32,
    coefficient5: i32,
    coefficient6: i32,
    coefficient7: i32,
    coefficient8: i32,
) -> (u8, u8, u8, u8, u8, u8, u8, u8, u8, u8, u8) {
    let coef1 = coefficient1 as u8;
    let coef2 = ((coefficient2 & 0x1F) as u8) << 3 | ((coefficient1 >> 8) as u8);
    let coef3 = ((coefficient3 & 0x3) as u8) << 6 | ((coefficient2 >> 5) as u8);
    let coef4 = ((coefficient3 >> 2) & 0xFF) as u8;
    let coef5 = ((coefficient4 & 0x7F) as u8) << 1 | (coefficient3 >> 10) as u8;
    let coef6 = ((coefficient5 & 0xF) as u8) << 4 | (coefficient4 >> 7) as u8;
    let coef7 = ((coefficient6 & 0x1) as u8) << 7 | (coefficient5 >> 4) as u8;
    let coef8 = ((coefficient6 >> 1) & 0xFF) as u8;
    let coef9 = ((coefficient7 & 0x3F) as u8) << 2 | (coefficient6 >> 9) as u8;
    let coef10 = ((coefficient8 & 0x7) as u8) << 5 | (coefficient7 >> 6) as u8;
    let coef11 = (coefficient8 >> 3) as u8;
    (
        coef1, coef2, coef3, coef4, coef5, coef6, coef7, coef8, coef9, coef10, coef11,
    )
}
#[inline(always)]
pub(super) fn compress_then_serialize_ring_element_u<
    const COMPRESSION_FACTOR: usize,
    const OUT_LEN: usize,
>(
    re: PolynomialRingElement,
) -> [u8; OUT_LEN] {
    hax_debug_assert!((COEFFICIENTS_IN_RING_ELEMENT * COMPRESSION_FACTOR) / 8 == OUT_LEN);

    match COMPRESSION_FACTOR as u32 {
        10 => compress_then_serialize_10(re),
        11 => compress_then_serialize_11(re),
        _ => unreachable!(),
    }
}

#[inline(always)]
fn compress_then_serialize_4<const OUT_LEN: usize>(re: PolynomialRingElement) -> [u8; OUT_LEN] {
    let mut serialized = [0u8; OUT_LEN];

    cloop! {
        for (i, coefficients) in re.coefficients.chunks_exact(2).enumerate() {
            let coefficient1 =
                compress_ciphertext_coefficient(4, to_unsigned_representative(coefficients[0])) as u8;
            let coefficient2 =
                compress_ciphertext_coefficient(4, to_unsigned_representative(coefficients[1])) as u8;

            serialized[i] = (coefficient2 << 4) | coefficient1;
        }
    }

    serialized
}

#[inline(always)]
fn compress_then_serialize_5<const OUT_LEN: usize>(re: PolynomialRingElement) -> [u8; OUT_LEN] {
    let mut serialized = [0u8; OUT_LEN];

    cloop! {
        for (i, coefficients) in re.coefficients.chunks_exact(8).enumerate() {
            let coefficient1 =
                compress_ciphertext_coefficient(5, to_unsigned_representative(coefficients[0])) as u8;
            let coefficient2 =
                compress_ciphertext_coefficient(5, to_unsigned_representative(coefficients[1])) as u8;
            let coefficient3 =
                compress_ciphertext_coefficient(5, to_unsigned_representative(coefficients[2])) as u8;
            let coefficient4 =
                compress_ciphertext_coefficient(5, to_unsigned_representative(coefficients[3])) as u8;
            let coefficient5 =
                compress_ciphertext_coefficient(5, to_unsigned_representative(coefficients[4])) as u8;
            let coefficient6 =
                compress_ciphertext_coefficient(5, to_unsigned_representative(coefficients[5])) as u8;
            let coefficient7 =
                compress_ciphertext_coefficient(5, to_unsigned_representative(coefficients[6])) as u8;
            let coefficient8 =
                compress_ciphertext_coefficient(5, to_unsigned_representative(coefficients[7])) as u8;

            let (coef1, coef2, coef3, coef4, coef5) = compress_coefficients_5(
                coefficient2,
                coefficient1,
                coefficient4,
                coefficient3,
                coefficient5,
                coefficient7,
                coefficient6,
                coefficient8,
            );
            serialized[5 * i] = coef1;
            serialized[5 * i + 1] = coef2;
            serialized[5 * i + 2] = coef3;
            serialized[5 * i + 3] = coef4;
            serialized[5 * i + 4] = coef5;
        }
    }

    serialized
}

#[inline(always)]
fn compress_coefficients_5(
    coefficient2: u8,
    coefficient1: u8,
    coefficient4: u8,
    coefficient3: u8,
    coefficient5: u8,
    coefficient7: u8,
    coefficient6: u8,
    coefficient8: u8,
) -> (u8, u8, u8, u8, u8) {
    let coef1 = (coefficient2 & 0x7) << 5 | coefficient1;
    let coef2 = ((coefficient4 & 1) << 7) | (coefficient3 << 2) | (coefficient2 >> 3);
    let coef3 = ((coefficient5 & 0xF) << 4) | (coefficient4 >> 1);
    let coef4 = ((coefficient7 & 0x3) << 6) | (coefficient6 << 1) | (coefficient5 >> 4);
    let coef5 = (coefficient8 << 3) | (coefficient7 >> 2);
    (coef1, coef2, coef3, coef4, coef5)
}

#[inline(always)]
pub(super) fn compress_then_serialize_ring_element_v<
    const COMPRESSION_FACTOR: usize,
    const OUT_LEN: usize,
>(
    re: PolynomialRingElement,
) -> [u8; OUT_LEN] {
    hax_debug_assert!((COEFFICIENTS_IN_RING_ELEMENT * COMPRESSION_FACTOR) / 8 == OUT_LEN);

    match COMPRESSION_FACTOR as u32 {
        4 => compress_then_serialize_4(re),
        5 => compress_then_serialize_5(re),
        _ => unreachable!(),
    }
}

#[inline(always)]
fn deserialize_then_decompress_10(serialized: &[u8]) -> PolynomialRingElement {
    hax_debug_assert!(serialized.len() == (COEFFICIENTS_IN_RING_ELEMENT * 10) / 8);

    let mut re = PolynomialRingElement::ZERO;

    cloop! {
        for (i, bytes) in serialized.chunks_exact(5).enumerate() {
            let byte1 = bytes[0] as FieldElement;
            let byte2 = bytes[1] as FieldElement;
            let byte3 = bytes[2] as FieldElement;
            let byte4 = bytes[3] as FieldElement;
            let byte5 = bytes[4] as FieldElement;

            let (coefficient1, coefficient2, coefficient3, coefficient4) =
                decompress_coefficients_10(byte2, byte1, byte3, byte4, byte5);

            re.coefficients[4 * i] = decompress_ciphertext_coefficient(10, coefficient1);
            re.coefficients[4 * i + 1] = decompress_ciphertext_coefficient(10, coefficient2);
            re.coefficients[4 * i + 2] = decompress_ciphertext_coefficient(10, coefficient3);
            re.coefficients[4 * i + 3] = decompress_ciphertext_coefficient(10, coefficient4);
        }
    }

    re
}

#[inline(always)]
fn decompress_coefficients_10(
    byte2: i32,
    byte1: i32,
    byte3: i32,
    byte4: i32,
    byte5: i32,
) -> (i32, i32, i32, i32) {
    let coefficient1 = (byte2 & 0x03) << 8 | (byte1 & 0xFF);
    let coefficient2 = (byte3 & 0x0F) << 6 | (byte2 >> 2);
    let coefficient3 = (byte4 & 0x3F) << 4 | (byte3 >> 4);
    let coefficient4 = (byte5 << 2) | (byte4 >> 6);
    (coefficient1, coefficient2, coefficient3, coefficient4)
}

#[inline(always)]
fn deserialize_then_decompress_11(serialized: &[u8]) -> PolynomialRingElement {
    hax_debug_assert!(serialized.len() == (COEFFICIENTS_IN_RING_ELEMENT * 11) / 8);

    let mut re = PolynomialRingElement::ZERO;

    cloop! {
        for (i, bytes) in serialized.chunks_exact(11).enumerate() {
            let byte1 = bytes[0] as FieldElement;
            let byte2 = bytes[1] as FieldElement;
            let byte3 = bytes[2] as FieldElement;
            let byte4 = bytes[3] as FieldElement;
            let byte5 = bytes[4] as FieldElement;
            let byte6 = bytes[5] as FieldElement;
            let byte7 = bytes[6] as FieldElement;
            let byte8 = bytes[7] as FieldElement;
            let byte9 = bytes[8] as FieldElement;
            let byte10 = bytes[9] as FieldElement;
            let byte11 = bytes[10] as FieldElement;

            let (
                coefficient1,
                coefficient2,
                coefficient3,
                coefficient4,
                coefficient5,
                coefficient6,
                coefficient7,
                coefficient8,
            ) = decompress_coefficients_11(
                byte2, byte1, byte3, byte5, byte4, byte6, byte7, byte9, byte8, byte10, byte11,
            );

            re.coefficients[8 * i] = decompress_ciphertext_coefficient(11, coefficient1);
            re.coefficients[8 * i + 1] = decompress_ciphertext_coefficient(11, coefficient2);
            re.coefficients[8 * i + 2] = decompress_ciphertext_coefficient(11, coefficient3);
            re.coefficients[8 * i + 3] = decompress_ciphertext_coefficient(11, coefficient4);
            re.coefficients[8 * i + 4] = decompress_ciphertext_coefficient(11, coefficient5);
            re.coefficients[8 * i + 5] = decompress_ciphertext_coefficient(11, coefficient6);
            re.coefficients[8 * i + 6] = decompress_ciphertext_coefficient(11, coefficient7);
            re.coefficients[8 * i + 7] = decompress_ciphertext_coefficient(11, coefficient8);
        }
    }

    re
}

#[inline(always)]
fn decompress_coefficients_11(
    byte2: i32,
    byte1: i32,
    byte3: i32,
    byte5: i32,
    byte4: i32,
    byte6: i32,
    byte7: i32,
    byte9: i32,
    byte8: i32,
    byte10: i32,
    byte11: i32,
) -> (i32, i32, i32, i32, i32, i32, i32, i32) {
    let coefficient1 = (byte2 & 0x7) << 8 | byte1;
    let coefficient2 = (byte3 & 0x3F) << 5 | (byte2 >> 3);
    let coefficient3 = (byte5 & 0x1) << 10 | (byte4 << 2) | (byte3 >> 6);
    let coefficient4 = (byte6 & 0xF) << 7 | (byte5 >> 1);
    let coefficient5 = (byte7 & 0x7F) << 4 | (byte6 >> 4);
    let coefficient6 = (byte9 & 0x3) << 9 | (byte8 << 1) | (byte7 >> 7);
    let coefficient7 = (byte10 & 0x1F) << 6 | (byte9 >> 2);
    let coefficient8 = (byte11 << 3) | (byte10 >> 5);
    (
        coefficient1,
        coefficient2,
        coefficient3,
        coefficient4,
        coefficient5,
        coefficient6,
        coefficient7,
        coefficient8,
    )
}

#[inline(always)]
pub(super) fn deserialize_then_decompress_ring_element_u<const COMPRESSION_FACTOR: usize>(
    serialized: &[u8],
) -> PolynomialRingElement {
    hax_debug_assert!(serialized.len() == (COEFFICIENTS_IN_RING_ELEMENT * COMPRESSION_FACTOR) / 8);

    match COMPRESSION_FACTOR as u32 {
        10 => deserialize_then_decompress_10(serialized),
        11 => deserialize_then_decompress_11(serialized),
        _ => unreachable!(),
    }
}

#[inline(always)]
fn deserialize_then_decompress_4(serialized: &[u8]) -> PolynomialRingElement {
    hax_debug_assert!(serialized.len() == (COEFFICIENTS_IN_RING_ELEMENT * 4) / 8);

    let mut re = PolynomialRingElement::ZERO;

    cloop! {
        for (i, byte) in serialized.iter().enumerate() {
            let (coefficient1, coefficient2) = decompress_coefficients_4(byte);

            re.coefficients[2 * i] = decompress_ciphertext_coefficient(4, coefficient1);
            re.coefficients[2 * i + 1] = decompress_ciphertext_coefficient(4, coefficient2);
        }
    }

    re
}

#[inline(always)]
fn decompress_coefficients_4(byte: &u8) -> (i32, i32) {
    let coefficient1 = (byte & 0x0F) as FieldElement;
    let coefficient2 = ((byte >> 4) & 0x0F) as FieldElement;
    (coefficient1, coefficient2)
}

#[inline(always)]
fn deserialize_then_decompress_5(serialized: &[u8]) -> PolynomialRingElement {
    hax_debug_assert!(serialized.len() == (COEFFICIENTS_IN_RING_ELEMENT * 5) / 8);

    let mut re = PolynomialRingElement::ZERO;

    cloop! {
        for (i, bytes) in serialized.chunks_exact(5).enumerate() {
            let byte1 = bytes[0] as FieldElement;
            let byte2 = bytes[1] as FieldElement;
            let byte3 = bytes[2] as FieldElement;
            let byte4 = bytes[3] as FieldElement;
            let byte5 = bytes[4] as FieldElement;

            let (
                coefficient1,
                coefficient2,
                coefficient3,
                coefficient4,
                coefficient5,
                coefficient6,
                coefficient7,
                coefficient8,
            ) = decompress_coefficients_5(byte1, byte2, byte3, byte4, byte5);

            re.coefficients[8 * i] = decompress_ciphertext_coefficient(5, coefficient1);
            re.coefficients[8 * i + 1] = decompress_ciphertext_coefficient(5, coefficient2);
            re.coefficients[8 * i + 2] = decompress_ciphertext_coefficient(5, coefficient3);
            re.coefficients[8 * i + 3] = decompress_ciphertext_coefficient(5, coefficient4);
            re.coefficients[8 * i + 4] = decompress_ciphertext_coefficient(5, coefficient5);
            re.coefficients[8 * i + 5] = decompress_ciphertext_coefficient(5, coefficient6);
            re.coefficients[8 * i + 6] = decompress_ciphertext_coefficient(5, coefficient7);
            re.coefficients[8 * i + 7] = decompress_ciphertext_coefficient(5, coefficient8);
        }
    }

    re
}

#[inline(always)]
fn decompress_coefficients_5(
    byte1: i32,
    byte2: i32,
    byte3: i32,
    byte4: i32,
    byte5: i32,
) -> (i32, i32, i32, i32, i32, i32, i32, i32) {
    let coefficient1 = byte1 & 0x1F;
    let coefficient2 = (byte2 & 0x3) << 3 | (byte1 >> 5);
    let coefficient3 = (byte2 >> 2) & 0x1F;
    let coefficient4 = ((byte3 & 0xF) << 1) | (byte2 >> 7);
    let coefficient5 = ((byte4 & 1) << 4) | (byte3 >> 4);
    let coefficient6 = (byte4 >> 1) & 0x1F;
    let coefficient7 = ((byte5 & 0x7) << 2) | (byte4 >> 6);
    let coefficient8 = byte5 >> 3;
    (
        coefficient1,
        coefficient2,
        coefficient3,
        coefficient4,
        coefficient5,
        coefficient6,
        coefficient7,
        coefficient8,
    )
}

#[inline(always)]
pub(super) fn deserialize_then_decompress_ring_element_v<const COMPRESSION_FACTOR: usize>(
    serialized: &[u8],
) -> PolynomialRingElement {
    hax_debug_assert!(serialized.len() == (COEFFICIENTS_IN_RING_ELEMENT * COMPRESSION_FACTOR) / 8);

    match COMPRESSION_FACTOR as u32 {
        4 => deserialize_then_decompress_4(serialized),
        5 => deserialize_then_decompress_5(serialized),
        _ => unreachable!(),
    }
}
