use super::{
    arithmetic::{to_unsigned_representative, KyberFieldElement, KyberPolynomialRingElement},
    compress::{compress_q, decompress_q},
    constants::{BYTES_PER_RING_ELEMENT, COEFFICIENTS_IN_RING_ELEMENT, SHARED_SECRET_SIZE},
};

#[inline(always)]
pub(super) fn compress_then_serialize_message(
    re: KyberPolynomialRingElement,
) -> [u8; SHARED_SECRET_SIZE] {
    let mut serialized = [0u8; SHARED_SECRET_SIZE];

    for index in 0..(re.coefficients.len() / 8) {
        let i = index / 8;
        let j = index % 8;
        let coefficient = re.coefficients[index];
        let coefficient = to_unsigned_representative(coefficient);
        let coefficient_compressed = compress_q(1, coefficient);
        serialized[i] |= (coefficient_compressed as u8) << j
    }
    // for (i, coefficients) in re.coefficients.chunks_exact(8).enumerate() {
    // // for (i, coefficients) in re.coefficients.len()/8 {
    //     for (j, coefficient) in coefficients.iter().enumerate() {
    //         let coefficient = to_unsigned_representative(*coefficient);

    //         let coefficient_compressed = compress_q(1, coefficient);

    //         // At this point, the following should hold for |coefficient_compressed|:
    //         //
    //         // if coefficient_compressed == 0 {
    //         //     coefficient < 832 ||
    //         //     (coefficient >= 2496 && coefficient < 4161)
    //         // } else { // coefficient_compressed = 1
    //         //     (coefficient >= 832 && coefficient < 2496) ||
    //         //     (coefficient >= 4161 && coefficient < 5825)
    //         // }
    //         //
    //         // TODO(xvzcf): When this is turned into an assertion, intermittent
    //         // failures arise in the |modified_ciphertext| test. Figure out why.

    //         serialized[i] |= (coefficient_compressed as u8) << j
    //     }
    // }

    serialized
}
#[inline(always)]
pub(super) fn deserialize_then_decompress_message(
    serialized: [u8; SHARED_SECRET_SIZE],
) -> KyberPolynomialRingElement {
    let mut re = KyberPolynomialRingElement::ZERO;

    for i in 0..serialized.len() {
        let byte = serialized[i];
        for j in 0..8 {
            let coefficient_compressed = ((byte >> j) & 0x1) as KyberFieldElement;
            re.coefficients[8 * i + j] = decompress_q(1, coefficient_compressed);
        }
    }

    re
}

#[inline(always)]
pub(super) fn serialize_uncompressed_ring_element(
    re: KyberPolynomialRingElement,
) -> [u8; BYTES_PER_RING_ELEMENT] {
    let mut serialized = [0u8; BYTES_PER_RING_ELEMENT];

    for i in 0..re.coefficients.len() / 2 {
        // for (i, coefficients) in re.coefficients.chunks_exact(2).enumerate() {
        let coefficient1 = to_unsigned_representative(re.coefficients[i * 2 + 0]);
        let coefficient2 = to_unsigned_representative(re.coefficients[i * 2 + 1]);

        serialized[3 * i] = (coefficient1 & 0xFF) as u8;
        serialized[3 * i + 1] = ((coefficient1 >> 8) | ((coefficient2 & 0x0F) << 4)) as u8;
        serialized[3 * i + 2] = ((coefficient2 >> 4) & 0xFF) as u8;
    }

    serialized
}
#[inline(always)]
pub(super) fn deserialize_to_uncompressed_ring_element(
    serialized: &[u8],
) -> KyberPolynomialRingElement {
    hax_lib::debug_assert!(serialized.len() == BYTES_PER_RING_ELEMENT);

    let mut re = KyberPolynomialRingElement::ZERO;

    // for (i, bytes) in serialized.chunks_exact(3).enumerate() {
    for i in 0..serialized.len() / 3 {
        let byte1 = serialized[i * 3 + 0] as KyberFieldElement;
        let byte2 = serialized[i * 3 + 1] as KyberFieldElement;
        let byte3 = serialized[i * 3 + 2] as KyberFieldElement;

        re.coefficients[2 * i] = (byte2 & 0x0F) << 8 | (byte1 & 0xFF);
        re.coefficients[2 * i + 1] = (byte3 << 4) | ((byte2 >> 4) & 0x0F);
    }

    re
}

#[inline(always)]
fn compress_then_serialize_10<const OUT_LEN: usize>(
    re: KyberPolynomialRingElement,
) -> [u8; OUT_LEN] {
    let mut serialized = [0u8; OUT_LEN];

    // for (i, coefficients) in re.coefficients.chunks_exact(4).enumerate() {
    for i in 0..re.coefficients.len() / 4 {
        let coefficient1 = compress_q(10, to_unsigned_representative(re.coefficients[i * 4 + 0]));
        let coefficient2 = compress_q(10, to_unsigned_representative(re.coefficients[i * 4 + 1]));
        let coefficient3 = compress_q(10, to_unsigned_representative(re.coefficients[i * 4 + 2]));
        let coefficient4 = compress_q(10, to_unsigned_representative(re.coefficients[i * 4 + 3]));

        serialized[5 * i] = (coefficient1 & 0xFF) as u8;
        serialized[5 * i + 1] =
            ((coefficient2 & 0x3F) as u8) << 2 | ((coefficient1 >> 8) & 0x03) as u8;
        serialized[5 * i + 2] =
            ((coefficient3 & 0x0F) as u8) << 4 | ((coefficient2 >> 6) & 0x0F) as u8;
        serialized[5 * i + 3] =
            ((coefficient4 & 0x03) as u8) << 6 | ((coefficient3 >> 4) & 0x3F) as u8;
        serialized[5 * i + 4] = ((coefficient4 >> 2) & 0xFF) as u8;
    }

    serialized
}
#[inline(always)]
fn compress_then_serialize_11<const OUT_LEN: usize>(
    re: KyberPolynomialRingElement,
) -> [u8; OUT_LEN] {
    let mut serialized = [0u8; OUT_LEN];

    // for (i, coefficients) in re.coefficients.chunks_exact(8).enumerate() {
    for i in 0..re.coefficients.len() / 8 {
        let coefficient1 = compress_q(11, to_unsigned_representative(re.coefficients[i * 8 + 0]));
        let coefficient2 = compress_q(11, to_unsigned_representative(re.coefficients[i * 8 + 1]));
        let coefficient3 = compress_q(11, to_unsigned_representative(re.coefficients[i * 8 + 2]));
        let coefficient4 = compress_q(11, to_unsigned_representative(re.coefficients[i * 8 + 3]));
        let coefficient5 = compress_q(11, to_unsigned_representative(re.coefficients[i * 8 + 4]));
        let coefficient6 = compress_q(11, to_unsigned_representative(re.coefficients[i * 8 + 5]));
        let coefficient7 = compress_q(11, to_unsigned_representative(re.coefficients[i * 8 + 6]));
        let coefficient8 = compress_q(11, to_unsigned_representative(re.coefficients[i * 8 + 7]));

        serialized[11 * i] = coefficient1 as u8;
        serialized[11 * i + 1] = ((coefficient2 & 0x1F) as u8) << 3 | ((coefficient1 >> 8) as u8);
        serialized[11 * i + 2] = ((coefficient3 & 0x3) as u8) << 6 | ((coefficient2 >> 5) as u8);
        serialized[11 * i + 3] = ((coefficient3 >> 2) & 0xFF) as u8;
        serialized[11 * i + 4] = ((coefficient4 & 0x7F) as u8) << 1 | (coefficient3 >> 10) as u8;
        serialized[11 * i + 5] = ((coefficient5 & 0xF) as u8) << 4 | (coefficient4 >> 7) as u8;
        serialized[11 * i + 6] = ((coefficient6 & 0x1) as u8) << 7 | (coefficient5 >> 4) as u8;
        serialized[11 * i + 7] = ((coefficient6 >> 1) & 0xFF) as u8;
        serialized[11 * i + 8] = ((coefficient7 & 0x3F) as u8) << 2 | (coefficient6 >> 9) as u8;
        serialized[11 * i + 9] = ((coefficient8 & 0x7) as u8) << 5 | (coefficient7 >> 6) as u8;
        serialized[11 * i + 10] = (coefficient8 >> 3) as u8;
    }

    serialized
}
#[inline(always)]
pub(super) fn compress_then_serialize_ring_element_u<
    const COMPRESSION_FACTOR: usize,
    const OUT_LEN: usize,
>(
    re: KyberPolynomialRingElement,
) -> [u8; OUT_LEN] {
    hax_lib::debug_assert!((COEFFICIENTS_IN_RING_ELEMENT * COMPRESSION_FACTOR) / 8 == OUT_LEN);

    match COMPRESSION_FACTOR as u32 {
        10 => compress_then_serialize_10(re),
        11 => compress_then_serialize_11(re),
        _ => unreachable!(),
    }
}

#[inline(always)]
fn compress_then_serialize_4<const OUT_LEN: usize>(
    re: KyberPolynomialRingElement,
) -> [u8; OUT_LEN] {
    let mut serialized = [0u8; OUT_LEN];

    // for (i, coefficients) in re.coefficients.chunks_exact(2).enumerate() {
    for i in 0..re.coefficients.len() / 2 {
        let coefficient1 =
            compress_q(4, to_unsigned_representative(re.coefficients[i * 2 + 0])) as u8;
        let coefficient2 =
            compress_q(4, to_unsigned_representative(re.coefficients[i * 2 + 1])) as u8;

        serialized[i] = (coefficient2 << 4) | coefficient1;
    }

    serialized
}

#[inline(always)]
fn compress_then_serialize_5<const OUT_LEN: usize>(
    re: KyberPolynomialRingElement,
) -> [u8; OUT_LEN] {
    let mut serialized = [0u8; OUT_LEN];

    // for (i, coefficients) in re.coefficients.chunks_exact(8).enumerate() {
    for i in 0..re.coefficients.len() / 8 {
        let coefficient1 =
            compress_q(5, to_unsigned_representative(re.coefficients[i * 8 + 0])) as u8;
        let coefficient2 =
            compress_q(5, to_unsigned_representative(re.coefficients[i * 8 + 1])) as u8;
        let coefficient3 =
            compress_q(5, to_unsigned_representative(re.coefficients[i * 8 + 2])) as u8;
        let coefficient4 =
            compress_q(5, to_unsigned_representative(re.coefficients[i * 8 + 3])) as u8;
        let coefficient5 =
            compress_q(5, to_unsigned_representative(re.coefficients[i * 8 + 4])) as u8;
        let coefficient6 =
            compress_q(5, to_unsigned_representative(re.coefficients[i * 8 + 5])) as u8;
        let coefficient7 =
            compress_q(5, to_unsigned_representative(re.coefficients[i * 8 + 6])) as u8;
        let coefficient8 =
            compress_q(5, to_unsigned_representative(re.coefficients[i * 8 + 7])) as u8;

        serialized[5 * i] = (coefficient2 & 0x7) << 5 | coefficient1;
        serialized[5 * i + 1] =
            ((coefficient4 & 1) << 7) | (coefficient3 << 2) | (coefficient2 >> 3);
        serialized[5 * i + 2] = ((coefficient5 & 0xF) << 4) | (coefficient4 >> 1);
        serialized[5 * i + 3] =
            ((coefficient7 & 0x3) << 6) | (coefficient6 << 1) | (coefficient5 >> 4);
        serialized[5 * i + 4] = (coefficient8 << 3) | (coefficient7 >> 2);
    }

    serialized
}
#[inline(always)]
pub(super) fn compress_then_serialize_ring_element_v<
    const COMPRESSION_FACTOR: usize,
    const OUT_LEN: usize,
>(
    re: KyberPolynomialRingElement,
) -> [u8; OUT_LEN] {
    hax_lib::debug_assert!((COEFFICIENTS_IN_RING_ELEMENT * COMPRESSION_FACTOR) / 8 == OUT_LEN);

    match COMPRESSION_FACTOR as u32 {
        4 => compress_then_serialize_4(re),
        5 => compress_then_serialize_5(re),
        _ => unreachable!(),
    }
}

#[inline(always)]
fn deserialize_then_decompress_10(serialized: &[u8]) -> KyberPolynomialRingElement {
    hax_lib::debug_assert!(serialized.len() == (COEFFICIENTS_IN_RING_ELEMENT * 10) / 8);

    let mut re = KyberPolynomialRingElement::ZERO;

    // for (i, bytes) in serialized.chunks_exact(5).enumerate() {
    for i in 0..serialized.len() / 5 {
        let byte1 = serialized[i * 5 + 0] as KyberFieldElement;
        let byte2 = serialized[i * 5 + 1] as KyberFieldElement;
        let byte3 = serialized[i * 5 + 2] as KyberFieldElement;
        let byte4 = serialized[i * 5 + 3] as KyberFieldElement;
        let byte5 = serialized[i * 5 + 4] as KyberFieldElement;

        let coefficient1 = (byte2 & 0x03) << 8 | (byte1 & 0xFF);
        re.coefficients[4 * i] = decompress_q(10, coefficient1);

        let coefficient2 = (byte3 & 0x0F) << 6 | (byte2 >> 2);
        re.coefficients[4 * i + 1] = decompress_q(10, coefficient2);

        let coefficient3 = (byte4 & 0x3F) << 4 | (byte3 >> 4);
        re.coefficients[4 * i + 2] = decompress_q(10, coefficient3);

        let coefficient4 = (byte5 << 2) | (byte4 >> 6);
        re.coefficients[4 * i + 3] = decompress_q(10, coefficient4);
    }

    re
}
#[inline(always)]
fn deserialize_then_decompress_11(serialized: &[u8]) -> KyberPolynomialRingElement {
    hax_lib::debug_assert!(serialized.len() == (COEFFICIENTS_IN_RING_ELEMENT * 11) / 8);

    let mut re = KyberPolynomialRingElement::ZERO;

    // for (i, bytes) in serialized.chunks_exact(11).enumerate() {
    for i in 0..serialized.len() / 11 {
        let byte1 = serialized[i * 11 + 0] as KyberFieldElement;
        let byte2 = serialized[i * 11 + 1] as KyberFieldElement;
        let byte3 = serialized[i * 11 + 2] as KyberFieldElement;
        let byte4 = serialized[i * 11 + 3] as KyberFieldElement;
        let byte5 = serialized[i * 11 + 4] as KyberFieldElement;
        let byte6 = serialized[i * 11 + 5] as KyberFieldElement;
        let byte7 = serialized[i * 11 + 6] as KyberFieldElement;
        let byte8 = serialized[i * 11 + 7] as KyberFieldElement;
        let byte9 = serialized[i * 11 + 8] as KyberFieldElement;
        let byte10 = serialized[i * 11 + 9] as KyberFieldElement;
        let byte11 = serialized[i * 11 + 10] as KyberFieldElement;

        let coefficient1 = (byte2 & 0x7) << 8 | byte1;
        re.coefficients[8 * i] = decompress_q(11, coefficient1);

        let coefficient2 = (byte3 & 0x3F) << 5 | (byte2 >> 3);
        re.coefficients[8 * i + 1] = decompress_q(11, coefficient2);

        let coefficient3 = (byte5 & 0x1) << 10 | (byte4 << 2) | (byte3 >> 6);
        re.coefficients[8 * i + 2] = decompress_q(11, coefficient3);

        let coefficient4 = (byte6 & 0xF) << 7 | (byte5 >> 1);
        re.coefficients[8 * i + 3] = decompress_q(11, coefficient4);

        let coefficient5 = (byte7 & 0x7F) << 4 | (byte6 >> 4);
        re.coefficients[8 * i + 4] = decompress_q(11, coefficient5);

        let coefficient6 = (byte9 & 0x3) << 9 | (byte8 << 1) | (byte7 >> 7);
        re.coefficients[8 * i + 5] = decompress_q(11, coefficient6);

        let coefficient7 = (byte10 & 0x1F) << 6 | (byte9 >> 2);
        re.coefficients[8 * i + 6] = decompress_q(11, coefficient7);

        let coefficient8 = (byte11 << 3) | (byte10 >> 5);
        re.coefficients[8 * i + 7] = decompress_q(11, coefficient8);
    }

    re
}
#[inline(always)]
pub(super) fn deserialize_then_decompress_ring_element_u<const COMPRESSION_FACTOR: usize>(
    serialized: &[u8],
) -> KyberPolynomialRingElement {
    hax_lib::debug_assert!(
        serialized.len() == (COEFFICIENTS_IN_RING_ELEMENT * COMPRESSION_FACTOR) / 8
    );

    match COMPRESSION_FACTOR as u32 {
        10 => deserialize_then_decompress_10(serialized),
        11 => deserialize_then_decompress_11(serialized),
        _ => unreachable!(),
    }
}

#[inline(always)]
fn deserialize_then_decompress_4(serialized: &[u8]) -> KyberPolynomialRingElement {
    hax_lib::debug_assert!(serialized.len() == (COEFFICIENTS_IN_RING_ELEMENT * 4) / 8);

    let mut re = KyberPolynomialRingElement::ZERO;

    // for (i, byte) in serialized.iter().enumerate() {
    for i in 0..serialized.len() {
        let byte = serialized[i];
        let coefficient1 = (byte & 0x0F) as KyberFieldElement;
        re.coefficients[2 * i] = decompress_q(4, coefficient1);

        let coefficient2 = ((byte >> 4) & 0x0F) as KyberFieldElement;
        re.coefficients[2 * i + 1] = decompress_q(4, coefficient2);
    }

    re
}
#[inline(always)]
fn deserialize_then_decompress_5(serialized: &[u8]) -> KyberPolynomialRingElement {
    hax_lib::debug_assert!(serialized.len() == (COEFFICIENTS_IN_RING_ELEMENT * 5) / 8);

    let mut re = KyberPolynomialRingElement::ZERO;

    // for (i, bytes) in serialized.chunks_exact(5).enumerate() {
    for i in 0..serialized.len() / 5 {
        let byte1 = serialized[i * 5 + 0] as KyberFieldElement;
        let byte2 = serialized[i * 5 + 1] as KyberFieldElement;
        let byte3 = serialized[i * 5 + 2] as KyberFieldElement;
        let byte4 = serialized[i * 5 + 3] as KyberFieldElement;
        let byte5 = serialized[i * 5 + 4] as KyberFieldElement;

        let coefficient1 = byte1 & 0x1F;
        re.coefficients[8 * i] = decompress_q(5, coefficient1);

        let coefficient2 = (byte2 & 0x3) << 3 | (byte1 >> 5);
        re.coefficients[8 * i + 1] = decompress_q(5, coefficient2);

        let coefficient3 = (byte2 >> 2) & 0x1F;
        re.coefficients[8 * i + 2] = decompress_q(5, coefficient3);

        let coefficient4 = ((byte3 & 0xF) << 1) | (byte2 >> 7);
        re.coefficients[8 * i + 3] = decompress_q(5, coefficient4);

        let coefficient5 = ((byte4 & 1) << 4) | (byte3 >> 4);
        re.coefficients[8 * i + 4] = decompress_q(5, coefficient5);

        let coefficient6 = (byte4 >> 1) & 0x1F;
        re.coefficients[8 * i + 5] = decompress_q(5, coefficient6);

        let coefficient7 = ((byte5 & 0x7) << 2) | (byte4 >> 6);
        re.coefficients[8 * i + 6] = decompress_q(5, coefficient7);

        let coefficient8 = byte5 >> 3;
        re.coefficients[8 * i + 7] = decompress_q(5, coefficient8);
    }

    re
}
#[inline(always)]
pub(super) fn deserialize_then_decompress_ring_element_v<const COMPRESSION_FACTOR: usize>(
    serialized: &[u8],
) -> KyberPolynomialRingElement {
    hax_lib::debug_assert!(
        serialized.len() == (COEFFICIENTS_IN_RING_ELEMENT * COMPRESSION_FACTOR) / 8
    );

    match COMPRESSION_FACTOR as u32 {
        4 => deserialize_then_decompress_4(serialized),
        5 => deserialize_then_decompress_5(serialized),
        _ => unreachable!(),
    }
}
