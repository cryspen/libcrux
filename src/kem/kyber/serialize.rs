use super::{
    arithmetic::{KyberFieldElement, KyberPolynomialRingElement},
    constants::{BYTES_PER_RING_ELEMENT, COEFFICIENTS_IN_RING_ELEMENT},
    conversions::to_unsigned_representative,
};

/// This file contains instantiations of the functions
/// `serialize_little_endian_n` and `deserialize_little_endian_n` for
/// `|n| = 1, |n| = 4, |n| = 10, and |n| = 12`.
///
/// `serialize_little_endian_n` converts a ring element |re| into a vector of
/// `|COEFFICIENTS_IN_RING_ELEMENT| * |n|` bits, and outputs this vector as a
/// byte array such that the first 8 bits of the vector represent the first byte
/// of the output, the next 8 bits the next byte of the output, and so on ...
///
/// `deserialize_little_endian_n` on the other hand, given a series of bytes
/// representing a ring element in `|serialized|`, first converts them into
/// a vector of bits in little-endian order; i.e. the least significant `|n|` of
/// `|serialized[0]|` are the first set of bits in the bitstream. This vector is
/// then deserialized into a KyberPolynomialRingElement structure. The first
/// `|n|` bits are used to re-construct the first coefficient of the ring element,
/// the second `|n|` the second coefficient, and so on.
///
/// N.B.: `serialize_little_endian_n` is the inverse of `deserialize_little_endian_n`
/// only when:
///
/// - each ring coefficient can fit into |n| bits (otherwise
///   lossy compression takes place)
/// - `|n| < |parameters::BITS_PER_COEFFICIENT|`, since
///   otherwise when `deserialize_little_endian` operates on 12 bits at a time,
///   it is not injective: the values 3329 + 1 and 1 for example both fit into
///   12 bits and map to the same `KyberFieldElement`
///
/// Otherwise `deserialize_little_endian` is not injective and therefore has
/// no left inverse.
///
/// N.B.: All the `serialize_little_endian_{n}` functions work on the canonical
/// unsigned representative of each coefficient in the polynomial ring.
/// Only `serialize_little_endian_12` actually performs this conversion in the
/// function itself; the rest don't since they are called only after `compress_q`
/// is called, and `compress_q` also performs this conversion.

#[inline(always)]
pub(super) fn serialize_little_endian<const COMPRESSION_FACTOR: usize, const OUT_LEN: usize>(
    re: KyberPolynomialRingElement,
) -> [u8; OUT_LEN] {
    debug_assert!(
        (COEFFICIENTS_IN_RING_ELEMENT * COMPRESSION_FACTOR) / 8 == OUT_LEN,
        "{} != {}",
        (COEFFICIENTS_IN_RING_ELEMENT * COMPRESSION_FACTOR) / 8,
        OUT_LEN
    );

    match COMPRESSION_FACTOR {
        1 => serialize_little_endian_1(re),
        // VECTOR_V_COMPRESSION_FACTOR_768 & VECTOR_V_COMPRESSION_FACTOR_512
        4 => serialize_little_endian_4(re),
        // VECTOR_V_COMPRESSION_FACTOR_1024
        5 => serialize_little_endian_5(re),
        // VECTOR_U_COMPRESSION_FACTOR_768 & VECTOR_U_COMPRESSION_FACTOR_512
        10 => serialize_little_endian_10(re),
        // VECTOR_U_COMPRESSION_FACTOR_1024
        11 => serialize_little_endian_11(re),
        12 => serialize_little_endian_12(re),
        _ => unreachable!("factor {COMPRESSION_FACTOR}"),
    }
}

#[inline(always)]
pub(super) fn deserialize_little_endian<const COMPRESSION_FACTOR: usize>(
    serialized: &[u8],
) -> KyberPolynomialRingElement {
    debug_assert_eq!(
        serialized.len(),
        (COEFFICIENTS_IN_RING_ELEMENT * COMPRESSION_FACTOR) / 8
    );

    match COMPRESSION_FACTOR {
        1 => deserialize_little_endian_1(serialized),
        // VECTOR_V_COMPRESSION_FACTOR_768 & VECTOR_V_COMPRESSION_FACTOR_512
        4 => deserialize_little_endian_4(serialized),
        // VECTOR_V_COMPRESSION_FACTOR_1024
        5 => deserialize_little_endian_5(serialized),
        // VECTOR_U_COMPRESSION_FACTOR_768 & VECTOR_U_COMPRESSION_FACTOR_512
        10 => deserialize_little_endian_10(serialized),
        // VECTOR_U_COMPRESSION_FACTOR_1024
        11 => deserialize_little_endian_11(serialized),
        12 => deserialize_little_endian_12(serialized),
        _ => unreachable!("factor {COMPRESSION_FACTOR}"),
    }
}

#[inline(always)]
fn serialize_little_endian_1<const OUT_LEN: usize>(
    re: KyberPolynomialRingElement,
) -> [u8; OUT_LEN] {
    let mut serialized = [0u8; OUT_LEN];

    for (i, chunk) in re.coefficients.chunks_exact(8).enumerate() {
        for (j, coefficient) in chunk.iter().enumerate() {
            serialized[i] |= (*coefficient as u8) << j
        }
    }

    serialized
}

#[inline(always)]
fn deserialize_little_endian_1(serialized: &[u8]) -> KyberPolynomialRingElement {
    debug_assert_eq!(serialized.len(), COEFFICIENTS_IN_RING_ELEMENT / 8);

    let mut re = KyberPolynomialRingElement::ZERO;

    for (i, byte) in serialized.iter().enumerate() {
        for j in 0..8 {
            re.coefficients[8 * i + j] = ((byte >> j) & 0x1) as KyberFieldElement;
        }
    }

    re
}

#[inline(always)]
fn serialize_little_endian_4<const OUT_LEN: usize>(
    re: KyberPolynomialRingElement,
) -> [u8; OUT_LEN] {
    let mut serialized = [0u8; OUT_LEN];

    for (i, chunk) in re.coefficients.chunks_exact(2).enumerate() {
        let coefficient1 = chunk[0] as u8;
        let coefficient2 = chunk[1] as u8;

        serialized[i] = (coefficient2 << 4) | coefficient1;
    }

    serialized
}

#[inline(always)]
fn deserialize_little_endian_4(serialized: &[u8]) -> KyberPolynomialRingElement {
    debug_assert_eq!(serialized.len(), (COEFFICIENTS_IN_RING_ELEMENT * 4) / 8);

    let mut re = KyberPolynomialRingElement::ZERO;

    for (i, byte) in serialized.iter().enumerate() {
        re.coefficients[2 * i] = (byte & 0x0F) as KyberFieldElement;
        re.coefficients[2 * i + 1] = ((byte >> 4) & 0x0F) as KyberFieldElement;
    }

    re
}

// FIXME make this correct for 5
#[inline(always)]
fn serialize_little_endian_5<const OUT_LEN: usize>(
    re: KyberPolynomialRingElement,
) -> [u8; OUT_LEN] {
    let mut serialized = [0u8; OUT_LEN];

    for (i, chunk) in re.coefficients.chunks_exact(2).enumerate() {
        let coefficient1 = chunk[0] as u8;
        let coefficient2 = chunk[1] as u8;

        serialized[i] = (coefficient2 << 4) | coefficient1;
    }

    serialized
}

// FIXME make this correct for 5
#[inline(always)]
fn deserialize_little_endian_5(serialized: &[u8]) -> KyberPolynomialRingElement {
    debug_assert_eq!(serialized.len(), (COEFFICIENTS_IN_RING_ELEMENT * 5) / 8);

    let mut re = KyberPolynomialRingElement::ZERO;

    for (i, byte) in serialized.iter().enumerate() {
        re.coefficients[2 * i] = (byte & 0x0F) as KyberFieldElement;
        re.coefficients[2 * i + 1] = ((byte >> 4) & 0x0F) as KyberFieldElement;
    }

    re
}

#[inline(always)]
fn serialize_little_endian_10<const OUT_LEN: usize>(
    re: KyberPolynomialRingElement,
) -> [u8; OUT_LEN] {
    let mut serialized = [0u8; OUT_LEN];

    for (i, chunk) in re.coefficients.chunks_exact(4).enumerate() {
        let coefficient1 = chunk[0];
        let coefficient2 = chunk[1];
        let coefficient3 = chunk[2];
        let coefficient4 = chunk[3];

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
fn deserialize_little_endian_10(serialized: &[u8]) -> KyberPolynomialRingElement {
    debug_assert_eq!(serialized.len(), (COEFFICIENTS_IN_RING_ELEMENT * 10) / 8);

    let mut re = KyberPolynomialRingElement::ZERO;

    for (i, bytes) in serialized.chunks(5).enumerate() {
        let byte1 = bytes[0] as KyberFieldElement;
        let byte2 = bytes[1] as KyberFieldElement;
        let byte3 = bytes[2] as KyberFieldElement;
        let byte4 = bytes[3] as KyberFieldElement;
        let byte5 = bytes[4] as KyberFieldElement;

        re.coefficients[4 * i] = (byte2 & 0x03) << 8 | (byte1 & 0xFF);
        re.coefficients[4 * i + 1] = (byte3 & 0x0F) << 6 | (byte2 >> 2);
        re.coefficients[4 * i + 2] = (byte4 & 0x3F) << 4 | (byte3 >> 4);
        re.coefficients[4 * i + 3] = byte5 << 2 | (byte4 >> 6);
    }

    re
}

// FIXME make this correct for 11
#[inline(always)]
fn serialize_little_endian_11<const OUT_LEN: usize>(
    re: KyberPolynomialRingElement,
) -> [u8; OUT_LEN] {
    let mut serialized = [0u8; OUT_LEN];

    for (i, chunk) in re.coefficients.chunks_exact(4).enumerate() {
        let coefficient1 = chunk[0];
        let coefficient2 = chunk[1];
        let coefficient3 = chunk[2];
        let coefficient4 = chunk[3];

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

// FIXME make this correct for 11
#[inline(always)]
fn deserialize_little_endian_11(serialized: &[u8]) -> KyberPolynomialRingElement {
    debug_assert_eq!(serialized.len(), (COEFFICIENTS_IN_RING_ELEMENT * 11) / 8);

    let mut re = KyberPolynomialRingElement::ZERO;

    for (i, bytes) in serialized.chunks(5).enumerate() {
        let byte1 = bytes[0] as KyberFieldElement;
        let byte2 = bytes[1] as KyberFieldElement;
        let byte3 = bytes[2] as KyberFieldElement;
        let byte4 = bytes[3] as KyberFieldElement;
        let byte5 = bytes[4] as KyberFieldElement;

        re.coefficients[4 * i] = (byte2 & 0x03) << 8 | (byte1 & 0xFF);
        re.coefficients[4 * i + 1] = (byte3 & 0x0F) << 6 | (byte2 >> 2);
        re.coefficients[4 * i + 2] = (byte4 & 0x3F) << 4 | (byte3 >> 4);
        re.coefficients[4 * i + 3] = byte5 << 2 | (byte4 >> 6);
    }

    re
}

#[inline(always)]
fn serialize_little_endian_12<const OUT_LEN: usize>(
    re: KyberPolynomialRingElement,
) -> [u8; OUT_LEN] {
    let mut serialized = [0u8; OUT_LEN];

    for (i, chunks) in re.coefficients.chunks_exact(2).enumerate() {
        let coefficient1 = to_unsigned_representative(chunks[0]);
        let coefficient2 = to_unsigned_representative(chunks[1]);

        serialized[3 * i] = (coefficient1 & 0xFF) as u8;
        serialized[3 * i + 1] = ((coefficient1 >> 8) | ((coefficient2 & 0xF) << 4)) as u8;
        serialized[3 * i + 2] = ((coefficient2 >> 4) & 0xFF) as u8;
    }

    serialized
}

#[inline(always)]
fn deserialize_little_endian_12(serialized: &[u8]) -> KyberPolynomialRingElement {
    debug_assert_eq!(serialized.len(), BYTES_PER_RING_ELEMENT);

    let mut re = KyberPolynomialRingElement::ZERO;

    for (i, bytes) in serialized.chunks_exact(3).enumerate() {
        let byte1 = bytes[0] as KyberFieldElement;
        let byte2 = bytes[1] as KyberFieldElement;
        let byte3 = bytes[2] as KyberFieldElement;

        re.coefficients[2 * i] = (byte2 & 0x0F) << 8 | (byte1 & 0xFF);
        re.coefficients[2 * i + 1] = (byte3 << 4) | ((byte2 >> 4) & 0x0F);
    }

    re
}
