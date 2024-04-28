use crate::{
    constants::{BYTES_PER_RING_ELEMENT, SHARED_SECRET_SIZE},
    hax_utils::hax_debug_assert,
    helper::cloop,
    polynomial::{PolynomialRingElement, VECTORS_IN_RING_ELEMENT},
    simd::{self, simd_trait::*},
};

#[cfg(hax)]
use super::constants::COEFFICIENTS_IN_RING_ELEMENT;

#[inline(always)]
pub(super) fn compress_then_serialize_message(
    re: PolynomialRingElement,
) -> [u8; SHARED_SECRET_SIZE] {
    let mut serialized = [0u8; SHARED_SECRET_SIZE];
    for i in 0..32 {
        let coefficient = simd::Vector::to_unsigned_representative(re.coefficients[i]);
        let coefficient_compressed = simd::Vector::compress_1(coefficient);
        serialized[i] = simd::Vector::serialize_1(coefficient_compressed);
    }
    serialized
}
#[inline(always)]
pub(super) fn deserialize_then_decompress_message(
    serialized: [u8; SHARED_SECRET_SIZE],
) -> PolynomialRingElement {
    let mut re = PolynomialRingElement::ZERO();
    for i in 0..32 {
        let coefficient_compressed = simd::Vector::deserialize_1(serialized[i]);
        re.coefficients[i] = simd::Vector::decompress_1(coefficient_compressed);
    }
    re
}

#[inline(always)]
pub(super) fn serialize_uncompressed_ring_element(
    re: PolynomialRingElement,
) -> [u8; BYTES_PER_RING_ELEMENT] {
    let mut serialized = [0u8; BYTES_PER_RING_ELEMENT];
    for i in 0..VECTORS_IN_RING_ELEMENT {
        let coefficient = simd::Vector::to_unsigned_representative(re.coefficients[i]);
        let bytes = simd::Vector::serialize_12(coefficient);
        serialized[12 * i] = bytes[0];
        serialized[12 * i + 1] = bytes[1];
        serialized[12 * i + 2] = bytes[2];
        serialized[12 * i + 3] = bytes[3];
        serialized[12 * i + 4] = bytes[4];
        serialized[12 * i + 5] = bytes[5];
        serialized[12 * i + 6] = bytes[6];
        serialized[12 * i + 7] = bytes[7];
        serialized[12 * i + 8] = bytes[8];
        serialized[12 * i + 9] = bytes[9];
        serialized[12 * i + 10] = bytes[10];
        serialized[12 * i + 11] = bytes[11];
    }
    serialized
}

#[inline(always)]
pub(super) fn deserialize_to_uncompressed_ring_element(serialized: &[u8]) -> PolynomialRingElement {
    hax_debug_assert!(serialized.len() == BYTES_PER_RING_ELEMENT);

    let mut re = PolynomialRingElement::ZERO();

    cloop! {
        for (i, bytes) in serialized.chunks_exact(12).enumerate() {
            re.coefficients[i] = simd::Vector::deserialize_12(&bytes);
        }
    }

    re
}

/// Only use with public values.
///
/// This MUST NOT be used with secret inputs, like its caller `deserialize_ring_elements_reduced`.
#[inline(always)]
fn deserialize_to_reduced_ring_element(serialized: &[u8]) -> PolynomialRingElement {
    hax_debug_assert!(serialized.len() == BYTES_PER_RING_ELEMENT);

    let mut re = PolynomialRingElement::ZERO();

    cloop! {
        for (i, bytes) in serialized.chunks_exact(12).enumerate() {
            let coefficient = simd::Vector::deserialize_12(&bytes);
            re.coefficients[i] = simd::Vector::cond_subtract_3329(coefficient);
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
    let mut deserialized_pk = [PolynomialRingElement::ZERO(); K];
    cloop! {
        for (i, ring_element) in public_key
            .chunks_exact(BYTES_PER_RING_ELEMENT)
            .enumerate()
        {
            deserialized_pk[i] = deserialize_to_reduced_ring_element(ring_element);
        }
    }
    deserialized_pk
}

#[inline(always)]
fn compress_then_serialize_10<const OUT_LEN: usize>(re: PolynomialRingElement) -> [u8; OUT_LEN] {
    let mut serialized = [0u8; OUT_LEN];
    for i in 0..VECTORS_IN_RING_ELEMENT {
        let coefficient = simd::Vector::compress::<10>(simd::Vector::to_unsigned_representative(
            re.coefficients[i],
        ));
        let bytes = simd::Vector::serialize_10(coefficient);
        serialized[10 * i] = bytes[0];
        serialized[10 * i + 1] = bytes[1];
        serialized[10 * i + 2] = bytes[2];
        serialized[10 * i + 3] = bytes[3];
        serialized[10 * i + 4] = bytes[4];
        serialized[10 * i + 5] = bytes[5];
        serialized[10 * i + 6] = bytes[6];
        serialized[10 * i + 7] = bytes[7];
        serialized[10 * i + 8] = bytes[8];
        serialized[10 * i + 9] = bytes[9];
    }
    serialized
}

#[inline(always)]
fn compress_then_serialize_11<const OUT_LEN: usize>(re: PolynomialRingElement) -> [u8; OUT_LEN] {
    let mut serialized = [0u8; OUT_LEN];
    for i in 0..VECTORS_IN_RING_ELEMENT {
        let coefficient = simd::Vector::compress::<11>(simd::Vector::to_unsigned_representative(
            re.coefficients[i],
        ));
        let bytes = simd::Vector::serialize_11(coefficient);
        serialized[11 * i] = bytes[0];
        serialized[11 * i + 1] = bytes[1];
        serialized[11 * i + 2] = bytes[2];
        serialized[11 * i + 3] = bytes[3];
        serialized[11 * i + 4] = bytes[4];
        serialized[11 * i + 5] = bytes[5];
        serialized[11 * i + 6] = bytes[6];
        serialized[11 * i + 7] = bytes[7];
        serialized[11 * i + 8] = bytes[8];
        serialized[11 * i + 9] = bytes[9];
        serialized[11 * i + 10] = bytes[10];
    }
    serialized
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
    for i in 0..VECTORS_IN_RING_ELEMENT {
        let coefficient = simd::Vector::compress::<4>(simd::Vector::to_unsigned_representative(
            re.coefficients[i],
        ));
        let bytes = simd::Vector::serialize_4(coefficient);
        serialized[4 * i] = bytes[0];
        serialized[4 * i + 1] = bytes[1];
        serialized[4 * i + 2] = bytes[2];
        serialized[4 * i + 3] = bytes[3];
    }
    serialized
}

#[inline(always)]
fn compress_then_serialize_5<const OUT_LEN: usize>(re: PolynomialRingElement) -> [u8; OUT_LEN] {
    let mut serialized = [0u8; OUT_LEN];

    for i in 0..VECTORS_IN_RING_ELEMENT {
        let coefficients = simd::Vector::compress::<5>(simd::Vector::to_unsigned_representative(
            re.coefficients[i],
        ));
        let bytes5 = simd::Vector::serialize_5(coefficients);
        serialized[5 * i] = bytes5[0];
        serialized[5 * i + 1] = bytes5[1];
        serialized[5 * i + 2] = bytes5[2];
        serialized[5 * i + 3] = bytes5[3];
        serialized[5 * i + 4] = bytes5[4];
    }
    serialized
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

    let mut re = PolynomialRingElement::ZERO();

    cloop! {
        for (i, bytes) in serialized.chunks_exact(10).enumerate() {
            let coefficient = simd::Vector::deserialize_10(&bytes);
            re.coefficients[i] = simd::Vector::decompress::<10>(coefficient);
        }
    }
    re
}

#[inline(always)]
fn deserialize_then_decompress_11(serialized: &[u8]) -> PolynomialRingElement {
    hax_debug_assert!(serialized.len() == (COEFFICIENTS_IN_RING_ELEMENT * 11) / 8);

    let mut re = PolynomialRingElement::ZERO();

    cloop! {
        for (i, bytes) in serialized.chunks_exact(11).enumerate() {
            let coefficient = simd::Vector::deserialize_11(&bytes);
            re.coefficients[i] = simd::Vector::decompress::<11>(coefficient);
        }
    }

    re
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
    let mut re = PolynomialRingElement::ZERO();
    cloop! {
        for (i, bytes) in serialized.chunks_exact(4).enumerate() {
            let coefficient = simd::Vector::deserialize_4(&bytes);
            re.coefficients[i] = simd::Vector::decompress::<4>(coefficient);
        }
    }
    re
}

#[inline(always)]
fn deserialize_then_decompress_5(serialized: &[u8]) -> PolynomialRingElement {
    hax_debug_assert!(serialized.len() == (COEFFICIENTS_IN_RING_ELEMENT * 5) / 8);

    let mut re = PolynomialRingElement::ZERO();

    cloop! {
        for (i, bytes) in serialized.chunks_exact(5).enumerate() {
            re.coefficients[i] = simd::Vector::deserialize_5(&bytes);
            re.coefficients[i] = simd::Vector::decompress::<5>(re.coefficients[i]);
        }
    }
    re
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
