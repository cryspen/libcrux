use crate::{
    constants::{COEFFICIENTS_IN_RING_ELEMENT, BYTES_PER_RING_ELEMENT, SHARED_SECRET_SIZE},
    helper::cloop,
    polynomial::{PolynomialRingElement, VECTORS_IN_RING_ELEMENT},
    vector::{decompress_1, to_unsigned_representative, Operations},
};

#[inline(always)]
pub(super) fn compress_then_serialize_message<Vector: Operations>(
    re: PolynomialRingElement<Vector>,
) -> [u8; SHARED_SECRET_SIZE] {
    let mut serialized = [0u8; SHARED_SECRET_SIZE];
    for i in 0..16 {
        let coefficient = to_unsigned_representative::<Vector>(re.coefficients[i]);
        let coefficient_compressed = Vector::compress_1(coefficient);

        let bytes = Vector::serialize_1(coefficient_compressed);
        serialized[2 * i..2 * i + 2].copy_from_slice(&bytes);
    }

    serialized
}
#[inline(always)]
pub(super) fn deserialize_then_decompress_message<Vector: Operations>(
    serialized: [u8; SHARED_SECRET_SIZE],
) -> PolynomialRingElement<Vector> {
    let mut re = PolynomialRingElement::<Vector>::ZERO();
    for i in 0..16 {
        let coefficient_compressed = Vector::deserialize_1(&serialized[2 * i..2 * i + 2]);
        re.coefficients[i] = decompress_1::<Vector>(coefficient_compressed);
    }
    re
}

#[inline(always)]
pub(super) fn serialize_uncompressed_ring_element<Vector: Operations>(
    re: &PolynomialRingElement<Vector>,
) -> [u8; BYTES_PER_RING_ELEMENT] {
    let mut serialized = [0u8; BYTES_PER_RING_ELEMENT];
    for i in 0..VECTORS_IN_RING_ELEMENT {
        let coefficient = to_unsigned_representative::<Vector>(re.coefficients[i]);

        let bytes = Vector::serialize_12(coefficient);
        serialized[24 * i..24 * i + 24].copy_from_slice(&bytes);
    }
    serialized
}

#[inline(always)]
#[hax_lib::requires(
    serialized.len() == BYTES_PER_RING_ELEMENT
)]
pub(super) fn deserialize_to_uncompressed_ring_element<Vector: Operations>(
    serialized: &[u8],
) -> PolynomialRingElement<Vector> {
    hax_lib::fstar!("assert (v $BYTES_PER_RING_ELEMENT / 24 == 16)");
    let mut re = PolynomialRingElement::<Vector>::ZERO();

    cloop! {
        for (i, bytes) in serialized.chunks_exact(24).enumerate() {
            re.coefficients[i] = Vector::deserialize_12(bytes);
        }
    }

    re
}

/// Only use with public values.
///
/// This MUST NOT be used with secret inputs, like its caller `deserialize_ring_elements_reduced`.
#[inline(always)]
#[hax_lib::requires(
    serialized.len() == BYTES_PER_RING_ELEMENT
)]
fn deserialize_to_reduced_ring_element<Vector: Operations>(
    serialized: &[u8],
) -> PolynomialRingElement<Vector> {
    hax_lib::fstar!("assert (v $BYTES_PER_RING_ELEMENT / 24 == 16)");
    let mut re = PolynomialRingElement::<Vector>::ZERO();

    cloop! {
        for (i, bytes) in serialized.chunks_exact(24).enumerate() {
            let coefficient = Vector::deserialize_12(bytes);
            re.coefficients[i] = Vector::cond_subtract_3329(coefficient);
        }
    }
    re
}

/// This function deserializes ring elements and reduces the result by the field
/// modulus.
///
/// This function MUST NOT be used on secret inputs.
#[inline(always)]
#[hax_lib::requires(
    public_key.len() == PUBLIC_KEY_SIZE &&
    PUBLIC_KEY_SIZE / BYTES_PER_RING_ELEMENT <= K
)]
pub(super) fn deserialize_ring_elements_reduced<
    const PUBLIC_KEY_SIZE: usize,
    const K: usize,
    Vector: Operations,
>(
    public_key: &[u8],
) -> [PolynomialRingElement<Vector>; K] {
    let mut deserialized_pk = core::array::from_fn(|_i| PolynomialRingElement::<Vector>::ZERO());
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
#[hax_lib::requires(
    20 * (VECTORS_IN_RING_ELEMENT - 1) + 20 <= OUT_LEN
)]
fn compress_then_serialize_10<const OUT_LEN: usize, Vector: Operations>(
    re: &PolynomialRingElement<Vector>,
) -> [u8; OUT_LEN] {
    let mut serialized = [0u8; OUT_LEN];
    for i in 0..VECTORS_IN_RING_ELEMENT {
        let coefficient =
            Vector::compress::<10>(to_unsigned_representative::<Vector>(re.coefficients[i]));

        let bytes = Vector::serialize_10(coefficient);
        serialized[20 * i..20 * i + 20].copy_from_slice(&bytes);
    }
    serialized
}

#[inline(always)]
#[hax_lib::requires(
    22 * (VECTORS_IN_RING_ELEMENT - 1) + 22 <= OUT_LEN
)]
fn compress_then_serialize_11<const OUT_LEN: usize, Vector: Operations>(
    re: &PolynomialRingElement<Vector>,
) -> [u8; OUT_LEN] {
    let mut serialized = [0u8; OUT_LEN];
    for i in 0..VECTORS_IN_RING_ELEMENT {
        let coefficient =
            Vector::compress::<11>(to_unsigned_representative::<Vector>(re.coefficients[i]));

        let bytes = Vector::serialize_11(coefficient);
        serialized[22 * i..22 * i + 22].copy_from_slice(&bytes);
    }
    serialized
}

#[inline(always)]
#[hax_lib::requires(
    (COMPRESSION_FACTOR == 10 || COMPRESSION_FACTOR == 11) &&
    (COEFFICIENTS_IN_RING_ELEMENT * COMPRESSION_FACTOR) / 8 == OUT_LEN
)]
pub(super) fn compress_then_serialize_ring_element_u<
    const COMPRESSION_FACTOR: usize,
    const OUT_LEN: usize,
    Vector: Operations,
>(
    re: &PolynomialRingElement<Vector>,
) -> [u8; OUT_LEN] {
    hax_lib::fstar!("assert (
        (v (cast $COMPRESSION_FACTOR <: u32) == 10) \\/
        (v (cast $COMPRESSION_FACTOR <: u32) == 11))");
    match COMPRESSION_FACTOR as u32 {
        10 => compress_then_serialize_10(re),
        11 => compress_then_serialize_11(re),
        _ => unreachable!(),
    }
}

#[inline(always)]
#[hax_lib::requires(
    8 * (VECTORS_IN_RING_ELEMENT - 1) + 8 <= serialized.len()
)]
fn compress_then_serialize_4<Vector: Operations>(
    re: PolynomialRingElement<Vector>,
    serialized: &mut [u8],
) {
    let _serialized_len = serialized.len();
    // The semicolon and parentheses at the end of loop are a workaround
    // for the following bug https://github.com/hacspec/hax/issues/720
    for i in 0..VECTORS_IN_RING_ELEMENT {
        hax_lib::loop_invariant!(|i: usize| serialized.len() == _serialized_len);
        let coefficient =
            Vector::compress::<4>(to_unsigned_representative::<Vector>(re.coefficients[i]));

        let bytes = Vector::serialize_4(coefficient);
        serialized[8 * i..8 * i + 8].copy_from_slice(&bytes);
    }
    ()
}

#[inline(always)]
#[hax_lib::requires(
    10 * (VECTORS_IN_RING_ELEMENT - 1) + 10 <= serialized.len()
)]
fn compress_then_serialize_5<Vector: Operations>(
    re: PolynomialRingElement<Vector>,
    serialized: &mut [u8],
) {
    let _serialized_len = serialized.len();
    // The semicolon and parentheses at the end of loop are a workaround
    // for the following bug https://github.com/hacspec/hax/issues/720
    for i in 0..VECTORS_IN_RING_ELEMENT {
        hax_lib::loop_invariant!(|i: usize| serialized.len() == _serialized_len);
        let coefficients =
            Vector::compress::<5>(to_unsigned_representative::<Vector>(re.coefficients[i]));

        let bytes = Vector::serialize_5(coefficients);
        serialized[10 * i..10 * i + 10].copy_from_slice(&bytes);
    }
    ()
}

#[inline(always)]
#[hax_lib::requires(
    (COMPRESSION_FACTOR == 4 || COMPRESSION_FACTOR == 5) &&
    (COEFFICIENTS_IN_RING_ELEMENT * COMPRESSION_FACTOR) / 8 == OUT_LEN &&
    out.len() == OUT_LEN
)]
#[hax_lib::ensures(|_|
    fstar!("${out_future.len()} == ${out.len()}")
)]
pub(super) fn compress_then_serialize_ring_element_v<
    const COMPRESSION_FACTOR: usize,
    const OUT_LEN: usize,
    Vector: Operations,
>(
    re: PolynomialRingElement<Vector>,
    out: &mut [u8],
) {
    hax_lib::fstar!("assert (
        (v (cast $COMPRESSION_FACTOR <: u32) == 4) \\/
        (v (cast $COMPRESSION_FACTOR <: u32) == 5))");
    match COMPRESSION_FACTOR as u32 {
        4 => compress_then_serialize_4(re, out),
        5 => compress_then_serialize_5(re, out),
        _ => unreachable!(),
    }
}

#[inline(always)]
#[hax_lib::requires(
    serialized.len() == (COEFFICIENTS_IN_RING_ELEMENT * 10) / 8
)]
fn deserialize_then_decompress_10<Vector: Operations>(
    serialized: &[u8],
) -> PolynomialRingElement<Vector> {
    hax_lib::fstar!("assert (v (($COEFFICIENTS_IN_RING_ELEMENT *! sz 10) /! sz 8) == 320)");
    let mut re = PolynomialRingElement::<Vector>::ZERO();

    let _coefficients_length = re.coefficients.len();
    cloop! {
        for (i, bytes) in serialized.chunks_exact(20).enumerate() {
            hax_lib::loop_invariant!(|i: usize| i <= 16);
            let coefficient = Vector::deserialize_10(bytes);
            re.coefficients[i] = Vector::decompress_ciphertext_coefficient::<10>(coefficient);
        }
    }
    re
}

#[inline(always)]
#[hax_lib::requires(
    serialized.len() == (COEFFICIENTS_IN_RING_ELEMENT * 11) / 8
)]
fn deserialize_then_decompress_11<Vector: Operations>(
    serialized: &[u8],
) -> PolynomialRingElement<Vector> {
    hax_lib::fstar!("assert (v (($COEFFICIENTS_IN_RING_ELEMENT *! sz 11) /! sz 8) == 352)");
    let mut re = PolynomialRingElement::<Vector>::ZERO();

    cloop! {
        for (i, bytes) in serialized.chunks_exact(22).enumerate() {
            hax_lib::loop_invariant!(|i: usize| i <= 16);
            let coefficient = Vector::deserialize_11(bytes);
            re.coefficients[i] = Vector::decompress_ciphertext_coefficient::<11>(coefficient);
        }
    }

    re
}

#[inline(always)]
#[hax_lib::requires(
    (COMPRESSION_FACTOR == 10 || COMPRESSION_FACTOR == 11) &&
    serialized.len() == (COEFFICIENTS_IN_RING_ELEMENT * COMPRESSION_FACTOR) / 8
)]
pub(super) fn deserialize_then_decompress_ring_element_u<
    const COMPRESSION_FACTOR: usize,
    Vector: Operations,
>(
    serialized: &[u8],
) -> PolynomialRingElement<Vector> {
    hax_lib::fstar!("assert (
        (v (cast $COMPRESSION_FACTOR <: u32) == 10) \\/
        (v (cast $COMPRESSION_FACTOR <: u32) == 11))");
    match COMPRESSION_FACTOR as u32 {
        10 => deserialize_then_decompress_10(serialized),
        11 => deserialize_then_decompress_11(serialized),
        _ => unreachable!(),
    }
}

#[inline(always)]
#[hax_lib::requires(
    serialized.len() == (COEFFICIENTS_IN_RING_ELEMENT * 4) / 8
)]
fn deserialize_then_decompress_4<Vector: Operations>(
    serialized: &[u8],
) -> PolynomialRingElement<Vector> {
    hax_lib::fstar!("assert (v (($COEFFICIENTS_IN_RING_ELEMENT *! sz 4) /! sz 8) == 128)");
    let mut re = PolynomialRingElement::<Vector>::ZERO();

    cloop! {
        for (i, bytes) in serialized.chunks_exact(8).enumerate() {
            hax_lib::loop_invariant!(|i: usize| i <= 16);
            let coefficient = Vector::deserialize_4(bytes);
            re.coefficients[i] = Vector::decompress_ciphertext_coefficient::<4>(coefficient);
        }
    }
    re
}

#[inline(always)]
#[hax_lib::requires(
    serialized.len() == (COEFFICIENTS_IN_RING_ELEMENT * 5) / 8
)]
fn deserialize_then_decompress_5<Vector: Operations>(
    serialized: &[u8],
) -> PolynomialRingElement<Vector> {
    hax_lib::fstar!("assert (v (($COEFFICIENTS_IN_RING_ELEMENT *! sz 5) /! sz 8) == 160)");
    let mut re = PolynomialRingElement::<Vector>::ZERO();

    cloop! {
        for (i, bytes) in serialized.chunks_exact(10).enumerate() {
            hax_lib::loop_invariant!(|i: usize| i <= 16);
            re.coefficients[i] = Vector::deserialize_5(bytes);
            re.coefficients[i] = Vector::decompress_ciphertext_coefficient::<5>(re.coefficients[i]);
        }
    }
    re
}

#[inline(always)]
#[hax_lib::requires(
    (COMPRESSION_FACTOR == 4 || COMPRESSION_FACTOR == 5) &&
    serialized.len() == (COEFFICIENTS_IN_RING_ELEMENT * COMPRESSION_FACTOR) / 8
)]
pub(super) fn deserialize_then_decompress_ring_element_v<
    const COMPRESSION_FACTOR: usize,
    Vector: Operations,
>(
    serialized: &[u8],
) -> PolynomialRingElement<Vector> {
    hax_lib::fstar!("assert (
        (v (cast $COMPRESSION_FACTOR <: u32) == 4) \\/
        (v (cast $COMPRESSION_FACTOR <: u32) == 5))");
    match COMPRESSION_FACTOR as u32 {
        4 => deserialize_then_decompress_4(serialized),
        5 => deserialize_then_decompress_5(serialized),
        _ => unreachable!(),
    }
}
