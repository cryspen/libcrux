use crate::{
    constants::{BYTES_PER_RING_ELEMENT, SHARED_SECRET_SIZE},
    hax_utils::hax_debug_assert,
    helper::cloop,
    polynomial::{PolynomialRingElement, VECTORS_IN_RING_ELEMENT},
    vector::{decompress_1, to_unsigned_representative, Operations},
};

use hax_lib::*;
use hax_lib::int::*;

#[cfg(hax)]
use super::constants::COEFFICIENTS_IN_RING_ELEMENT;

#[cfg_attr(hax, requires(
    32 + 2 <= SHARED_SECRET_SIZE
))]
#[inline(always)]
pub(super) fn compress_then_serialize_message<Vector: Operations>(
    re: PolynomialRingElement<Vector>,
) -> [u8; SHARED_SECRET_SIZE] {
    let mut serialized = [0u8; SHARED_SECRET_SIZE];
    for i in 0..16 {
        let coefficient = to_unsigned_representative::<Vector>(re.coefficients[i]);
        fstar!("assume (Libcrux_ml_kem.Vector.Traits.f_compress_1_pre #v_Vector coefficient)");
        let coefficient_compressed = Vector::compress_1(coefficient);
        fstar!("assume (Libcrux_ml_kem.Vector.Traits.f_serialize_1_pre #v_Vector coefficient_compressed)");
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
        fstar!("assume (Libcrux_ml_kem.Vector.Traits.f_deserialize_1_pre #v_Vector (serialized.[ {
                Core.Ops.Range.f_start = sz 2 *! i <: usize;
                Core.Ops.Range.f_end = (sz 2 *! i <: usize) +! sz 2 <: usize
                }
                <:
                Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8))");
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

        fstar!("assume (Libcrux_ml_kem.Vector.Traits.f_serialize_12_pre #v_Vector coefficient)");
        let bytes = Vector::serialize_12(coefficient);
        serialized[24 * i..24 * i + 24].copy_from_slice(&bytes);
    }
    serialized
}

#[inline(always)]
pub(super) fn deserialize_to_uncompressed_ring_element<Vector: Operations>(
    serialized: &[u8],
) -> PolynomialRingElement<Vector> {
    hax_debug_assert!(serialized.len() == BYTES_PER_RING_ELEMENT);

    let mut re = PolynomialRingElement::<Vector>::ZERO();

    cloop! {
        for (i, bytes) in serialized.chunks_exact(24).enumerate() {
            fstar!("assume (Libcrux_ml_kem.Vector.Traits.f_deserialize_12_pre #v_Vector bytes)");
            assume!(i < 16);
            re.coefficients[i] = Vector::deserialize_12(bytes);
        }
    }

    re
}

/// Only use with public values.
///
/// This MUST NOT be used with secret inputs, like its caller `deserialize_ring_elements_reduced`.
#[inline(always)]
fn deserialize_to_reduced_ring_element<Vector: Operations>(
    serialized: &[u8],
) -> PolynomialRingElement<Vector> {
    hax_debug_assert!(serialized.len() == BYTES_PER_RING_ELEMENT);

    let mut re = PolynomialRingElement::<Vector>::ZERO();

    cloop! {
        for (i, bytes) in serialized.chunks_exact(24).enumerate() {
            fstar!("assume (Libcrux_ml_kem.Vector.Traits.f_deserialize_12_pre #v_Vector bytes)");
            let coefficient = Vector::deserialize_12(bytes);
            fstar!("assume (Libcrux_ml_kem.Vector.Traits.f_cond_subtract_3329_pre #v_Vector coefficient)");
            assume!(i < 16);
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
            assume!(i < K);
            deserialized_pk[i] = deserialize_to_reduced_ring_element(ring_element);
        }
    }
    deserialized_pk
}

#[cfg_attr(hax, requires(
    20 * VECTORS_IN_RING_ELEMENT + 20 <= OUT_LEN
))]
#[inline(always)]
fn compress_then_serialize_10<const OUT_LEN: usize, Vector: Operations>(
    re: &PolynomialRingElement<Vector>,
) -> [u8; OUT_LEN] {
    let mut serialized = [0u8; OUT_LEN];
    for i in 0..VECTORS_IN_RING_ELEMENT {
        fstar!("assume (Libcrux_ml_kem.Vector.Traits.f_compress_pre #v_Vector
            #(_ by (FStar.Tactics.Typeclasses.tcresolve ()))
            #10l
            (Libcrux_ml_kem.Vector.Traits.to_unsigned_representative #v_Vector
                (re.Libcrux_ml_kem.Polynomial.f_coefficients.[ i ] <: v_Vector)
            <:
            v_Vector))");
        let coefficient =
            Vector::compress::<10>(to_unsigned_representative::<Vector>(re.coefficients[i]));

        fstar!("assume (Libcrux_ml_kem.Vector.Traits.f_serialize_10_pre #v_Vector coefficient)");
        let bytes = Vector::serialize_10(coefficient);
        serialized[20 * i..20 * i + 20].copy_from_slice(&bytes);
    }
    serialized
}

#[cfg_attr(hax, requires(
    22 * VECTORS_IN_RING_ELEMENT + 22 <= OUT_LEN
))]
#[inline(always)]
fn compress_then_serialize_11<const OUT_LEN: usize, Vector: Operations>(
    re: &PolynomialRingElement<Vector>,
) -> [u8; OUT_LEN] {
    let mut serialized = [0u8; OUT_LEN];
    for i in 0..VECTORS_IN_RING_ELEMENT {
        fstar!("assume (Libcrux_ml_kem.Vector.Traits.f_compress_pre #v_Vector
            #(_ by (FStar.Tactics.Typeclasses.tcresolve ()))
            #11l
            (Libcrux_ml_kem.Vector.Traits.to_unsigned_representative #v_Vector
                (re.Libcrux_ml_kem.Polynomial.f_coefficients.[ i ] <: v_Vector)
            <:
            v_Vector))");
        let coefficient =
            Vector::compress::<11>(to_unsigned_representative::<Vector>(re.coefficients[i]));

        fstar!("assume (Libcrux_ml_kem.Vector.Traits.f_serialize_11_pre #v_Vector coefficient)");
        let bytes = Vector::serialize_11(coefficient);
        serialized[22 * i..22 * i + 22].copy_from_slice(&bytes);
    }
    serialized
}

#[cfg_attr(hax, requires(
    22 * VECTORS_IN_RING_ELEMENT + 22 <= OUT_LEN
))]
#[inline(always)]
pub(super) fn compress_then_serialize_ring_element_u<
    const COMPRESSION_FACTOR: usize,
    const OUT_LEN: usize,
    Vector: Operations,
>(
    re: &PolynomialRingElement<Vector>,
) -> [u8; OUT_LEN] {
    hax_debug_assert!((COEFFICIENTS_IN_RING_ELEMENT * COMPRESSION_FACTOR) / 8 == OUT_LEN);

    match COMPRESSION_FACTOR as u32 {
        10 => compress_then_serialize_10(re),
        11 => compress_then_serialize_11(re),
        //_ => unreachable!(), //Does't verify, maybe we can use Option enum!!
        _ => [0u8; OUT_LEN],
    }
}

#[inline(always)]
fn compress_then_serialize_4<Vector: Operations>(
    re: PolynomialRingElement<Vector>,
    serialized: &mut [u8],
) {
    for i in 0..VECTORS_IN_RING_ELEMENT {
        fstar!("assume (Libcrux_ml_kem.Vector.Traits.f_compress_pre #v_Vector
            #(_ by (FStar.Tactics.Typeclasses.tcresolve ()))
            #4l
            (Libcrux_ml_kem.Vector.Traits.to_unsigned_representative #v_Vector
                (re.Libcrux_ml_kem.Polynomial.f_coefficients.[ i ] <: v_Vector)
            <:
            v_Vector))");
        let coefficient: Vector =
            Vector::compress::<4>(to_unsigned_representative::<Vector>(re.coefficients[i]));

        fstar!("assume (Libcrux_ml_kem.Vector.Traits.f_serialize_4_pre #v_Vector coefficient)");
        let bytes = Vector::serialize_4(coefficient);
        assume!(8 * VECTORS_IN_RING_ELEMENT + 8 <= serialized.len());
        serialized[8 * i..8 * i + 8].copy_from_slice(&bytes);
    };
    ()
}

#[inline(always)]
fn compress_then_serialize_5<Vector: Operations>(
    re: PolynomialRingElement<Vector>,
    serialized: &mut [u8],
) {
    for i in 0..VECTORS_IN_RING_ELEMENT {
        fstar!("assume(Libcrux_ml_kem.Vector.Traits.f_compress_pre #v_Vector
            #(_ by (FStar.Tactics.Typeclasses.tcresolve ()))
            #5l
            (Libcrux_ml_kem.Vector.Traits.to_unsigned_representative #v_Vector
                (re.Libcrux_ml_kem.Polynomial.f_coefficients.[ i ] <: v_Vector)
              <:
              v_Vector))");
        let coefficients =
            Vector::compress::<5>(to_unsigned_representative::<Vector>(re.coefficients[i]));

        fstar!("assume(Libcrux_ml_kem.Vector.Traits.f_serialize_5_pre #v_Vector coefficients)");
        let bytes = Vector::serialize_5(coefficients);
        assume!(10 * VECTORS_IN_RING_ELEMENT + 10 <= serialized.len());
        serialized[10 * i..10 * i + 10].copy_from_slice(&bytes);
    };
    ()
}

#[inline(always)]
pub(super) fn compress_then_serialize_ring_element_v<
    const COMPRESSION_FACTOR: usize,
    const OUT_LEN: usize,
    Vector: Operations,
>(
    re: PolynomialRingElement<Vector>,
    out: &mut [u8],
) {
    hax_debug_assert!((COEFFICIENTS_IN_RING_ELEMENT * COMPRESSION_FACTOR) / 8 == OUT_LEN);

    match COMPRESSION_FACTOR as u32 {
        4 => compress_then_serialize_4(re, out),
        5 => compress_then_serialize_5(re, out),
        //_ => unreachable!(),
        _ => (),
    }
}

#[inline(always)]
fn deserialize_then_decompress_10<Vector: Operations>(
    serialized: &[u8],
) -> PolynomialRingElement<Vector> {
    hax_debug_assert!(serialized.len() == (COEFFICIENTS_IN_RING_ELEMENT * 10) / 8);

    let mut re = PolynomialRingElement::<Vector>::ZERO();

    cloop! {
        for (i, bytes) in serialized.chunks_exact(20).enumerate() {
            fstar!("assume (Libcrux_ml_kem.Vector.Traits.f_deserialize_10_pre #v_Vector bytes)");
            let coefficient = Vector::deserialize_10(bytes);
            fstar!("assume (Libcrux_ml_kem.Vector.Traits.f_decompress_ciphertext_coefficient_pre #v_Vector
                #(_ by (FStar.Tactics.Typeclasses.tcresolve ()))
                #10l
                coefficient)");
            assume!(i < 16);
            re.coefficients[i] = Vector::decompress_ciphertext_coefficient::<10>(coefficient);
        }
    }
    re
}

#[inline(always)]
fn deserialize_then_decompress_11<Vector: Operations>(
    serialized: &[u8],
) -> PolynomialRingElement<Vector> {
    hax_debug_assert!(serialized.len() == (COEFFICIENTS_IN_RING_ELEMENT * 11) / 8);

    let mut re = PolynomialRingElement::<Vector>::ZERO();

    cloop! {
        for (i, bytes) in serialized.chunks_exact(22).enumerate() {
            fstar!("assume (Libcrux_ml_kem.Vector.Traits.f_deserialize_11_pre #v_Vector bytes)");
            let coefficient = Vector::deserialize_11(bytes);
            fstar!("assume (Libcrux_ml_kem.Vector.Traits.f_decompress_ciphertext_coefficient_pre #v_Vector
                #(_ by (FStar.Tactics.Typeclasses.tcresolve ()))
                #11l
                coefficient)");
            assume!(i < 16);
            re.coefficients[i] = Vector::decompress_ciphertext_coefficient::<11>(coefficient);
        }
    }

    re
}

#[inline(always)]
pub(super) fn deserialize_then_decompress_ring_element_u<
    const COMPRESSION_FACTOR: usize,
    Vector: Operations,
>(
    serialized: &[u8],
) -> PolynomialRingElement<Vector> {
    hax_debug_assert!(serialized.len() == (COEFFICIENTS_IN_RING_ELEMENT * COMPRESSION_FACTOR) / 8);

    match COMPRESSION_FACTOR as u32 {
        10 => deserialize_then_decompress_10(serialized),
        11 => deserialize_then_decompress_11(serialized),
        //_ => unreachable!(),
        _ => PolynomialRingElement::<Vector>::ZERO(),
    }
}

#[inline(always)]
fn deserialize_then_decompress_4<Vector: Operations>(
    serialized: &[u8],
) -> PolynomialRingElement<Vector> {
    hax_debug_assert!(serialized.len() == (COEFFICIENTS_IN_RING_ELEMENT * 4) / 8);
    let mut re = PolynomialRingElement::<Vector>::ZERO();
    cloop! {
        for (i, bytes) in serialized.chunks_exact(8).enumerate() {
            fstar!("assume (Libcrux_ml_kem.Vector.Traits.f_deserialize_4_pre #v_Vector bytes)");
            let coefficient = Vector::deserialize_4(bytes);
            fstar!("assume (Libcrux_ml_kem.Vector.Traits.f_decompress_ciphertext_coefficient_pre #v_Vector
                #(_ by (FStar.Tactics.Typeclasses.tcresolve ()))
                #4l
                coefficient)");
            assume!(i < 16);
            re.coefficients[i] = Vector::decompress_ciphertext_coefficient::<4>(coefficient);
        }
    }
    re
}

#[inline(always)]
fn deserialize_then_decompress_5<Vector: Operations>(
    serialized: &[u8],
) -> PolynomialRingElement<Vector> {
    hax_debug_assert!(serialized.len() == (COEFFICIENTS_IN_RING_ELEMENT * 5) / 8);

    let mut re = PolynomialRingElement::<Vector>::ZERO();

    cloop! {
        for (i, bytes) in serialized.chunks_exact(10).enumerate() {
            fstar!("assume (Libcrux_ml_kem.Vector.Traits.f_deserialize_5_pre #v_Vector bytes)");
            assume!(i < 16);
            re.coefficients[i] = Vector::deserialize_5(bytes);
            fstar!("assume (Libcrux_ml_kem.Vector.Traits.f_decompress_ciphertext_coefficient_pre #v_Vector
                #(_ by (FStar.Tactics.Typeclasses.tcresolve ()))
                #5l
                (re.Libcrux_ml_kem.Polynomial.f_coefficients.[ i ] <: v_Vector))");
            re.coefficients[i] = Vector::decompress_ciphertext_coefficient::<5>(re.coefficients[i]);
        }
    }
    re
}

#[inline(always)]
pub(super) fn deserialize_then_decompress_ring_element_v<
    const COMPRESSION_FACTOR: usize,
    Vector: Operations,
>(
    serialized: &[u8],
) -> PolynomialRingElement<Vector> {
    hax_debug_assert!(serialized.len() == (COEFFICIENTS_IN_RING_ELEMENT * COMPRESSION_FACTOR) / 8);

    match COMPRESSION_FACTOR as u32 {
        4 => deserialize_then_decompress_4(serialized),
        5 => deserialize_then_decompress_5(serialized),
        //_ => unreachable!(),
        _ => PolynomialRingElement::<Vector>::ZERO(),
    }
}
