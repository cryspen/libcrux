use crate::{
    constants::{BYTES_PER_RING_ELEMENT, SHARED_SECRET_SIZE},
    helper::cloop,
    polynomial::{PolynomialRingElement, VECTORS_IN_RING_ELEMENT},
    vector::{traits::decompress_1, Operations},
};

#[inline(always)]
#[hax_lib::fstar::verification_status(panic_free)]
#[hax_lib::requires(fstar!(r#"Libcrux_ml_kem.Polynomial.is_bounded_vector 3328 $a"#))]
#[hax_lib::ensures(|_| fstar!(r#"forall (i:nat). i < 16 ==>
    v (Seq.index (i0._super_16084754032855797384.f_repr ${out}_future) i) >= 0 /\
    v (Seq.index (i0._super_16084754032855797384.f_repr ${out}_future) i) < v ${crate::vector::FIELD_MODULUS}"#))]
pub(super) fn to_unsigned_field_modulus<Vector: Operations>(a: &Vector, out: &mut Vector) {
    *out = Vector::to_unsigned_representative(*a);
}

#[inline(always)]
#[hax_lib::fstar::verification_status(panic_free)]
#[hax_lib::requires(fstar!(r#"Libcrux_ml_kem.Polynomial.is_bounded_poly 3328 $re /\ 
    Seq.length $serialized == v ${crate::constants::SHARED_SECRET_SIZE}"#))]
#[hax_lib::ensures(|_|
    fstar!(r#"${serialized}_future ==
        Spec.MLKEM.compress_then_encode_message (Libcrux_ml_kem.Polynomial.to_spec_poly_t #$:Vector $re)
          /\ Seq.length ${serialized}_future = Seq.length $serialized"#)
)]
pub(super) fn compress_then_serialize_message<Vector: Operations>(
    re: &PolynomialRingElement<Vector>,
    serialized: &mut [u8],
    scratch: &mut Vector,
) {
    for i in 0..16 {
        hax_lib::loop_invariant!(|i: usize| {
            fstar!("v $i < 16 ==> Libcrux_ml_kem.Polynomial.is_bounded_poly 3328 $re")
        });
        hax_lib::fstar!(r#"assert (2 * v $i + 2 <= 32)"#);
        to_unsigned_field_modulus(&re.coefficients[i], scratch);
        Vector::compress_1(scratch);

        Vector::serialize_1(scratch, &mut serialized[2 * i..2 * i + 2]);
    }
}

#[inline(always)]
#[hax_lib::fstar::verification_status(panic_free)]
#[hax_lib::ensures(|_|
    fstar!(r#"Libcrux_ml_kem.Polynomial.to_spec_poly_t #$:Vector ${re}_future ==
        Spec.MLKEM.decode_then_decompress_message $serialized"#)
)]
pub(super) fn deserialize_then_decompress_message<Vector: Operations>(
    serialized: &[u8; SHARED_SECRET_SIZE],
    re: &mut PolynomialRingElement<Vector>,
) {
    for i in 0..16 {
        Vector::deserialize_1(&serialized[2 * i..2 * i + 2], &mut re.coefficients[i]);
        decompress_1::<Vector>(&mut re.coefficients[i]);
    }
}

#[inline(always)]
#[hax_lib::fstar::verification_status(panic_free)]
#[hax_lib::requires(fstar!(r#"Libcrux_ml_kem.Polynomial.is_bounded_poly 3328 $re /\ 
    Seq.length $serialized == v ${crate::constants::BYTES_PER_RING_ELEMENT}"#))]
#[hax_lib::ensures(|_|
    fstar!(r#"${serialized}_future ==
        Spec.MLKEM.byte_encode 12 (Libcrux_ml_kem.Polynomial.to_spec_poly_t #$:Vector $re)
        /\ Seq.length ${serialized}_future = Seq.length $serialized"#)
)]
pub(super) fn serialize_uncompressed_ring_element<Vector: Operations>(
    re: &PolynomialRingElement<Vector>,
    scratch: &mut Vector,
    serialized: &mut [u8],
) {
    debug_assert!(serialized.len() == BYTES_PER_RING_ELEMENT);
    hax_lib::fstar!(r#"assert_norm (pow2 12 == 4096)"#);
    for i in 0..VECTORS_IN_RING_ELEMENT {
        hax_lib::loop_invariant!(|i: usize| {
            fstar!(
                r#"v $i >= 0 /\ v $i <= 16 /\
            v $i < 16 ==> Libcrux_ml_kem.Polynomial.is_bounded_poly 3328 $re"#
            )
        });
        hax_lib::fstar!(r#"assert (24 * v $i + 24 <= 384)"#);

        to_unsigned_field_modulus(&re.coefficients[i], scratch);

        Vector::serialize_12(scratch, &mut serialized[24 * i..24 * i + 24]);
    }
}

#[inline(always)]
#[hax_lib::fstar::verification_status(panic_free)]
#[hax_lib::requires(
    serialized.len() == BYTES_PER_RING_ELEMENT
)]
#[hax_lib::ensures(|_|
    fstar!(r#"Libcrux_ml_kem.Polynomial.to_spec_poly_t #$:Vector ${re}_future == 
        Spec.MLKEM.byte_decode 12 $serialized"#)
)]
pub(super) fn deserialize_to_uncompressed_ring_element<Vector: Operations>(
    serialized: &[u8],
    re: &mut PolynomialRingElement<Vector>,
) {
    hax_lib::fstar!(r#"assert (v $BYTES_PER_RING_ELEMENT / 24 == 16)"#);
    cloop! {
        for (i, bytes) in serialized.chunks_exact(24).enumerate() {
            Vector::deserialize_12(bytes, &mut re.coefficients[i]);
        }
    }
}

/// Only use with public values.
///
/// This MUST NOT be used with secret inputs, like its caller `deserialize_ring_elements_reduced`.
#[inline(always)]
#[hax_lib::fstar::verification_status(panic_free)]
#[hax_lib::requires(
    serialized.len() == BYTES_PER_RING_ELEMENT
)]
fn deserialize_to_reduced_ring_element<Vector: Operations>(
    serialized: &[u8],
    re: &mut PolynomialRingElement<Vector>,
) {
    hax_lib::fstar!(r#"assert (v $BYTES_PER_RING_ELEMENT / 24 == 16)"#);
    cloop! {
        for (i, bytes) in serialized.chunks_exact(24).enumerate() {
            Vector::deserialize_12(bytes, &mut re.coefficients[i]);
            Vector::cond_subtract_3329(&mut re.coefficients[i]);
        }
    }
}

/// This function deserializes ring elements and reduces the result by the field
/// modulus.
///
/// This function MUST NOT be used on secret inputs.
#[inline(always)]
#[hax_lib::fstar::verification_status(panic_free)]
#[hax_lib::requires(
    fstar!(r#"Spec.MLKEM.is_rank v_K /\ 
            Seq.length $deserialized_pk == v v_K /\
            Seq.length $public_key == v (Spec.MLKEM.v_T_AS_NTT_ENCODED_SIZE v_K)"#)
)]
#[hax_lib::ensures(|_|
    fstar!(r#"Seq.length ${deserialized_pk}_future == v v_K /\
        Libcrux_ml_kem.Polynomial.to_spec_vector_t #$K #$:Vector ${deserialized_pk}_future == 
         Spec.MLKEM.vector_decode_12 #$K $public_key"#)
)]
pub(super) fn deserialize_ring_elements_reduced<const K: usize, Vector: Operations>(
    public_key: &[u8],
    deserialized_pk: &mut [PolynomialRingElement<Vector>],
) {
    cloop! {
        for (i, ring_element) in public_key
            .chunks_exact(BYTES_PER_RING_ELEMENT)
            .enumerate()
        {
            deserialize_to_reduced_ring_element(ring_element, &mut deserialized_pk[i]);
        }
    };
    ()
}

#[inline(always)]
#[hax_lib::fstar::verification_status(panic_free)]
#[hax_lib::requires(fstar!(r#"v $OUT_LEN == 320 /\ 
    Libcrux_ml_kem.Polynomial.is_bounded_poly 3328  $re /\ 
    Seq.length $serialized == v $OUT_LEN"#))]
fn compress_then_serialize_10<const OUT_LEN: usize, Vector: Operations>(
    re: &PolynomialRingElement<Vector>,
    serialized: &mut [u8],
    scratch: &mut Vector,
) {
    debug_assert!(serialized.len() == OUT_LEN);
    hax_lib::fstar!(r#"assert_norm (pow2 10 == 1024)"#);
    for i in 0..VECTORS_IN_RING_ELEMENT {
        hax_lib::loop_invariant!(|i: usize| {
            fstar!(
                r#"v $i >= 0 /\ v $i <= 16 /\
            v $i < 16 ==> Libcrux_ml_kem.Polynomial.is_bounded_poly 3328 $re"#
            )
        });
        hax_lib::fstar!(r#"assert (20 * v $i + 20 <= 320)"#);
        to_unsigned_field_modulus(&re.coefficients[i], scratch);
        Vector::compress::<10>(scratch);

        Vector::serialize_10(scratch, &mut serialized[20 * i..20 * i + 20]);
    }
}

#[inline(always)]
#[hax_lib::fstar::verification_status(lax)]
fn compress_then_serialize_11<const OUT_LEN: usize, Vector: Operations>(
    re: &PolynomialRingElement<Vector>,
    serialized: &mut [u8],
    scratch: &mut Vector,
) {
    debug_assert!(serialized.len() == OUT_LEN);

    for i in 0..VECTORS_IN_RING_ELEMENT {
        *scratch = Vector::to_unsigned_representative(re.coefficients[i]);
        Vector::compress::<11>(scratch);

        Vector::serialize_11(scratch, &mut serialized[22 * i..22 * i + 22]);
    }
}

#[inline(always)]
#[hax_lib::fstar::verification_status(panic_free)]
#[hax_lib::requires(fstar!(r#"(v $COMPRESSION_FACTOR == 10 \/ v $COMPRESSION_FACTOR == 11) /\
    v $OUT_LEN == 32 * v $COMPRESSION_FACTOR /\ Libcrux_ml_kem.Polynomial.is_bounded_poly 3328 $re /\
    Seq.length $serialized == v $OUT_LEN"#))]
#[hax_lib::ensures(|_|
    fstar!(r#"${serialized}_future == Spec.MLKEM.compress_then_byte_encode (v $COMPRESSION_FACTOR)
        (Libcrux_ml_kem.Polynomial.to_spec_poly_t #$:Vector $re)"#)
)]
pub(super) fn compress_then_serialize_ring_element_u<
    const COMPRESSION_FACTOR: usize,
    const OUT_LEN: usize,
    Vector: Operations,
>(
    re: &PolynomialRingElement<Vector>,
    serialized: &mut [u8],
    scratch: &mut Vector,
) {
    hax_lib::fstar!(
        r#"assert (
        (v (cast $COMPRESSION_FACTOR <: u32) == 10) \/
        (v (cast $COMPRESSION_FACTOR <: u32) == 11))"#
    );
    match COMPRESSION_FACTOR as u32 {
        10 => compress_then_serialize_10::<OUT_LEN, Vector>(re, serialized, scratch),
        11 => compress_then_serialize_11::<OUT_LEN, Vector>(re, serialized, scratch),
        _ => unreachable!(),
    }
}

#[inline(always)]
#[hax_lib::fstar::verification_status(panic_free)]
#[hax_lib::requires(fstar!(r#"Seq.length $serialized == 128 /\
    Libcrux_ml_kem.Polynomial.is_bounded_poly 3328 $re"#))]
#[hax_lib::ensures(|_|
    fstar!(r#"${serialized_future.len()} == ${serialized.len()}"#)
)]
fn compress_then_serialize_4<Vector: Operations>(
    re: PolynomialRingElement<Vector>,
    serialized: &mut [u8],
    scratch: &mut Vector,
) {
    hax_lib::fstar!(r#"assert_norm (pow2 4 == 16)"#);
    for i in 0..VECTORS_IN_RING_ELEMENT {
        // NOTE: Using `$serialized` in loop_invariant doesn't work here
        hax_lib::loop_invariant!(|i: usize| {
            fstar!(
                r#"v $i >= 0 /\ v $i <= 16 /\
            v $i < 16 ==> (Seq.length serialized == 128 /\ 
                           Libcrux_ml_kem.Polynomial.is_bounded_poly 3328 $re)"#
            )
        });
        hax_lib::fstar!(r#"assert (8 * v $i + 8 <= 128)"#);
        to_unsigned_field_modulus(&re.coefficients[i], scratch);
        Vector::compress::<4>(scratch);

        Vector::serialize_4(scratch, &mut serialized[8 * i..8 * i + 8]);
    }
}

#[inline(always)]
#[hax_lib::fstar::verification_status(lax)]
#[hax_lib::requires(
    serialized.len() == 160
)]
#[hax_lib::ensures(|_|
    fstar!(r#"${serialized_future.len()} == ${serialized.len()}"#)
)]
fn compress_then_serialize_5<Vector: Operations>(
    re: PolynomialRingElement<Vector>,
    serialized: &mut [u8],
    scratch: &mut Vector,
) {
    for i in 0..VECTORS_IN_RING_ELEMENT {
        *scratch = Vector::to_unsigned_representative(re.coefficients[i]);
        Vector::compress::<5>(scratch);

        Vector::serialize_5(scratch, &mut serialized[10 * i..10 * i + 10]);
    }
}

#[inline(always)]
#[hax_lib::fstar::verification_status(panic_free)]
#[hax_lib::requires(fstar!(r#"Spec.MLKEM.is_rank v_K /\ 
    $COMPRESSION_FACTOR == Spec.MLKEM.v_VECTOR_V_COMPRESSION_FACTOR v_K /\
    Seq.length $out == v $OUT_LEN /\ v $OUT_LEN == 32 * v $COMPRESSION_FACTOR /\
    Libcrux_ml_kem.Polynomial.is_bounded_poly 3328 $re"#))]
#[hax_lib::ensures(|_|
    fstar!(r#"${out_future.len()} == ${out.len()} /\
        ${out}_future == Spec.MLKEM.compress_then_encode_v #v_K
            (Libcrux_ml_kem.Polynomial.to_spec_poly_t #$:Vector $re)"#)
)]
pub(super) fn compress_then_serialize_ring_element_v<
    const K: usize,
    const COMPRESSION_FACTOR: usize,
    const OUT_LEN: usize,
    Vector: Operations,
>(
    re: PolynomialRingElement<Vector>,
    out: &mut [u8],
    scratch: &mut Vector,
) {
    hax_lib::fstar!(
        r#"assert (
        (v (cast $COMPRESSION_FACTOR <: u32) == 4) \/
        (v (cast $COMPRESSION_FACTOR <: u32) == 5))"#
    );
    match COMPRESSION_FACTOR as u32 {
        4 => compress_then_serialize_4::<Vector>(re, out, scratch),
        5 => compress_then_serialize_5::<Vector>(re, out, scratch),
        _ => unreachable!(),
    }
}

#[inline(always)]
#[hax_lib::requires(
    serialized.len() == 320
)]
fn deserialize_then_decompress_10<Vector: Operations>(
    serialized: &[u8],
    re: &mut PolynomialRingElement<Vector>,
) {
    hax_lib::fstar!(
        r#"assert (v ((${crate::constants::COEFFICIENTS_IN_RING_ELEMENT} *! sz 10) /! sz 8) == 320)"#
    );
    cloop! {
        for (i, bytes) in serialized.chunks_exact(20).enumerate() {
            Vector::deserialize_10(bytes, &mut re.coefficients[i]);
            Vector::decompress_ciphertext_coefficient::<10>(&mut re.coefficients[i]);
        }
    }
}

#[inline(always)]
#[hax_lib::fstar::verification_status(lax)]
#[hax_lib::requires(
    serialized.len() == 352
)]
fn deserialize_then_decompress_11<Vector: Operations>(
    serialized: &[u8],
    re: &mut PolynomialRingElement<Vector>,
) {
    hax_lib::fstar!(
        r#"assert (v ((${crate::constants::COEFFICIENTS_IN_RING_ELEMENT} *! sz 11) /! sz 8) == 352)"#
    );
    cloop! {
        for (i, bytes) in serialized.chunks_exact(22).enumerate() {
            Vector::deserialize_11(bytes, &mut re.coefficients[i]);
            Vector::decompress_ciphertext_coefficient::<11>(&mut re.coefficients[i]);
        }
    }
}

#[inline(always)]
#[hax_lib::fstar::verification_status(panic_free)]
#[hax_lib::requires(
    (COMPRESSION_FACTOR == 10 || COMPRESSION_FACTOR == 11) &&
    serialized.len() == 32 * COMPRESSION_FACTOR
)]
#[hax_lib::ensures(|_|
    fstar!(r#"Libcrux_ml_kem.Polynomial.to_spec_poly_t #$:Vector ${output}_future == 
        Spec.MLKEM.byte_decode_then_decompress (v $COMPRESSION_FACTOR) $serialized"#)
)]
pub(super) fn deserialize_then_decompress_ring_element_u<
    const COMPRESSION_FACTOR: usize,
    Vector: Operations,
>(
    serialized: &[u8],
    output: &mut PolynomialRingElement<Vector>,
) {
    hax_lib::fstar!(
        r#"assert (
        (v (cast $COMPRESSION_FACTOR <: u32) == 10) \/
        (v (cast $COMPRESSION_FACTOR <: u32) == 11))"#
    );
    match COMPRESSION_FACTOR as u32 {
        10 => deserialize_then_decompress_10::<Vector>(serialized, output),
        11 => deserialize_then_decompress_11::<Vector>(serialized, output),
        _ => unreachable!(),
    };
}

#[inline(always)]
#[hax_lib::requires(
    serialized.len() == 128
)]
fn deserialize_then_decompress_4<Vector: Operations>(
    serialized: &[u8],
    re: &mut PolynomialRingElement<Vector>,
) {
    hax_lib::fstar!(
        r#"assert (v ((${crate::constants::COEFFICIENTS_IN_RING_ELEMENT} *! sz 4) /! sz 8) == 128)"#
    );
    cloop! {
        for (i, bytes) in serialized.chunks_exact(8).enumerate() {
            Vector::deserialize_4(bytes, &mut re.coefficients[i]);
            Vector::decompress_ciphertext_coefficient::<4>(&mut re.coefficients[i]);
        }
    }
}

#[inline(always)]
#[hax_lib::fstar::verification_status(lax)]
#[hax_lib::requires(
    serialized.len() == 160
)]
fn deserialize_then_decompress_5<Vector: Operations>(
    serialized: &[u8],
    re: &mut PolynomialRingElement<Vector>,
) {
    hax_lib::fstar!(
        r#"assert (v ((${crate::constants::COEFFICIENTS_IN_RING_ELEMENT} *! sz 5) /! sz 8) == 160)"#
    );
    cloop! {
        for (i, bytes) in serialized.chunks_exact(10).enumerate() {
            Vector::deserialize_5(bytes, &mut re.coefficients[i]);
            Vector::decompress_ciphertext_coefficient::<5>(&mut re.coefficients[i]);
        }
    }
}

#[inline(always)]
#[hax_lib::fstar::verification_status(panic_free)]
#[hax_lib::requires(fstar!(r#"Spec.MLKEM.is_rank $K /\ 
    $COMPRESSION_FACTOR == Spec.MLKEM.v_VECTOR_V_COMPRESSION_FACTOR $K /\
    Seq.length $serialized == 32 * v $COMPRESSION_FACTOR"#)
)]
#[hax_lib::ensures(|_|
    fstar!(r#"Libcrux_ml_kem.Polynomial.to_spec_poly_t #$:Vector ${output}_future == 
        Spec.MLKEM.decode_then_decompress_v #${K} $serialized"#)
)]
pub(super) fn deserialize_then_decompress_ring_element_v<
    const K: usize,
    const COMPRESSION_FACTOR: usize,
    Vector: Operations,
>(
    serialized: &[u8],
    output: &mut PolynomialRingElement<Vector>,
) {
    hax_lib::fstar!(
        r#"assert (
        (v (cast $COMPRESSION_FACTOR <: u32) == 4) \/
        (v (cast $COMPRESSION_FACTOR <: u32) == 5))"#
    );
    match COMPRESSION_FACTOR as u32 {
        4 => deserialize_then_decompress_4::<Vector>(serialized, output),
        5 => deserialize_then_decompress_5::<Vector>(serialized, output),
        _ => unreachable!(),
    }
}
