#[cfg(hax)]
use super::traits::spec;
use super::traits::{Operations, Repr};
use arithmetic::{bitwise_and_with_constant, shift_right};
pub(crate) use libcrux_intrinsics::avx2::*;

mod arithmetic;
mod compress;
mod ntt;
mod sampling;
mod serialize;

#[derive(Clone, Copy)]
#[hax_lib::fstar::before(interface, "noeq")]
#[hax_lib::fstar::after(interface,"let repr (x:t_SIMD256Vector) : t_Array i16 (sz 16) = Libcrux_intrinsics.Avx2_extract.vec256_as_i16x16 x.f_elements")]
pub struct SIMD256Vector {
    elements: Vec256,
}

#[inline(always)]
#[hax_lib::fstar::verification_status(panic_free)]
#[hax_lib::ensures(|result| fstar!(r#"repr ${result} == Seq.create 16 (mk_i16 0)"#))]
fn vec_zero() -> SIMD256Vector {
    SIMD256Vector {
        elements: mm256_setzero_si256(),
    }
}

#[inline(always)]
#[hax_lib::fstar::verification_status(panic_free)]
#[hax_lib::requires(out.len() == 16)]
#[hax_lib::ensures(|_| fstar!(r#"Seq.length ${out}_future == Seq.length $out /\
                                 ${out}_future == repr ${vector}"#))]
fn vec_to_i16_array(vector: &SIMD256Vector, out: &mut [i16]) {
    debug_assert!(out.len() >= 16);

    mm256_storeu_si256_i16(out, vector.elements);
}

#[inline(always)]
#[hax_lib::fstar::verification_status(panic_free)]
#[hax_lib::ensures(|_| fstar!(r#"repr ${out}_future == ${array}"#))]
fn vec_from_i16_array(array: &[i16], out: &mut SIMD256Vector) {
    out.elements = mm256_loadu_si256_i16(array);
}

#[inline(always)]
#[hax_lib::fstar::verification_status(lax)]
#[hax_lib::requires(fstar!(r#"Spec.Utils.is_i16b_array (pow2 12 - 1) (repr $vector)"#))]
#[hax_lib::ensures(|_| fstar!(r#"repr ${vector}_future == Spec.Utils.map_array (fun x -> if x >=. (mk_i16 3329) then x -! (mk_i16 3329) else x) (repr $vector)"#))]
fn cond_subtract_3329(vector: &mut SIMD256Vector) {
    arithmetic::cond_subtract_3329(&mut vector.elements);
}

#[inline(always)]
#[hax_lib::fstar::verification_status(lax)]
#[hax_lib::requires(fstar!(r#"forall (i:nat). i < 16 ==> v (Seq.index (repr $vector) i) >= 0 /\
    v (Seq.index (repr $vector) i) < 3329"#))]
#[hax_lib::ensures(|_| fstar!(r#"forall (i:nat). i < 16 ==> bounded (Seq.index (repr ${vector}_future) i) 1"#))]
fn compress_1(vector: &mut SIMD256Vector) {
    compress::compress_message_coefficient(&mut vector.elements);
}

#[inline(always)]
#[hax_lib::fstar::verification_status(lax)]
#[hax_lib::requires(fstar!(r#"(v $COEFFICIENT_BITS == 4 \/
    v $COEFFICIENT_BITS == 5 \/
    v $COEFFICIENT_BITS == 10 \/
    v $COEFFICIENT_BITS == 11) /\
    (forall (i:nat). i < 16 ==> v (Seq.index (repr $vector) i) >= 0 /\
    v (Seq.index (repr $vector) i) < 3329)"#))]
#[hax_lib::ensures(|_| fstar!(r#"(v $COEFFICIENT_BITS == 4 \/
    v $COEFFICIENT_BITS == 5 \/
    v $COEFFICIENT_BITS == 10 \/
    v $COEFFICIENT_BITS == 11) ==>
        (forall (i:nat). i < 16 ==> bounded (Seq.index (repr ${vector}_future) i) (v $COEFFICIENT_BITS))"#))]
fn compress<const COEFFICIENT_BITS: i32>(vector: &mut SIMD256Vector) {
    compress::compress_ciphertext_coefficient::<COEFFICIENT_BITS>(&mut vector.elements);
}

#[inline(always)]
#[hax_lib::fstar::verification_status(lax)]
#[hax_lib::requires(fstar!(r#"Spec.Utils.is_i16b 1664 zeta0 /\ Spec.Utils.is_i16b 1664 zeta1 /\ 
                    Spec.Utils.is_i16b 1664 zeta2 /\ Spec.Utils.is_i16b 1664 zeta3 /\
                    Spec.Utils.is_i16b_array (11207+5*3328) (repr ${vector})"#))]
#[hax_lib::ensures(|_| fstar!(r#"Spec.Utils.is_i16b_array (11207+6*3328) (repr ${vector}_future)"#))]
fn ntt_layer_1_step(vector: &mut SIMD256Vector, zeta0: i16, zeta1: i16, zeta2: i16, zeta3: i16) {
    ntt::ntt_layer_1_step(&mut vector.elements, zeta0, zeta1, zeta2, zeta3);
}

#[inline(always)]
#[hax_lib::fstar::verification_status(lax)]
#[hax_lib::requires(fstar!(r#"Spec.Utils.is_i16b 1664 zeta0 /\ Spec.Utils.is_i16b 1664 zeta1 /\
                    Spec.Utils.is_i16b_array (11207+4*3328) (repr ${vector})"#))]
#[hax_lib::ensures(|_| fstar!(r#"Spec.Utils.is_i16b_array (11207+5*3328) (repr ${vector}_future)"#))]
fn ntt_layer_2_step(vector: &mut SIMD256Vector, zeta0: i16, zeta1: i16) {
    ntt::ntt_layer_2_step(&mut vector.elements, zeta0, zeta1);
}

#[inline(always)]
#[hax_lib::fstar::verification_status(lax)]
#[hax_lib::requires(fstar!(r#"Spec.Utils.is_i16b 1664 zeta /\
                    Spec.Utils.is_i16b_array (11207+3*3328) (repr ${vector})"#))]
#[hax_lib::ensures(|_| fstar!(r#"Spec.Utils.is_i16b_array (11207+4*3328) (repr ${vector}_future)"#))]
fn ntt_layer_3_step(vector: &mut SIMD256Vector, zeta: i16) {
    ntt::ntt_layer_3_step(&mut vector.elements, zeta);
}

#[inline(always)]
#[hax_lib::fstar::verification_status(lax)]
#[hax_lib::requires(fstar!(r#"Spec.Utils.is_i16b 1664 zeta0 /\ Spec.Utils.is_i16b 1664 zeta1 /\ 
                    Spec.Utils.is_i16b 1664 zeta2 /\ Spec.Utils.is_i16b 1664 zeta3  /\
                    Spec.Utils.is_i16b_array (4*3328) (repr ${vector})"#))]
#[hax_lib::ensures(|_| fstar!(r#"Spec.Utils.is_i16b_array 3328 (repr ${vector}_future)"#))]
fn inv_ntt_layer_1_step(
    vector: &mut SIMD256Vector,
    zeta0: i16,
    zeta1: i16,
    zeta2: i16,
    zeta3: i16,
) {
    ntt::inv_ntt_layer_1_step(&mut vector.elements, zeta0, zeta1, zeta2, zeta3);
}

#[inline(always)]
#[hax_lib::fstar::verification_status(lax)]
#[hax_lib::requires(fstar!(r#"Spec.Utils.is_i16b 1664 zeta0 /\ Spec.Utils.is_i16b 1664 zeta1 /\
                    Spec.Utils.is_i16b_array 3328 (repr ${vector})"#))]
#[hax_lib::ensures(|_| fstar!(r#"Spec.Utils.is_i16b_array 3328 (repr ${vector}_future)"#))]
fn inv_ntt_layer_2_step(vector: &mut SIMD256Vector, zeta0: i16, zeta1: i16) {
    ntt::inv_ntt_layer_2_step(&mut vector.elements, zeta0, zeta1);
}

#[inline(always)]
#[hax_lib::fstar::verification_status(lax)]
#[hax_lib::requires(fstar!(r#"Spec.Utils.is_i16b 1664 zeta /\
                    Spec.Utils.is_i16b_array 3328 (repr ${vector})"#))]
#[hax_lib::ensures(|_| fstar!(r#"Spec.Utils.is_i16b_array 3328 (repr ${vector}_future)"#))]
fn inv_ntt_layer_3_step(vector: &mut SIMD256Vector, zeta: i16) {
    ntt::inv_ntt_layer_3_step(&mut vector.elements, zeta);
}

#[inline(always)]
#[hax_lib::fstar::verification_status(lax)]
#[hax_lib::requires(fstar!(r#"Spec.Utils.is_i16b 1664 zeta0 /\ Spec.Utils.is_i16b 1664 zeta1 /\
                    Spec.Utils.is_i16b 1664 zeta2 /\ Spec.Utils.is_i16b 1664 zeta3 /\
                    Spec.Utils.is_i16b_array 3328 (repr ${lhs}) /\
                    Spec.Utils.is_i16b_array 3328 (repr ${rhs})"#))]
#[hax_lib::ensures(|_| fstar!(r#"Spec.Utils.is_i16b_array 3328 (repr ${out}_future)"#))]
fn ntt_multiply(
    lhs: &SIMD256Vector,
    rhs: &SIMD256Vector,
    out: &mut SIMD256Vector,
    zeta0: i16,
    zeta1: i16,
    zeta2: i16,
    zeta3: i16,
) {
    ntt::ntt_multiply(
        &lhs.elements,
        &rhs.elements,
        &mut out.elements,
        zeta0,
        zeta1,
        zeta2,
        zeta3,
    );
}

#[inline(always)]
#[hax_lib::fstar::verification_status(lax)]
#[hax_lib::requires(fstar!(r#"Spec.MLKEM.serialize_pre 1 (repr $vector) /\ Seq.length $out == 2"#))]
#[hax_lib::ensures(|_| fstar!(r#"Seq.length ${out}_future == 2 /\
    (Spec.MLKEM.serialize_pre 1 (repr $vector) ==> 
        Spec.MLKEM.serialize_post 1 (repr $vector) ${out}_future)"#))]
fn serialize_1(vector: &SIMD256Vector, out: &mut [u8]) {
    serialize::serialize_1(&vector.elements, out);
}

#[inline(always)]
#[hax_lib::fstar::verification_status(lax)]
#[hax_lib::requires(bytes.len() == 2)]
#[hax_lib::ensures(|_| fstar!(r#"sz (Seq.length $bytes) =. sz 2 ==> Spec.MLKEM.deserialize_post 1 $bytes (repr ${out}_future)"#))]
fn deserialize_1(bytes: &[u8], out: &mut SIMD256Vector) {
    serialize::deserialize_1(bytes, &mut out.elements);
}

#[inline(always)]
#[hax_lib::fstar::verification_status(lax)]
#[hax_lib::requires(fstar!(r#"Spec.MLKEM.serialize_pre 4 (repr $vector) /\ Seq.length $out == 8"#))]
#[hax_lib::ensures(|_| fstar!(r#"Seq.length ${out}_future == 8 /\
    (Spec.MLKEM.serialize_pre 4 (repr $vector) ==> 
        Spec.MLKEM.serialize_post 4 (repr $vector) ${out}_future)"#))]
fn serialize_4(vector: &SIMD256Vector, out: &mut [u8]) {
    serialize::serialize_4(&vector.elements, out)
}

#[inline(always)]
#[hax_lib::fstar::verification_status(lax)]
#[hax_lib::requires(bytes.len() == 8)]
#[hax_lib::ensures(|_| fstar!(r#"sz (Seq.length $bytes) =. sz 8 ==> Spec.MLKEM.deserialize_post 4 $bytes (repr ${out}_future)"#))]
fn deserialize_4(bytes: &[u8], out: &mut SIMD256Vector) {
    serialize::deserialize_4(bytes, &mut out.elements);
}

#[inline(always)]
#[hax_lib::fstar::verification_status(lax)]
#[hax_lib::requires(fstar!(r#"Spec.MLKEM.serialize_pre 10 (repr $vector) /\ Seq.length $out == 20"#))]
#[hax_lib::ensures(|_| fstar!(r#"Seq.length ${out}_future == 20 /\
    (Spec.MLKEM.serialize_pre 10 (repr $vector) ==> 
        Spec.MLKEM.serialize_post 10 (repr $vector) ${out}_future)"#))]
fn serialize_10(vector: &SIMD256Vector, out: &mut [u8]) {
    serialize::serialize_10(&vector.elements, out);
}

#[inline(always)]
#[hax_lib::fstar::verification_status(lax)]
#[hax_lib::requires(bytes.len() == 20)]
#[hax_lib::ensures(|_| fstar!(r#"sz (Seq.length $bytes) =. sz 20 ==>
    Spec.MLKEM.deserialize_post 10 $bytes (repr ${out}_future)"#))]
fn deserialize_10(bytes: &[u8], out: &mut SIMD256Vector) {
    serialize::deserialize_10(bytes, &mut out.elements);
}

#[inline(always)]
#[hax_lib::fstar::verification_status(lax)]
#[hax_lib::requires(fstar!(r#"Spec.MLKEM.serialize_pre 12 (repr $vector) /\ Seq.length $out == 24"#))]
#[hax_lib::ensures(|_| fstar!(r#"Seq.length ${out}_future == 24 /\
    (Spec.MLKEM.serialize_pre 12 (repr $vector) ==> 
        Spec.MLKEM.serialize_post 12 (repr $vector) ${out}_future)"#))]
fn serialize_12(vector: &SIMD256Vector, out: &mut [u8]) {
    serialize::serialize_12(&vector.elements, out);
}

#[inline(always)]
#[hax_lib::fstar::verification_status(lax)]
#[hax_lib::requires(bytes.len() == 24)]
#[hax_lib::ensures(|_| fstar!(r#"sz (Seq.length $bytes) =. sz 24 ==> Spec.MLKEM.deserialize_post 12 $bytes (repr ${out}_future)"#))]
fn deserialize_12(bytes: &[u8], out: &mut SIMD256Vector) {
    serialize::deserialize_12(bytes, &mut out.elements);
}

#[cfg(hax)]
impl Repr for SIMD256Vector {
    fn repr(&self) -> [i16; 16] {
        let mut out = [0i16; 16];
        vec_to_i16_array(&self, &mut out);
        out
    }
}

#[cfg(any(eurydice, not(hax)))]
impl Repr for SIMD256Vector {}

#[inline(always)]
#[hax_lib::requires(array.len() >= 32)]
pub(super) fn from_bytes(array: &[u8], out: &mut Vec256) {
    *out = mm256_loadu_si256_u8(&array[0..32]);
}

#[inline(always)]
#[hax_lib::fstar::verification_status(lax)]
#[hax_lib::requires(bytes.len() >= 32)]
#[hax_lib::ensures(|_| future(bytes).len() == bytes.len())]
pub(super) fn to_bytes(x: SIMD256Vector, bytes: &mut [u8]) {
    mm256_storeu_si256_u8(&mut bytes[0..32], x.elements)
}

#[hax_lib::attributes]
impl Operations for SIMD256Vector {
    #[inline(always)]
    #[requires(true)]
    #[ensures(|result| result.repr() == [0i16; 16])]
    fn ZERO() -> Self {
        vec_zero()
    }

    #[inline(always)]
    #[requires(array.len() == 16)]
    #[ensures(|_| future(out).repr() == array)]
    fn from_i16_array(array: &[i16], out: &mut Self) {
        vec_from_i16_array(array, out);
    }

    #[inline(always)]
    #[requires(out.len() == 16)]
    #[ensures(|_| future(out) == x.repr())]
    fn to_i16_array(x: &Self, out: &mut [i16]) {
        vec_to_i16_array(x, out);
    }

    #[inline(always)]
    #[requires(array.len() >= 32)]
    fn from_bytes(array: &[u8], out: &mut Self) {
        from_bytes(array, &mut out.elements);
    }

    #[inline(always)]
    #[requires(bytes.len() >= 32)]
    #[ensures(|_| future(bytes).len() == bytes.len())]
    fn to_bytes(x: Self, bytes: &mut [u8]) {
        to_bytes(x, bytes)
    }

    #[inline(always)]
    #[requires(spec::add_pre(&lhs.repr(), &rhs.repr()))]
    #[ensures(|_| spec::add_post(&lhs.repr(), &rhs.repr(), &future(lhs).repr()))]
    fn add(lhs: &mut Self, rhs: &Self) {
        hax_lib::fstar!(
            r#"reveal_opaque (`%Libcrux_ml_kem.Vector.Traits.Spec.add_post) (Libcrux_ml_kem.Vector.Traits.Spec.add_post)"#
        );
        arithmetic::add(&mut lhs.elements, &rhs.elements);
    }

    #[inline(always)]
    #[requires(spec::sub_pre(&lhs.repr(), &rhs.repr()))]
    #[ensures(|_| spec::sub_post(&lhs.repr(), &rhs.repr(), &future(lhs).repr()))]
    fn sub(lhs: &mut Self, rhs: &Self) {
        arithmetic::sub(&mut lhs.elements, &rhs.elements);
    }

    #[inline(always)]
    #[requires(spec::negate_pre(&vec.repr()))]
    #[ensures(|_| spec::negate_post(&vec.repr(), &future(vec).repr()))]
    fn negate(vec: &mut Self) {
        arithmetic::negate(&mut vec.elements);
    }

    #[inline(always)]
    #[requires(spec::multiply_by_constant_pre(&vec.repr(), c))]
    #[ensures(|_| spec::multiply_by_constant_post(&vec.repr(), c, &future(vec).repr()))]
    fn multiply_by_constant(vec: &mut Self, c: i16) {
        arithmetic::multiply_by_constant(&mut vec.elements, c);
    }

    #[inline(always)]
    #[requires(true)]
    #[ensures(|_| spec::bitwise_and_with_constant_constant_post(&vec.repr(), c, &future(vec).repr()))]
    fn bitwise_and_with_constant(vec: &mut Self, c: i16) {
        vec.elements = bitwise_and_with_constant(vec.elements, c);
    }

    #[inline(always)]
    #[requires(SHIFT_BY >= 0 && SHIFT_BY < 16)]
    #[ensures(|_| spec::shift_right_post(&vec.repr(), SHIFT_BY, &future(vec).repr()))]
    fn shift_right<const SHIFT_BY: i32>(vec: &mut Self) {
        vec.elements = shift_right::<SHIFT_BY>(vec.elements);
    }

    #[inline(always)]
    #[requires(spec::cond_subtract_3329_pre(&vec.repr()))]
    #[ensures(|_| spec::cond_subtract_3329_post(&vec.repr(), &future(vec).repr()))]
    fn cond_subtract_3329(vec: &mut Self) {
        cond_subtract_3329(vec)
    }

    #[inline(always)]
    #[requires(spec::barrett_reduce_pre(&vec.repr()))]
    #[ensures(|_| spec::barrett_reduce_post(&vec.repr(), &future(vec).repr()))]
    fn barrett_reduce(vec: &mut Self) {
        arithmetic::barrett_reduce(&mut vec.elements);
    }

    #[inline(always)]
    #[requires(spec::montgomery_multiply_by_constant_pre(&vec.repr(), c))]
    #[ensures(|_| spec::montgomery_multiply_by_constant_post(&vec.repr(), c, &future(vec).repr()))]
    fn montgomery_multiply_by_constant(vec: &mut Self, c: i16) {
        arithmetic::montgomery_multiply_by_constant(&mut vec.elements, c);
    }

    #[inline(always)]
    #[requires(spec::to_unsigned_representative_pre(&vec.repr()))]
    #[ensures(|result| spec::to_unsigned_representative_post(&vec.repr(), &result.repr()))]
    fn to_unsigned_representative(vec: Self) -> Self {
        Self {
            elements: arithmetic::to_unsigned_representative(vec.elements),
        }
    }

    #[inline(always)]
    #[requires(spec::compress_1_pre(&vec.repr()))]
    #[ensures(|_| spec::compress_1_post(&vec.repr(), &future(vec).repr()))]
    fn compress_1(vec: &mut Self) {
        compress_1(vec);
    }

    #[inline(always)]
    #[requires(spec::compress_pre(&vec.repr(), COEFFICIENT_BITS))]
    #[ensures(|_| spec::compress_post(&vec.repr(), COEFFICIENT_BITS, &future(vec).repr()))]
    fn compress<const COEFFICIENT_BITS: i32>(vec: &mut Self) {
        compress::<COEFFICIENT_BITS>(vec);
    }

    #[inline(always)]
    #[hax_lib::requires(spec::decompress_1_pre(&vec.repr()))]
    fn decompress_1(vec: Self) -> Self {
        Self {
            elements: compress::decompress_1(vec.elements),
        }
    }

    #[inline(always)]
    #[requires(spec::decompress_ciphertext_coefficient_pre(&vec.repr(), COEFFICIENT_BITS))]
    fn decompress_ciphertext_coefficient<const COEFFICIENT_BITS: i32>(vec: &mut Self) {
        compress::decompress_ciphertext_coefficient::<COEFFICIENT_BITS>(&mut vec.elements);
    }

    #[inline(always)]
    #[requires(spec::ntt_layer_1_step_pre(&vec.repr(), zeta0, zeta1, zeta2, zeta3))]
    #[ensures(|_| spec::ntt_layer_1_step_post(&vec.repr(), zeta0, zeta1, zeta2, zeta3, &future(vec).repr()))]
    fn ntt_layer_1_step(vec: &mut Self, zeta0: i16, zeta1: i16, zeta2: i16, zeta3: i16) {
        ntt_layer_1_step(vec, zeta0, zeta1, zeta2, zeta3);
    }

    #[inline(always)]
    #[requires(spec::ntt_layer_2_step_pre(&vec.repr(), zeta0, zeta1))]
    #[ensures(|_| spec::ntt_layer_2_step_post(&vec.repr(), zeta0, zeta1, &future(vec).repr()))]
    fn ntt_layer_2_step(vec: &mut Self, zeta0: i16, zeta1: i16) {
        ntt_layer_2_step(vec, zeta0, zeta1);
    }

    #[inline(always)]
    #[requires(spec::ntt_layer_3_step_pre(&vec.repr(), zeta0))]
    #[ensures(|_| spec::ntt_layer_3_step_post(&vec.repr(), zeta0, &future(vec).repr()))]
    fn ntt_layer_3_step(vec: &mut Self, zeta0: i16) {
        ntt_layer_3_step(vec, zeta0);
    }

    #[inline(always)]
    #[requires(spec::inv_ntt_layer_1_step_pre(&vec.repr(), zeta0, zeta1, zeta2, zeta3))]
    #[ensures(|_| spec::inv_ntt_layer_1_step_post(&vec.repr(), zeta0, zeta1, zeta2, zeta3, &future(vec).repr()))]
    fn inv_ntt_layer_1_step(vec: &mut Self, zeta0: i16, zeta1: i16, zeta2: i16, zeta3: i16) {
        inv_ntt_layer_1_step(vec, zeta0, zeta1, zeta2, zeta3);
    }

    #[inline(always)]
    #[requires(spec::inv_ntt_layer_2_step_pre(&vec.repr(), zeta0, zeta1))]
    #[ensures(|_| spec::inv_ntt_layer_2_step_post(&vec.repr(), zeta0, zeta1, &future(vec).repr()))]
    fn inv_ntt_layer_2_step(vec: &mut Self, zeta0: i16, zeta1: i16) {
        inv_ntt_layer_2_step(vec, zeta0, zeta1);
    }

    #[inline(always)]
    #[requires(spec::inv_ntt_layer_3_step_pre(&vec.repr(), zeta0))]
    #[ensures(|_| spec::inv_ntt_layer_3_step_post(&vec.repr(), zeta0, &future(vec).repr()))]
    fn inv_ntt_layer_3_step(vec: &mut Self, zeta0: i16) {
        inv_ntt_layer_3_step(vec, zeta0);
    }

    #[inline(always)]
    #[requires(spec::ntt_multiply_pre(&lhs.repr(), &rhs.repr(), &out.repr(),zeta0, zeta1, zeta2, zeta3))]
    #[ensures(|_| spec::ntt_multiply_post(&lhs.repr(), &rhs.repr(), &out.repr(),zeta0, zeta1, zeta2, zeta3, &future(out).repr()))]
    fn ntt_multiply(
        lhs: &Self,
        rhs: &Self,
        out: &mut Self,
        zeta0: i16,
        zeta1: i16,
        zeta2: i16,
        zeta3: i16,
    ) {
        ntt_multiply(lhs, rhs, out, zeta0, zeta1, zeta2, zeta3);
    }

    #[inline(always)]
    #[requires(spec::serialize_1_pre(&vec.repr(), &out))]
    #[ensures(|_| spec::serialize_1_post(&vec.repr(), &out, &future(out)))]
    fn serialize_1(vec: &Self, out: &mut [u8]) {
        debug_assert!(out.len() == 2);
        serialize_1(vec, out);
    }

    #[inline(always)]
    #[requires(spec::deserialize_1_pre(&input, &out.repr()))]
    #[ensures(|_| spec::deserialize_1_post(&input, &out.repr(), &future(out).repr()))]
    fn deserialize_1(input: &[u8], out: &mut Self) {
        deserialize_1(input, out);
    }

    #[inline(always)]
    #[requires(spec::serialize_4_pre(&vec.repr(), &out))]
    #[ensures(|_| spec::serialize_4_post(&vec.repr(), &out, &future(out)))]
    fn serialize_4(vec: &Self, out: &mut [u8]) {
        debug_assert!(out.len() == 8);
        serialize_4(vec, out);
    }

    #[inline(always)]
    #[requires(spec::deserialize_4_pre(&input, &out.repr()))]
    #[ensures(|_| spec::deserialize_4_post(&input, &out.repr(), &future(out).repr()))]
    fn deserialize_4(input: &[u8], out: &mut Self) {
        deserialize_4(input, out);
    }

    #[inline(always)]
    #[requires(out.len() == 10)]
    fn serialize_5(vec: &Self, out: &mut [u8]) {
        debug_assert!(out.len() == 10);
        serialize::serialize_5(&vec.elements, out);
    }

    #[inline(always)]
    #[requires(input.len() == 10)]
    fn deserialize_5(input: &[u8], out: &mut Self) {
        serialize::deserialize_5(input, &mut out.elements);
    }

    #[inline(always)]
    #[requires(spec::serialize_10_pre(&vec.repr(), &out))]
    #[ensures(|_| spec::serialize_10_post(&vec.repr(), &out, &future(out)))]
    fn serialize_10(vec: &Self, out: &mut [u8]) {
        debug_assert!(out.len() == 20);
        serialize_10(vec, out);
    }

    #[inline(always)]
    #[requires(spec::deserialize_10_pre(&input, &out.repr()))]
    #[ensures(|_| spec::deserialize_10_post(&input, &out.repr(), &future(out).repr()))]
    fn deserialize_10(input: &[u8], out: &mut Self) {
        deserialize_10(input, out);
    }

    #[inline(always)]
    #[requires(out.len() == 22)]
    fn serialize_11(vec: &Self, out: &mut [u8]) {
        debug_assert!(out.len() == 22);
        serialize::serialize_11(&vec.elements, out);
    }

    #[inline(always)]
    #[requires(input.len() == 22)]
    fn deserialize_11(input: &[u8], out: &mut Self) {
        serialize::deserialize_11(input, &mut out.elements);
    }

    #[inline(always)]
    #[requires(spec::serialize_12_pre(&vec.repr(), &out))]
    #[ensures(|_| spec::serialize_12_post(&vec.repr(), &out, &future(out)))]
    fn serialize_12(vec: &Self, out: &mut [u8]) {
        debug_assert!(out.len() == 24);
        serialize_12(vec, out);
    }

    #[inline(always)]
    #[requires(spec::deserialize_12_pre(&input, &out.repr()))]
    #[ensures(|_| spec::deserialize_12_post(&input, &out.repr(), &future(out).repr()))]
    fn deserialize_12(input: &[u8], out: &mut Self) {
        deserialize_12(input, out);
    }

    #[inline(always)]
    #[requires(input.len() == 24 && out.len() == 16)]
    #[ensures(|result| result <= 16 && future(out).len() == 16)]
    fn rej_sample(input: &[u8], out: &mut [i16]) -> usize {
        sampling::rejection_sample(input, out)
    }
}
