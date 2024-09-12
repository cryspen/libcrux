use super::Operations;
mod arithmetic;
mod compress;
mod ntt;
mod sampling;
mod serialize;
mod vector_type;

use arithmetic::*;
use compress::*;
use ntt::*;
use sampling::*;
use serialize::*;
use vector_type::*;

pub(crate) use vector_type::PortableVector;

#[cfg(hax)]
impl crate::vector::traits::Repr for PortableVector {
    fn repr(x: Self) -> [i16; 16] {
        to_i16_array(x)
    }
}

#[hax_lib::attributes]
#[hax_lib::fstar::options("--z3rlimit 300")]
impl Operations for PortableVector {
    #[ensures(|out| fstar!("impl.f_repr out == Seq.create 16 0s"))]
    fn ZERO() -> Self {
        zero()
    }

    #[requires(array.len() == 16)]
    #[ensures(|out| fstar!("impl.f_repr out == $array"))]
    fn from_i16_array(array: &[i16]) -> Self {
        from_i16_array(array)
    }

    #[ensures(|out| fstar!("out == impl.f_repr $x"))]
    fn to_i16_array(x: Self) -> [i16; 16] {
        to_i16_array(x)
    }

    #[requires(fstar!("forall i. i < 16 ==> 
        Spec.Utils.is_intb (pow2 15) (v (Seq.index ${lhs}.f_elements i) + v (Seq.index ${rhs}.f_elements i))"))]
    #[ensures(|result| fstar!("forall i. i < 16 ==> 
        (v (Seq.index ${result}.f_elements i) == 
         v (Seq.index ${lhs}.f_elements i) + v (Seq.index ${rhs}.f_elements i))"))]
    fn add(lhs: Self, rhs: &Self) -> Self {
        add(lhs, rhs)
    }

    #[requires(fstar!("forall i. i < 16 ==> 
        Spec.Utils.is_intb (pow2 15) (v (Seq.index ${lhs}.f_elements i) - v (Seq.index ${rhs}.f_elements i))"))]
    #[ensures(|result| fstar!("forall i. i < 16 ==> 
        (v (Seq.index ${result}.f_elements i) == 
         v (Seq.index ${lhs}.f_elements i) - v (Seq.index ${rhs}.f_elements i))"))]
    fn sub(lhs: Self, rhs: &Self) -> Self {
        sub(lhs, rhs)
    }

    #[requires(fstar!("forall i. i < 16 ==> 
        Spec.Utils.is_intb (pow2 31) (v (Seq.index ${vec}.f_elements i) * v c)"))]
    #[ensures(|result| fstar!("forall i. i < 16 ==> 
        (v (Seq.index ${result}.f_elements i) == 
        v (Seq.index ${vec}.f_elements i) * v c)"))]
    fn multiply_by_constant(vec: Self, c: i16) -> Self {
        multiply_by_constant(vec, c)
    }

    #[ensures(|out| fstar!("impl.f_repr out == Spec.Utils.map_array (fun x -> x &. c) (impl.f_repr $v)"))]
    fn bitwise_and_with_constant(v: Self, c: i16) -> Self {
        bitwise_and_with_constant(v, c)
    }

    #[requires(SHIFT_BY >= 0 && SHIFT_BY < 16)]
    #[ensures(|out| fstar!("(v_SHIFT_BY >=. 0l /\\ v_SHIFT_BY <. 16l) ==> impl.f_repr out == Spec.Utils.map_array (fun x -> x >>! ${SHIFT_BY}) (impl.f_repr $v)"))]
    fn shift_right<const SHIFT_BY: i32>(v: Self) -> Self {
        shift_right::<{ SHIFT_BY }>(v)
    }

    #[requires(fstar!("Spec.Utils.is_i16b_array (pow2 12 - 1) (impl.f_repr $v)"))]
    #[ensures(|out| fstar!("impl.f_repr out == Spec.Utils.map_array (fun x -> if x >=. 3329s then x -! 3329s else x) (impl.f_repr $v)"))]
    fn cond_subtract_3329(v: Self) -> Self {
        cond_subtract_3329(v)
    }

    #[requires(fstar!("Spec.Utils.is_i16b_array 28296 (impl.f_repr ${v})"))]
    fn barrett_reduce(v: Self) -> Self {
        barrett_reduce(v)
    }

    #[requires(fstar!("Spec.Utils.is_i16b 3328 $r"))]
    fn montgomery_multiply_by_constant(v: Self, r: i16) -> Self {
        montgomery_multiply_by_constant(v, r)
    }

    fn compress_1(v: Self) -> Self {
        compress_1(v)
    }

    #[requires(COEFFICIENT_BITS == 4 || COEFFICIENT_BITS == 5 ||
               COEFFICIENT_BITS == 10 || COEFFICIENT_BITS == 11)]
    fn compress<const COEFFICIENT_BITS: i32>(v: Self) -> Self {
        compress::<COEFFICIENT_BITS>(v)
    }

    #[requires(COEFFICIENT_BITS == 4 || COEFFICIENT_BITS == 5 ||
               COEFFICIENT_BITS == 10 || COEFFICIENT_BITS == 11)]
    fn decompress_ciphertext_coefficient<const COEFFICIENT_BITS: i32>(v: Self) -> Self {
        decompress_ciphertext_coefficient::<COEFFICIENT_BITS>(v)
    }

    #[requires(fstar!("Spec.Utils.is_i16b 1664 zeta0 /\\ Spec.Utils.is_i16b 1664 zeta1 /\\ Spec.Utils.is_i16b 1664 zeta2 /\\ Spec.Utils.is_i16b 1664 zeta3"))]
    fn ntt_layer_1_step(a: Self, zeta0: i16, zeta1: i16, zeta2: i16, zeta3: i16) -> Self {
        ntt_layer_1_step(a, zeta0, zeta1, zeta2, zeta3)
    }

    #[requires(fstar!("Spec.Utils.is_i16b 1664 zeta0 /\\ Spec.Utils.is_i16b 1664 zeta1"))]
    fn ntt_layer_2_step(a: Self, zeta0: i16, zeta1: i16) -> Self {
        ntt_layer_2_step(a, zeta0, zeta1)
    }

    #[requires(fstar!("Spec.Utils.is_i16b 1664 zeta"))]
    fn ntt_layer_3_step(a: Self, zeta: i16) -> Self {
        ntt_layer_3_step(a, zeta)
    }

    #[requires(fstar!("Spec.Utils.is_i16b 1664 zeta0 /\\ Spec.Utils.is_i16b 1664 zeta1 /\\ Spec.Utils.is_i16b 1664 zeta2 /\\ Spec.Utils.is_i16b 1664 zeta3"))]
    fn inv_ntt_layer_1_step(a: Self, zeta0: i16, zeta1: i16, zeta2: i16, zeta3: i16) -> Self {
        inv_ntt_layer_1_step(a, zeta0, zeta1, zeta2, zeta3)
    }

    #[requires(fstar!("Spec.Utils.is_i16b 1664 zeta0 /\\ Spec.Utils.is_i16b 1664 zeta1"))]
    fn inv_ntt_layer_2_step(a: Self, zeta0: i16, zeta1: i16) -> Self {
        inv_ntt_layer_2_step(a, zeta0, zeta1)
    }

    #[requires(fstar!("Spec.Utils.is_i16b 1664 zeta"))]
    fn inv_ntt_layer_3_step(a: Self, zeta: i16) -> Self {
        inv_ntt_layer_3_step(a, zeta)
    }

    fn ntt_multiply(
        lhs: &Self,
        rhs: &Self,
        zeta0: i16,
        zeta1: i16,
        zeta2: i16,
        zeta3: i16,
    ) -> Self {
        ntt_multiply(lhs, rhs, zeta0, zeta1, zeta2, zeta3)
    }

    #[requires(fstar!("Spec.MLKEM.serialize_pre 1 (impl.f_repr $a)"))]
    #[ensures(|out| fstar!("Spec.MLKEM.serialize_pre 1 (impl.f_repr $a) ==> Spec.MLKEM.serialize_post 1 (impl.f_repr $a) $out"))]
    fn serialize_1(a: Self) -> [u8; 2] {
        hax_lib::fstar!("Libcrux_ml_kem.Vector.Portable.Serialize.serialize_1_lemma $a");
        serialize_1(a)
    }

    #[requires(a.len() == 2)]
    #[ensures(|out| fstar!("sz (Seq.length $a) =. sz 2 ==> Spec.MLKEM.deserialize_post 1 $a (impl.f_repr $out)"))]
    fn deserialize_1(a: &[u8]) -> Self {
        hax_lib::fstar!("Libcrux_ml_kem.Vector.Portable.Serialize.deserialize_1_lemma $a");
        deserialize_1(a)
    }

    #[requires(fstar!("Spec.MLKEM.serialize_pre 4 (impl.f_repr $a)"))]
    #[ensures(|out| fstar!("Spec.MLKEM.serialize_pre 4 (impl.f_repr $a) ==> Spec.MLKEM.serialize_post 4 (impl.f_repr $a) $out"))]
    fn serialize_4(a: Self) -> [u8; 8] {
        hax_lib::fstar!("Libcrux_ml_kem.Vector.Portable.Serialize.serialize_4_lemma $a");
        serialize_4(a)
    }

    #[requires(a.len() == 8)]
    #[ensures(|out| fstar!("sz (Seq.length $a) =. sz 8 ==> Spec.MLKEM.deserialize_post 4 $a (impl.f_repr $out)"))]
    fn deserialize_4(a: &[u8]) -> Self {
        hax_lib::fstar!("Libcrux_ml_kem.Vector.Portable.Serialize.deserialize_4_lemma $a");
        deserialize_4(a)
    }

    fn serialize_5(a: Self) -> [u8; 10] {
        serialize_5(a)
    }

    #[requires(a.len() == 10)]
    fn deserialize_5(a: &[u8]) -> Self {
        deserialize_5(a)
    }

    #[requires(fstar!("Spec.MLKEM.serialize_pre 10 (impl.f_repr $a)"))]
    #[ensures(|out| fstar!("Spec.MLKEM.serialize_pre 10 (impl.f_repr $a) ==> Spec.MLKEM.serialize_post 10 (impl.f_repr $a) $out"))]
    fn serialize_10(a: Self) -> [u8; 20] {
        hax_lib::fstar!("Libcrux_ml_kem.Vector.Portable.Serialize.serialize_10_lemma $a");
        serialize_10(a)
    }

    #[requires(a.len() == 20)]
    #[ensures(|out| fstar!("sz (Seq.length $a) =. sz 20 ==> Spec.MLKEM.deserialize_post 10 $a (impl.f_repr $out)"))]
    fn deserialize_10(a: &[u8]) -> Self {
        hax_lib::fstar!("Libcrux_ml_kem.Vector.Portable.Serialize.deserialize_10_lemma $a");
        deserialize_10(a)
    }

    fn serialize_11(a: Self) -> [u8; 22] {
        serialize_11(a)
    }

    #[requires(a.len() == 22)]
    fn deserialize_11(a: &[u8]) -> Self {
        deserialize_11(a)
    }

    #[requires(fstar!("Spec.MLKEM.serialize_pre 12 (impl.f_repr $a)"))]
    #[ensures(|out| fstar!("Spec.MLKEM.serialize_pre 12 (impl.f_repr $a) ==> Spec.MLKEM.serialize_post 12 (impl.f_repr $a) $out"))]
    fn serialize_12(a: Self) -> [u8; 24] {
        hax_lib::fstar!("Libcrux_ml_kem.Vector.Portable.Serialize.serialize_12_lemma $a");
        serialize_12(a)
    }

    #[requires(a.len() == 24)]
    #[ensures(|out| fstar!("sz (Seq.length $a) =. sz 24 ==> Spec.MLKEM.deserialize_post 12 $a (impl.f_repr $out)"))]
    fn deserialize_12(a: &[u8]) -> Self {
        hax_lib::fstar!("Libcrux_ml_kem.Vector.Portable.Serialize.deserialize_12_lemma $a");
        deserialize_12(a)
    }

    fn rej_sample(a: &[u8], out: &mut [i16]) -> usize {
        rej_sample(a, out)
    }
}
