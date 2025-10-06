use super::Operations;
use libcrux_secrets::*;

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
use vector_type::*;

pub(crate) use vector_type::PortableVector;

#[cfg(hax)]
impl crate::vector::traits::Repr for PortableVector {
    fn repr(&self) -> [i16; 16] {
        let mut out = [0i16; 16];
        to_i16_array(self, &mut out);
        out
    }
}

#[cfg(any(eurydice, not(hax)))]
impl crate::vector::traits::Repr for PortableVector {}

#[hax_lib::requires(fstar!(r#"Spec.MLKEM.serialize_pre 1 (impl.f_repr $a) /\ Seq.length $out == 2"#))]
#[hax_lib::ensures(|out| fstar!(r#"Seq.length ${out}_future == 2 /\
    (Spec.MLKEM.serialize_pre 1 (impl.f_repr $a) ==> 
            Spec.MLKEM.serialize_post 1 (impl.f_repr $a) ${out}_future)"#))]
fn serialize_1(a: &PortableVector, out: &mut [u8]) {
    hax_lib::fstar!(
        r#"assert (forall i. Rust_primitives.bounded (Seq.index ${a}.f_elements i) 1)"#
    );
    hax_lib::fstar!(r#"Libcrux_ml_kem.Vector.Portable.Serialize.serialize_1_lemma $a $out"#);
    serialize::serialize_1(a, out)
}

#[hax_lib::requires(a.len() == 2)]
#[hax_lib::ensures(|_| fstar!(r#"Seq.length $a == 2 ==> 
    Spec.MLKEM.deserialize_post 1 $a (impl.f_repr ${out}_future)"#))]
fn deserialize_1(a: &[u8], out: &mut PortableVector) {
    hax_lib::fstar!(r#"Libcrux_ml_kem.Vector.Portable.Serialize.deserialize_1_lemma $a $out"#);
    serialize::deserialize_1(a.classify_ref(), out)
}

#[hax_lib::requires(fstar!(r#"Spec.MLKEM.serialize_pre 4 (impl.f_repr $a) /\ Seq.length $out == 8"#))]
#[hax_lib::ensures(|_| fstar!(r#"Seq.length ${out}_future == 8 /\
    (Spec.MLKEM.serialize_pre 4 (impl.f_repr $a) ==> 
        Spec.MLKEM.serialize_post 4 (impl.f_repr $a) ${out}_future)"#))]
fn serialize_4(a: &PortableVector, out: &mut [u8]) {
    hax_lib::fstar!(
        r#"assert (forall i. Rust_primitives.bounded (Seq.index ${a}.f_elements i) 4)"#
    );
    hax_lib::fstar!(r#"Libcrux_ml_kem.Vector.Portable.Serialize.serialize_4_lemma $a $out"#);
    serialize::serialize_4(a, out)
}

#[hax_lib::requires(a.len() == 8)]
#[hax_lib::ensures(|out| fstar!(r#"Seq.length $a == 8 ==> 
    Spec.MLKEM.deserialize_post 4 $a (impl.f_repr ${out}_future)"#))]
fn deserialize_4(a: &[u8], out: &mut PortableVector) {
    hax_lib::fstar!(r#"Libcrux_ml_kem.Vector.Portable.Serialize.deserialize_4_lemma $a $out"#);
    serialize::deserialize_4(a.classify_ref(), out)
}

fn serialize_5(a: &PortableVector, out: &mut [u8]) {
    serialize::serialize_5(a, out)
}

#[hax_lib::requires(a.len() == 10)]
fn deserialize_5(a: &[u8], out: &mut PortableVector) {
    serialize::deserialize_5(a.classify_ref(), out)
}

#[hax_lib::requires(fstar!(r#"Spec.MLKEM.serialize_pre 10 (impl.f_repr $a) /\ Seq.length $out == 20"#))]
#[hax_lib::ensures(|out| fstar!(r#"Seq.length ${out}_future == 20 /\
    (Spec.MLKEM.serialize_pre 10 (impl.f_repr $a) ==> 
        Spec.MLKEM.serialize_post 10 (impl.f_repr $a) ${out}_future)"#))]
fn serialize_10(a: &PortableVector, out: &mut [u8]) {
    hax_lib::fstar!(r#"Libcrux_ml_kem.Vector.Portable.Serialize.serialize_10_lemma $a $out"#);
    serialize::serialize_10(a, out)
}

#[hax_lib::requires(a.len() == 20)]
#[hax_lib::ensures(|_| fstar!(r#"Seq.length $a == 20 ==> 
    Spec.MLKEM.deserialize_post 10 $a (impl.f_repr ${out}_future)"#))]
fn deserialize_10(a: &[u8], out: &mut PortableVector) {
    hax_lib::fstar!(r#"Libcrux_ml_kem.Vector.Portable.Serialize.deserialize_10_lemma $a $out"#);
    serialize::deserialize_10(a.classify_ref(), out)
}

fn serialize_11(a: &PortableVector, out: &mut [u8]) {
    serialize::serialize_11(a, out)
}

#[hax_lib::requires(a.len() == 22)]
fn deserialize_11(a: &[u8], out: &mut PortableVector) {
    serialize::deserialize_11(a.classify_ref(), out)
}

#[hax_lib::requires(fstar!(r#"Spec.MLKEM.serialize_pre 12 (impl.f_repr $a) /\ Seq.length $out == 24"#))]
#[hax_lib::ensures(|out| fstar!(r#"Seq.length ${out}_future == 24 /\
    (Spec.MLKEM.serialize_pre 12 (impl.f_repr $a) ==> 
        Spec.MLKEM.serialize_post 12 (impl.f_repr $a) ${out}_future)"#))]
fn serialize_12(a: &PortableVector, out: &mut [u8]) {
    hax_lib::fstar!(r#"Libcrux_ml_kem.Vector.Portable.Serialize.serialize_12_lemma $a $out"#);
    serialize::serialize_12(a, out)
}

#[hax_lib::requires(a.len() == 24)]
#[hax_lib::ensures(|out| fstar!(r#"Seq.length $a == 24 ==> 
    Spec.MLKEM.deserialize_post 12 $a (impl.f_repr ${out}_future)"#))]
fn deserialize_12(a: &[u8], out: &mut PortableVector) {
    hax_lib::fstar!(r#"Libcrux_ml_kem.Vector.Portable.Serialize.deserialize_12_lemma $a $out"#);
    serialize::deserialize_12(a.classify_ref(), out)
}

#[hax_lib::fstar::before(r#"#push-options "--z3rlimit 400 --split_queries always""#)]
#[hax_lib::fstar::after(r#"#pop-options"#)]
#[hax_lib::attributes]
impl Operations for PortableVector {
    #[ensures(|out| fstar!(r#"impl.f_repr out == Seq.create 16 (mk_i16 0)"#))]
    fn ZERO() -> Self {
        zero()
    }

    #[requires(array.len() == 16)]
    #[ensures(|_| fstar!(r#"impl.f_repr ${out}_future == $array"#))]
    fn from_i16_array(array: &[i16], out: &mut Self) {
        from_i16_array(array.classify_ref(), out)
    }

    #[requires(out.len() == 16)]
    #[ensures(|_| fstar!(r#"${out}_future == impl.f_repr $x"#))]
    fn to_i16_array(x: &Self, out: &mut [i16]) {
        to_i16_array(x, out)
    }

    #[requires(array.len() >= 32)]
    fn from_bytes(array: &[u8], out: &mut Self) {
        from_bytes(array.classify_ref(), out)
    }

    #[requires(bytes.len() >= 32)]
    #[ensures(|_| future(bytes).len() == bytes.len())]
    fn to_bytes(x: Self, bytes: &mut [u8]) {
        #[cfg(not(hax))]
        to_bytes(x, classify_mut_slice(bytes));

        // hax does not support &mut returning functions like `classify_mut_slice`
        #[cfg(hax)]
        to_bytes(x, bytes);
    }

    #[requires(fstar!(r#"forall i. i < 16 ==> 
        Spec.Utils.is_intb (pow2 15 - 1) (v (Seq.index ${lhs}.f_elements i) + v (Seq.index ${rhs}.f_elements i))"#))]
    #[ensures(|_| fstar!(r#"forall i. i < 16 ==> 
        (v (Seq.index ${lhs}_future.f_elements i) == 
         v (Seq.index ${lhs}.f_elements i) + v (Seq.index ${rhs}.f_elements i))"#))]
    fn add(lhs: &mut Self, rhs: &Self) {
        add(lhs, rhs)
    }

    #[requires(fstar!(r#"forall i. i < 16 ==> 
        Spec.Utils.is_intb (pow2 15 - 1) (v (Seq.index ${lhs}.f_elements i) - v (Seq.index ${rhs}.f_elements i))"#))]
    #[ensures(|_| fstar!(r#"forall i. i < 16 ==> 
        (v (Seq.index ${lhs}_future.f_elements i) == 
         v (Seq.index ${lhs}.f_elements i) - v (Seq.index ${rhs}.f_elements i))"#))]
    fn sub(lhs: &mut Self, rhs: &Self) {
        sub(lhs, rhs)
    }

    #[requires(fstar!(r#"forall i. i < 16 ==> 
        Spec.Utils.is_intb (pow2 15 - 1) (v (Seq.index ${vec}.f_elements i))"#))]
    #[ensures(|_| fstar!(r#"forall i. i < 16 ==> 
        v (Seq.index ${vec}_future.f_elements i) == 
        - (v (Seq.index ${vec}.f_elements i))"#))]
    fn negate(vec: &mut Self) {
        negate(vec)
    }

    #[requires(fstar!(r#"forall i. i < 16 ==> 
        Spec.Utils.is_intb (pow2 15 - 1) (v (Seq.index ${vec}.f_elements i) * v c)"#))]
    #[ensures(|_| fstar!(r#"forall i. i < 16 ==> 
        (v (Seq.index ${vec}_future.f_elements i) == 
        v (Seq.index ${vec}.f_elements i) * v c)"#))]
    fn multiply_by_constant(vec: &mut Self, c: i16) {
        multiply_by_constant(vec, c)
    }

    #[ensures(|_| fstar!(r#"impl.f_repr ${vec}_future == Spec.Utils.map_array (fun x -> x &. c) (impl.f_repr $vec)"#))]
    fn bitwise_and_with_constant(vec: &mut Self, c: i16) {
        bitwise_and_with_constant(vec, c)
    }

    #[requires(SHIFT_BY >= 0 && SHIFT_BY < 16)]
    #[ensures(|_| fstar!(r#"(v_SHIFT_BY >=. (mk_i32 0) /\ v_SHIFT_BY <. (mk_i32 16)) ==> impl.f_repr ${vec}_future == Spec.Utils.map_array (fun x -> x >>! ${SHIFT_BY}) (impl.f_repr $vec)"#))]
    fn shift_right<const SHIFT_BY: i32>(vec: &mut Self) {
        shift_right::<{ SHIFT_BY }>(vec)
    }

    #[requires(fstar!(r#"Spec.Utils.is_i16b_array (pow2 12 - 1) (impl.f_repr $vec)"#))]
    #[ensures(|_| fstar!(r#"impl.f_repr ${vec}_future == Spec.Utils.map_array (fun x -> if x >=. (mk_i16 3329) then x -! (mk_i16 3329) else x) (impl.f_repr $vec)"#))]
    fn cond_subtract_3329(vec: &mut Self) {
        cond_subtract_3329(vec)
    }

    #[requires(fstar!(r#"Spec.Utils.is_i16b_array 28296 (impl.f_repr ${vec})"#))]
    #[ensures(|_| fstar!(r#"Spec.Utils.is_i16b_array 3328 (impl.f_repr ${vec}_future) /\
                (forall i. (v (Seq.index (impl.f_repr ${vec}_future) i) % 3329) == 
                           (v (Seq.index (impl.f_repr ${vec})i) % 3329))"#))]

    fn barrett_reduce(vec: &mut Self) {
        barrett_reduce(vec)
    }

    #[requires(fstar!(r#"Spec.Utils.is_i16b 1664 $r"#))]
    #[ensures(|_| fstar!(r#"Spec.Utils.is_i16b_array 3328 (impl.f_repr ${vec}_future) /\
                (forall i. i < 16 ==> ((v (Seq.index (impl.f_repr ${vec}_future) i) % 3329)==
                                       (v (Seq.index (impl.f_repr $vec) i) * v $r * 169) % 3329))"#))]
    fn montgomery_multiply_by_constant(vec: &mut Self, r: i16) {
        montgomery_multiply_by_constant(vec, r.classify())
    }

    #[requires(fstar!(r#"Spec.Utils.is_i16b_array 3328 (impl.f_repr $a)"#))]
    #[ensures(|result| fstar!(r#"forall (i:nat). i < 16 ==>
                                (let x = Seq.index (impl.f_repr ${a}) i in
                                 let y = Seq.index (impl.f_repr ${result}) i in
                                 (v y >= 0 /\ v y <= 3328 /\ (v y % 3329 == v x % 3329)))"#))]
    fn to_unsigned_representative(a: Self) -> Self {
        to_unsigned_representative(a)
    }

    #[requires(fstar!(r#"forall (i:nat). i < 16 ==> v (Seq.index (impl.f_repr $a) i) >= 0 /\
        v (Seq.index (impl.f_repr $a) i) < 3329"#))]
    #[ensures(|_| fstar!(r#"forall (i:nat). i < 16 ==> bounded (Seq.index (impl.f_repr ${a}_future) i) 1"#))]
    fn compress_1(a: &mut Self) {
        compress_1(a)
    }

    #[requires(fstar!(r#"(v $COEFFICIENT_BITS == 4 \/
            v $COEFFICIENT_BITS == 5 \/
            v $COEFFICIENT_BITS == 10 \/
            v $COEFFICIENT_BITS == 11) /\
        (forall (i:nat). i < 16 ==> v (Seq.index (impl.f_repr $a) i) >= 0 /\
            v (Seq.index (impl.f_repr $a) i) < 3329)"#))]
    #[ensures(|_| fstar!(r#"(v $COEFFICIENT_BITS == 4 \/
            v $COEFFICIENT_BITS == 5 \/
            v $COEFFICIENT_BITS == 10 \/
            v $COEFFICIENT_BITS == 11) ==>
                (forall (i:nat). i < 16 ==> bounded (Seq.index (impl.f_repr ${a}_future) i) (v $COEFFICIENT_BITS))"#))]
    fn compress<const COEFFICIENT_BITS: i32>(a: &mut Self) {
        compress::<COEFFICIENT_BITS>(a)
    }

    #[hax_lib::requires(fstar!(r#"forall (i:nat). i < 16 ==> 
                                    (let x = Seq.index (impl.f_repr $a) i in 
                                     (x == mk_i16 0 \/ x == mk_i16 1))"#))]
    fn decompress_1(a: Self) -> Self {
        decompress_1(a)
    }

    #[requires(fstar!(r#"(v $COEFFICIENT_BITS == 4 \/
        v $COEFFICIENT_BITS == 5 \/
        v $COEFFICIENT_BITS == 10 \/
        v $COEFFICIENT_BITS == 11) /\
    (forall (i:nat). i < 16 ==> v (Seq.index (impl.f_repr $a) i) >= 0 /\
        v (Seq.index (impl.f_repr $a) i) < pow2 (v $COEFFICIENT_BITS))"#))]
    fn decompress_ciphertext_coefficient<const COEFFICIENT_BITS: i32>(a: &mut Self) {
        decompress_ciphertext_coefficient::<COEFFICIENT_BITS>(a)
    }

    #[requires(fstar!(r#"Spec.Utils.is_i16b 1664 zeta0 /\ Spec.Utils.is_i16b 1664 zeta1 /\ 
                       Spec.Utils.is_i16b 1664 zeta2 /\ Spec.Utils.is_i16b 1664 zeta3  /\
                       Spec.Utils.is_i16b_array (11207+5*3328) (impl.f_repr ${a})"#))]
    #[ensures(|_| fstar!(r#"Spec.Utils.is_i16b_array (11207+6*3328) (impl.f_repr ${a}_future)"#))]
    fn ntt_layer_1_step(a: &mut Self, zeta0: i16, zeta1: i16, zeta2: i16, zeta3: i16) {
        ntt_layer_1_step(a, zeta0, zeta1, zeta2, zeta3)
    }

    #[requires(fstar!(r#"Spec.Utils.is_i16b 1664 zeta0 /\ Spec.Utils.is_i16b 1664 zeta1 /\
                       Spec.Utils.is_i16b_array (11207+4*3328) (impl.f_repr ${a})"#))]
    #[ensures(|_| fstar!(r#"Spec.Utils.is_i16b_array (11207+5*3328) (impl.f_repr ${a}_future)"#))]
    fn ntt_layer_2_step(a: &mut Self, zeta0: i16, zeta1: i16) {
        ntt_layer_2_step(a, zeta0, zeta1)
    }

    #[requires(fstar!(r#"Spec.Utils.is_i16b 1664 zeta /\
                       Spec.Utils.is_i16b_array (11207+3*3328) (impl.f_repr ${a})"#))]
    #[ensures(|_| fstar!(r#"Spec.Utils.is_i16b_array (11207+4*3328) (impl.f_repr ${a}_future)"#))]
    fn ntt_layer_3_step(a: &mut Self, zeta: i16) {
        ntt_layer_3_step(a, zeta)
    }

    #[requires(fstar!(r#"Spec.Utils.is_i16b 1664 zeta0 /\ Spec.Utils.is_i16b 1664 zeta1 /\ 
                       Spec.Utils.is_i16b 1664 zeta2 /\ Spec.Utils.is_i16b 1664 zeta3 /\
                       Spec.Utils.is_i16b_array (4*3328) (impl.f_repr ${a})"#))]
    #[ensures(|_| fstar!(r#"Spec.Utils.is_i16b_array 3328 (impl.f_repr ${a}_future)"#))]
    fn inv_ntt_layer_1_step(a: &mut Self, zeta0: i16, zeta1: i16, zeta2: i16, zeta3: i16) {
        inv_ntt_layer_1_step(a, zeta0, zeta1, zeta2, zeta3)
    }

    #[requires(fstar!(r#"Spec.Utils.is_i16b 1664 zeta0 /\ Spec.Utils.is_i16b 1664 zeta1 /\
                       Spec.Utils.is_i16b_array 3328 (impl.f_repr ${a})"#))]
    #[ensures(|_| fstar!(r#"Spec.Utils.is_i16b_array 3328 (impl.f_repr ${a}_future)"#))]
    fn inv_ntt_layer_2_step(a: &mut Self, zeta0: i16, zeta1: i16) {
        inv_ntt_layer_2_step(a, zeta0, zeta1)
    }

    #[requires(fstar!(r#"Spec.Utils.is_i16b 1664 zeta /\
                       Spec.Utils.is_i16b_array 3328 (impl.f_repr ${a})"#))]
    #[ensures(|_| fstar!(r#"Spec.Utils.is_i16b_array 3328 (impl.f_repr ${a}_future)"#))]
    fn inv_ntt_layer_3_step(a: &mut Self, zeta: i16) {
        inv_ntt_layer_3_step(a, zeta)
    }

    #[requires(fstar!(r#"Spec.Utils.is_i16b 1664 zeta0 /\ Spec.Utils.is_i16b 1664 zeta1 /\
                       Spec.Utils.is_i16b 1664 zeta2 /\ Spec.Utils.is_i16b 1664 zeta3 /\
                       Spec.Utils.is_i16b_array 3328 (impl.f_repr ${lhs}) /\
                       Spec.Utils.is_i16b_array 3328 (impl.f_repr ${rhs})"#))]
    #[ensures(|_| fstar!(r#"Spec.Utils.is_i16b_array 3328 (impl.f_repr ${out}_future)"#))]
    fn ntt_multiply(
        lhs: &Self,
        rhs: &Self,
        out: &mut Self,
        zeta0: i16,
        zeta1: i16,
        zeta2: i16,
        zeta3: i16,
    ) {
        ntt_multiply(lhs, rhs, out, zeta0, zeta1, zeta2, zeta3)
    }

    #[requires(fstar!(r#"Spec.MLKEM.serialize_pre 1 (impl.f_repr $a) /\ Seq.length $out == 2"#))]
    #[ensures(|_| fstar!(r#"Seq.length ${out}_future == 2 /\ 
            (Spec.MLKEM.serialize_pre 1 (impl.f_repr $a) ==> 
                Spec.MLKEM.serialize_post 1 (impl.f_repr $a) ${out}_future)
                        "#))]
    fn serialize_1(a: &Self, out: &mut [u8]) {
        serialize_1(a, out)
    }

    #[requires(a.len() == 2)]
    #[ensures(|_| fstar!(r#"Seq.length $a == 2 ==> 
        Spec.MLKEM.deserialize_post 1 $a (impl.f_repr ${out}_future)"#))]
    fn deserialize_1(a: &[u8], out: &mut Self) {
        deserialize_1(a, out)
    }

    #[requires(fstar!(r#"Spec.MLKEM.serialize_pre 4 (impl.f_repr $a) /\ Seq.length $out == 8"#))]
    #[ensures(|_| fstar!(r#"Seq.length ${out}_future == 8 /\
        (Spec.MLKEM.serialize_pre 4 (impl.f_repr $a) ==> 
            Spec.MLKEM.serialize_post 4 (impl.f_repr $a) ${out}_future)
                         "#))]
    fn serialize_4(a: &Self, out: &mut [u8]) {
        serialize_4(a, out)
    }

    #[requires(a.len() == 8)]
    #[ensures(|_| fstar!(r#"Seq.length $a == 8 ==> 
        Spec.MLKEM.deserialize_post 4 $a (impl.f_repr ${out}_future)"#))]
    fn deserialize_4(a: &[u8], out: &mut Self) {
        deserialize_4(a, out)
    }

    fn serialize_5(a: &Self, out: &mut [u8]) {
        serialize_5(a, out)
    }

    #[requires(a.len() == 10)]
    fn deserialize_5(a: &[u8], out: &mut Self) {
        deserialize_5(a, out)
    }

    #[requires(fstar!(r#"Spec.MLKEM.serialize_pre 10 (impl.f_repr $a) /\ Seq.length $out == 20"#))]
    #[ensures(|_| fstar!(r#"Seq.length ${out}_future == 20 /\
        (Spec.MLKEM.serialize_pre 10 (impl.f_repr $a) ==> 
            Spec.MLKEM.serialize_post 10 (impl.f_repr $a) ${out}_future)
                         "#))]
    fn serialize_10(a: &Self, out: &mut [u8]) {
        serialize_10(a, out)
    }

    #[requires(a.len() == 20)]
    #[ensures(|_| fstar!(r#"Seq.length $a == 20 ==> 
        Spec.MLKEM.deserialize_post 10 $a (impl.f_repr ${out}_future)"#))]
    fn deserialize_10(a: &[u8], out: &mut Self) {
        deserialize_10(a, out)
    }

    fn serialize_11(a: &Self, out: &mut [u8]) {
        serialize_11(a, out)
    }

    #[requires(a.len() == 22)]
    fn deserialize_11(a: &[u8], out: &mut Self) {
        deserialize_11(a, out)
    }

    #[requires(fstar!(r#"Spec.MLKEM.serialize_pre 12 (impl.f_repr $a) /\ Seq.length $out == 24"#))]
    #[ensures(|_| fstar!(r#"Seq.length ${out}_future == 24 /\ 
        (Spec.MLKEM.serialize_pre 12 (impl.f_repr $a) ==> 
            Spec.MLKEM.serialize_post 12 (impl.f_repr $a) ${out}_future)
                         "#))]
    fn serialize_12(a: &Self, out: &mut [u8]) {
        serialize_12(a, out)
    }

    #[requires(a.len() == 24)]
    #[ensures(|_| fstar!(r#"Seq.length $a == 24 ==> 
        Spec.MLKEM.deserialize_post 12 $a (impl.f_repr ${out}_future)"#))]
    fn deserialize_12(a: &[u8], out: &mut Self) {
        deserialize_12(a, out)
    }

    #[requires(a.len() == 24 && out.len() == 16)]
    #[ensures(|result| result <= 16 && future(out).len() == 16)]
    fn rej_sample(a: &[u8], out: &mut [i16]) -> usize {
        rej_sample(a, out)
    }
}
