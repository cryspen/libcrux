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
use super::traits::spec;
#[cfg(hax)]
use hax_lib::prop::ToProp;

#[cfg(hax)]
impl crate::vector::traits::Repr for PortableVector {
    fn repr(&self) -> [i16; 16] {
        to_i16_array(self.clone())
    }
}

#[cfg(any(eurydice, not(hax)))]
impl crate::vector::traits::Repr for PortableVector {}

#[hax_lib::requires(fstar!(r#"Spec.MLKEM.serialize_pre 1 (impl.f_repr $a)"#))]
#[hax_lib::ensures(|out| fstar!(r#"Spec.MLKEM.serialize_pre 1 (impl.f_repr $a) ==> 
                                 Spec.MLKEM.serialize_post 1 (impl.f_repr $a) $out"#))]
fn serialize_1(a: PortableVector) -> [u8; 2] {
    hax_lib::fstar!(
        r#"assert (forall i. Rust_primitives.bounded (Seq.index ${a}.f_elements i) 1)"#
    );
    hax_lib::fstar!(r#"Libcrux_ml_kem.Vector.Portable.Serialize.serialize_1_lemma $a"#);
    serialize::serialize_1(a).declassify()
}

#[hax_lib::requires(a.len() == 2)]
#[hax_lib::ensures(|out| fstar!(r#"sz (Seq.length $a) =. sz 2 ==> Spec.MLKEM.deserialize_post 1 $a (impl.f_repr $out)"#))]
fn deserialize_1(a: &[u8]) -> PortableVector {
    hax_lib::fstar!(r#"Libcrux_ml_kem.Vector.Portable.Serialize.deserialize_1_lemma $a"#);
    serialize::deserialize_1(a.classify_ref())
}

#[hax_lib::requires(fstar!(r#"Spec.MLKEM.serialize_pre 4 (impl.f_repr $a)"#))]
#[hax_lib::ensures(|out| fstar!(r#"Spec.MLKEM.serialize_pre 4 (impl.f_repr $a) ==> Spec.MLKEM.serialize_post 4 (impl.f_repr $a) $out"#))]
fn serialize_4(a: PortableVector) -> [u8; 8] {
    hax_lib::fstar!(
        r#"assert (forall i. Rust_primitives.bounded (Seq.index ${a}.f_elements i) 4)"#
    );
    hax_lib::fstar!(r#"Libcrux_ml_kem.Vector.Portable.Serialize.serialize_4_lemma $a"#);
    serialize::serialize_4(a).declassify()
}

#[hax_lib::requires(a.len() == 8)]
#[hax_lib::ensures(|out| fstar!(r#"sz (Seq.length $a) =. sz 8 ==> Spec.MLKEM.deserialize_post 4 $a (impl.f_repr $out)"#))]
fn deserialize_4(a: &[u8]) -> PortableVector {
    hax_lib::fstar!(r#"Libcrux_ml_kem.Vector.Portable.Serialize.deserialize_4_lemma $a"#);
    serialize::deserialize_4(a.classify_ref())
}

fn serialize_5(a: PortableVector) -> [u8; 10] {
    serialize::serialize_5(a).declassify()
}

#[hax_lib::requires(a.len() == 10)]
fn deserialize_5(a: &[u8]) -> PortableVector {
    serialize::deserialize_5(a.classify_ref())
}

#[hax_lib::requires(fstar!(r#"Spec.MLKEM.serialize_pre 10 (impl.f_repr $a)"#))]
#[hax_lib::ensures(|out| fstar!(r#"Spec.MLKEM.serialize_pre 10 (impl.f_repr $a) ==> Spec.MLKEM.serialize_post 10 (impl.f_repr $a) $out"#))]
fn serialize_10(a: PortableVector) -> [u8; 20] {
    hax_lib::fstar!(r#"Libcrux_ml_kem.Vector.Portable.Serialize.serialize_10_lemma $a"#);
    serialize::serialize_10(a).declassify()
}

#[hax_lib::requires(a.len() == 20)]
#[hax_lib::ensures(|out| fstar!(r#"sz (Seq.length $a) =. sz 20 ==> Spec.MLKEM.deserialize_post 10 $a (impl.f_repr $out)"#))]
fn deserialize_10(a: &[u8]) -> PortableVector {
    hax_lib::fstar!(r#"Libcrux_ml_kem.Vector.Portable.Serialize.deserialize_10_lemma $a"#);
    serialize::deserialize_10(a.classify_ref())
}

fn serialize_11(a: PortableVector) -> [u8; 22] {
    serialize::serialize_11(a).declassify()
}

#[hax_lib::requires(a.len() == 22)]
fn deserialize_11(a: &[u8]) -> PortableVector {
    serialize::deserialize_11(a.classify_ref())
}

#[hax_lib::requires(fstar!(r#"Spec.MLKEM.serialize_pre 12 (impl.f_repr $a)"#))]
#[hax_lib::ensures(|out| fstar!(r#"Spec.MLKEM.serialize_pre 12 (impl.f_repr $a) ==> Spec.MLKEM.serialize_post 12 (impl.f_repr $a) $out"#))]
fn serialize_12(a: PortableVector) -> [u8; 24] {
    hax_lib::fstar!(r#"Libcrux_ml_kem.Vector.Portable.Serialize.serialize_12_lemma $a"#);
    serialize::serialize_12(a).declassify()
}

#[hax_lib::requires(a.len() == 24)]
#[hax_lib::ensures(|out| fstar!(r#"sz (Seq.length $a) =. sz 24 ==> Spec.MLKEM.deserialize_post 12 $a (impl.f_repr $out)"#))]
fn deserialize_12(a: &[u8]) -> PortableVector {
    hax_lib::fstar!(r#"Libcrux_ml_kem.Vector.Portable.Serialize.deserialize_12_lemma $a"#);
    serialize::deserialize_12(a.classify_ref())
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
    #[ensures(|out| fstar!(r#"impl.f_repr out == $array"#))]
    fn from_i16_array(array: &[i16]) -> Self {
        from_i16_array(array.classify_ref())
    }

    #[ensures(|out| fstar!(r#"out == impl.f_repr $x"#))]
    fn to_i16_array(x: Self) -> [i16; 16] {
        to_i16_array(x).declassify()
    }

    #[requires(array.len() >= 32)]
    fn from_bytes(array: &[u8]) -> Self {
        from_bytes(array.classify_ref())
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

    #[requires(fstar!(r#"${spec::add_pre} ${lhs}.f_elements ${rhs}.f_elements"#))]
    #[ensures(|result| fstar!(r#"${spec::add_post} ${lhs}.f_elements ${rhs}.f_elements ${result}.f_elements"#))]
    fn add(lhs: Self, rhs: &Self) -> Self {
        add(lhs, rhs)
    }

    #[requires(fstar!(r#"${spec::sub_pre} ${lhs}.f_elements ${rhs}.f_elements"#))]
    #[ensures(|result| fstar!(r#"${spec::sub_post} ${lhs}.f_elements ${rhs}.f_elements ${result}.f_elements"#))]
    fn sub(lhs: Self, rhs: &Self) -> Self {
        sub(lhs, rhs)
    }

    #[requires(fstar!(r#"forall i. i < 16 ==> 
        Spec.Utils.is_intb (pow2 15 - 1) (v (Seq.index ${vec}.f_elements i) * v c)"#))]
    #[ensures(|result| fstar!(r#"
        (forall i. i < 16 ==> 
            (v (Seq.index ${result}.f_elements i) == 
            v (Seq.index ${vec}.f_elements i) * v c))"#))]
    fn multiply_by_constant(vec: Self, c: i16) -> Self {
        hax_lib::fstar!(
            r#"reveal_opaque (`%Spec.Utils.is_i16b_array_opaque) (Spec.Utils.is_i16b_array_opaque)"#
        );
        multiply_by_constant(vec, c)
    }

    #[requires(fstar!(r#"Spec.Utils.is_i16b_array_opaque (pow2 12 - 1) (impl.f_repr $v)"#))]
    #[ensures(|out| fstar!(r#"impl.f_repr out == Spec.Utils.map_array (fun x -> if x >=. (mk_i16 3329) then x -! (mk_i16 3329) else x) (impl.f_repr $v)"#))]
    fn cond_subtract_3329(v: Self) -> Self {
        hax_lib::fstar!(
            r#"reveal_opaque (`%Spec.Utils.is_i16b_array_opaque) (Spec.Utils.is_i16b_array_opaque)"#
        );
        cond_subtract_3329(v)
    }

    #[requires(fstar!(r#"Spec.Utils.is_i16b_array_opaque 28296 (impl.f_repr ${vector})"#))]
    #[ensures(|result| fstar!(r#"Spec.Utils.is_i16b_array_opaque 3328 (impl.f_repr ${result}) /\
                (forall i. (v (Seq.index (impl.f_repr ${result}) i) % 3329) == 
                           (v (Seq.index (impl.f_repr ${vector})i) % 3329))"#))]
    fn barrett_reduce(vector: Self) -> Self {
        hax_lib::fstar!(
            r#"reveal_opaque (`%Spec.Utils.is_i16b_array_opaque) 
                        (Spec.Utils.is_i16b_array_opaque 28296)"#
        );
        hax_lib::fstar!(
            r#"reveal_opaque (`%Spec.Utils.is_i16b_array_opaque) 
                        (Spec.Utils.is_i16b_array_opaque 3328)"#
        );
        barrett_reduce(vector)
    }

    #[requires(fstar!(r#"Spec.Utils.is_i16b 1664 $constant"#))]
    #[ensures(|result| fstar!(r#"Spec.Utils.is_i16b_array_opaque 3328 (impl.f_repr ${result}) /\
                (forall i. i < 16 ==> ((v (Seq.index (impl.f_repr ${result}) i) % 3329)==
                                       (v (Seq.index (impl.f_repr ${vector}) i) * v ${constant} * 169) % 3329))"#))]
    fn montgomery_multiply_by_constant(vector: Self, constant: i16) -> Self {
        hax_lib::fstar!(
            r#"reveal_opaque (`%Spec.Utils.is_i16b_array_opaque) 
                        (Spec.Utils.is_i16b_array_opaque 3328)"#
        );
        montgomery_multiply_by_constant(vector, constant.classify())
    }

    #[requires(fstar!(r#"Spec.Utils.is_i16b_array_opaque 3328 (impl.f_repr $a)"#))]
    #[ensures(|result| fstar!(r#"forall (i:nat). i < 16 ==>
                                (let x = Seq.index (impl.f_repr ${a}) i in
                                 let y = Seq.index (impl.f_repr ${result}) i in
                                 (v y >= 0 /\ v y <= 3328 /\ (v y % 3329 == v x % 3329)))"#))]
    fn to_unsigned_representative(a: Self) -> Self {
        hax_lib::fstar!(
            r#"reveal_opaque (`%Spec.Utils.is_i16b_array_opaque) 
                        (Spec.Utils.is_i16b_array_opaque 3328)"#
        );
        to_unsigned_representative(a)
    }

    #[requires(fstar!(r#"forall (i:nat). i < 16 ==> v (Seq.index (impl.f_repr $a) i) >= 0 /\
        v (Seq.index (impl.f_repr $a) i) < 3329"#))]
    #[ensures(|out| fstar!(r#"forall (i:nat). i < 16 ==> bounded (Seq.index (impl.f_repr $out) i) 1"#))]
    fn compress_1(a: Self) -> Self {
        compress_1(a)
    }

    #[requires(fstar!(r#"(v $COEFFICIENT_BITS == 4 \/
            v $COEFFICIENT_BITS == 5 \/
            v $COEFFICIENT_BITS == 10 \/
            v $COEFFICIENT_BITS == 11) /\
        (forall (i:nat). i < 16 ==> v (Seq.index (impl.f_repr $a) i) >= 0 /\
            v (Seq.index (impl.f_repr $a) i) < 3329)"#))]
    #[ensures(|out| fstar!(r#"(v $COEFFICIENT_BITS == 4 \/
            v $COEFFICIENT_BITS == 5 \/
            v $COEFFICIENT_BITS == 10 \/
            v $COEFFICIENT_BITS == 11) ==>
                (forall (i:nat). i < 16 ==> bounded (Seq.index (impl.f_repr $out) i) (v $COEFFICIENT_BITS))"#))]
    fn compress<const COEFFICIENT_BITS: i32>(a: Self) -> Self {
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
    fn decompress_ciphertext_coefficient<const COEFFICIENT_BITS: i32>(a: Self) -> Self {
        decompress_ciphertext_coefficient::<COEFFICIENT_BITS>(a)
    }

    #[requires(fstar!(r#"Spec.Utils.is_i16b 1664 zeta0 /\ Spec.Utils.is_i16b 1664 zeta1 /\ 
                       Spec.Utils.is_i16b 1664 zeta2 /\ Spec.Utils.is_i16b 1664 zeta3  /\
                       Spec.Utils.is_i16b_array_opaque (7*3328) (impl.f_repr ${a})"#))]
    #[ensures(|out| fstar!(r#"Spec.Utils.is_i16b_array_opaque (8*3328) (impl.f_repr $out)"#))]
    fn ntt_layer_1_step(a: Self, zeta0: i16, zeta1: i16, zeta2: i16, zeta3: i16) -> Self {
        hax_lib::fstar!(
            r#"reveal_opaque (`%Spec.Utils.is_i16b_array_opaque) 
                        (Spec.Utils.is_i16b_array_opaque (7*3328))"#
        );
        hax_lib::fstar!(
            r#"reveal_opaque (`%Spec.Utils.is_i16b_array_opaque) 
                        (Spec.Utils.is_i16b_array_opaque (8*3328))"#
        );
        ntt_layer_1_step(a, zeta0, zeta1, zeta2, zeta3)
    }

    #[requires(fstar!(r#"Spec.Utils.is_i16b 1664 zeta0 /\ Spec.Utils.is_i16b 1664 zeta1 /\
                       Spec.Utils.is_i16b_array_opaque (6*3328) (impl.f_repr ${a})"#))]
    #[ensures(|out| fstar!(r#"Spec.Utils.is_i16b_array_opaque (7*3328) (impl.f_repr $out)"#))]
    fn ntt_layer_2_step(a: Self, zeta0: i16, zeta1: i16) -> Self {
        hax_lib::fstar!(
            r#"reveal_opaque (`%Spec.Utils.is_i16b_array_opaque) 
                        (Spec.Utils.is_i16b_array_opaque (6*3328))"#
        );
        hax_lib::fstar!(
            r#"reveal_opaque (`%Spec.Utils.is_i16b_array_opaque) 
                        (Spec.Utils.is_i16b_array_opaque (7*3328))"#
        );
        ntt_layer_2_step(a, zeta0, zeta1)
    }

    #[requires(fstar!(r#"Spec.Utils.is_i16b 1664 zeta /\
                       Spec.Utils.is_i16b_array_opaque (5*3328) (impl.f_repr ${a})"#))]
    #[ensures(|out| fstar!(r#"Spec.Utils.is_i16b_array_opaque (6*3328) (impl.f_repr $out)"#))]
    fn ntt_layer_3_step(a: Self, zeta: i16) -> Self {
        hax_lib::fstar!(
            r#"reveal_opaque (`%Spec.Utils.is_i16b_array_opaque) 
                        (Spec.Utils.is_i16b_array_opaque (5*3328))"#
        );
        hax_lib::fstar!(
            r#"reveal_opaque (`%Spec.Utils.is_i16b_array_opaque) 
                        (Spec.Utils.is_i16b_array_opaque (6*3328))"#
        );
        ntt_layer_3_step(a, zeta)
    }

    #[requires(fstar!(r#"Spec.Utils.is_i16b 1664 zeta0 /\ Spec.Utils.is_i16b 1664 zeta1 /\ 
                       Spec.Utils.is_i16b 1664 zeta2 /\ Spec.Utils.is_i16b 1664 zeta3 /\
                       Spec.Utils.is_i16b_array_opaque (4*3328) (impl.f_repr ${a})"#))]
    #[ensures(|out| fstar!(r#"Spec.Utils.is_i16b_array_opaque 3328 (impl.f_repr $out)"#))]
    fn inv_ntt_layer_1_step(a: Self, zeta0: i16, zeta1: i16, zeta2: i16, zeta3: i16) -> Self {
        hax_lib::fstar!(
            r#"reveal_opaque (`%Spec.Utils.is_i16b_array_opaque) 
                        (Spec.Utils.is_i16b_array_opaque (4*3328))"#
        );
        hax_lib::fstar!(
            r#"reveal_opaque (`%Spec.Utils.is_i16b_array_opaque) 
                        (Spec.Utils.is_i16b_array_opaque 3328)"#
        );
        inv_ntt_layer_1_step(a, zeta0, zeta1, zeta2, zeta3)
    }

    #[requires(fstar!(r#"Spec.Utils.is_i16b 1664 zeta0 /\ Spec.Utils.is_i16b 1664 zeta1 /\
                       Spec.Utils.is_i16b_array_opaque 3328 (impl.f_repr ${a})"#))]
    #[ensures(|out| fstar!(r#"Spec.Utils.is_i16b_array_opaque 3328 (impl.f_repr $out)"#))]
    fn inv_ntt_layer_2_step(a: Self, zeta0: i16, zeta1: i16) -> Self {
        hax_lib::fstar!(
            r#"reveal_opaque (`%Spec.Utils.is_i16b_array_opaque) 
                        (Spec.Utils.is_i16b_array_opaque 3328)"#
        );
        inv_ntt_layer_2_step(a, zeta0, zeta1)
    }

    #[requires(fstar!(r#"Spec.Utils.is_i16b 1664 zeta /\
                       Spec.Utils.is_i16b_array_opaque 3328 (impl.f_repr ${a})"#))]
    #[ensures(|out| fstar!(r#"Spec.Utils.is_i16b_array_opaque 3328 (impl.f_repr $out)"#))]
    fn inv_ntt_layer_3_step(a: Self, zeta: i16) -> Self {
        hax_lib::fstar!(
            r#"reveal_opaque (`%Spec.Utils.is_i16b_array_opaque) 
                        (Spec.Utils.is_i16b_array_opaque 3328)"#
        );
        inv_ntt_layer_3_step(a, zeta)
    }

    #[requires(fstar!(r#"Spec.Utils.is_i16b 1664 zeta0 /\ Spec.Utils.is_i16b 1664 zeta1 /\
                       Spec.Utils.is_i16b 1664 zeta2 /\ Spec.Utils.is_i16b 1664 zeta3 /\
                       Spec.Utils.is_i16b_array_opaque 3328 (impl.f_repr ${lhs}) /\
                       Spec.Utils.is_i16b_array_opaque 3328 (impl.f_repr ${rhs})"#))]
    #[ensures(|out| fstar!(r#"Spec.Utils.is_i16b_array_opaque 3328 (impl.f_repr $out)"#))]
    fn ntt_multiply(
        lhs: &Self,
        rhs: &Self,
        zeta0: i16,
        zeta1: i16,
        zeta2: i16,
        zeta3: i16,
    ) -> Self {
        hax_lib::fstar!(
            r#"reveal_opaque (`%Spec.Utils.is_i16b_array_opaque) 
                        (Spec.Utils.is_i16b_array_opaque 3328)"#
        );
        ntt_multiply(lhs, rhs, zeta0, zeta1, zeta2, zeta3)
    }

    #[requires(fstar!(r#"Spec.MLKEM.serialize_pre 1 (impl.f_repr $a)"#))]
    #[ensures(|out| fstar!(r#"Spec.MLKEM.serialize_pre 1 (impl.f_repr $a) ==> Spec.MLKEM.serialize_post 1 (impl.f_repr $a) $out"#))]
    fn serialize_1(a: Self) -> [u8; 2] {
        serialize_1(a)
    }

    #[requires(a.len() == 2)]
    #[ensures(|out| fstar!(r#"sz (Seq.length $a) =. sz 2 ==> Spec.MLKEM.deserialize_post 1 $a (impl.f_repr $out)"#))]
    fn deserialize_1(a: &[u8]) -> Self {
        deserialize_1(a)
    }

    #[requires(fstar!(r#"Spec.MLKEM.serialize_pre 4 (impl.f_repr $a)"#))]
    #[ensures(|out| fstar!(r#"Spec.MLKEM.serialize_pre 4 (impl.f_repr $a) ==> Spec.MLKEM.serialize_post 4 (impl.f_repr $a) $out"#))]
    fn serialize_4(a: Self) -> [u8; 8] {
        serialize_4(a)
    }

    #[requires(a.len() == 8)]
    #[ensures(|out| fstar!(r#"sz (Seq.length $a) =. sz 8 ==> Spec.MLKEM.deserialize_post 4 $a (impl.f_repr $out)"#))]
    fn deserialize_4(a: &[u8]) -> Self {
        deserialize_4(a)
    }

    fn serialize_5(a: Self) -> [u8; 10] {
        serialize_5(a)
    }

    #[requires(a.len() == 10)]
    fn deserialize_5(a: &[u8]) -> Self {
        deserialize_5(a)
    }

    #[requires(fstar!(r#"Spec.MLKEM.serialize_pre 10 (impl.f_repr $a)"#))]
    #[ensures(|out| fstar!(r#"Spec.MLKEM.serialize_pre 10 (impl.f_repr $a) ==> Spec.MLKEM.serialize_post 10 (impl.f_repr $a) $out"#))]
    fn serialize_10(a: Self) -> [u8; 20] {
        serialize_10(a)
    }

    #[requires(a.len() == 20)]
    #[ensures(|out| fstar!(r#"sz (Seq.length $a) =. sz 20 ==> Spec.MLKEM.deserialize_post 10 $a (impl.f_repr $out)"#))]
    fn deserialize_10(a: &[u8]) -> Self {
        deserialize_10(a)
    }

    fn serialize_11(a: Self) -> [u8; 22] {
        serialize_11(a)
    }

    #[requires(a.len() == 22)]
    fn deserialize_11(a: &[u8]) -> Self {
        deserialize_11(a)
    }

    #[requires(fstar!(r#"Spec.MLKEM.serialize_pre 12 (impl.f_repr $a)"#))]
    #[ensures(|out| fstar!(r#"Spec.MLKEM.serialize_pre 12 (impl.f_repr $a) ==> Spec.MLKEM.serialize_post 12 (impl.f_repr $a) $out"#))]
    fn serialize_12(a: Self) -> [u8; 24] {
        serialize_12(a)
    }

    #[requires(a.len() == 24)]
    #[ensures(|out| fstar!(r#"sz (Seq.length $a) =. sz 24 ==> Spec.MLKEM.deserialize_post 12 $a (impl.f_repr $out)"#))]
    fn deserialize_12(a: &[u8]) -> Self {
        deserialize_12(a)
    }

    #[requires(a.len() == 24 && out.len() == 16)]
    #[ensures(|result| (future(out).len() == 16 && result <= 16).to_prop().and(
            hax_lib::forall(|j: usize|
                hax_lib::implies(j < result,
                    future(out)[j] >= 0 && future(out)[j] <= 3328))))]
    fn rej_sample(a: &[u8], out: &mut [i16]) -> usize {
        rej_sample(a, out)
    }
}
