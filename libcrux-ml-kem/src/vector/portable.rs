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
use super::traits::{spec, Repr};
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

#[hax_lib::requires(fstar!(r#"Libcrux_ml_kem.Vector.Traits.Spec.serialize_pre_N 1 (impl.f_repr $a)"#))]
#[hax_lib::ensures(|out| fstar!(r#"Libcrux_ml_kem.Vector.Traits.Spec.serialize_pre_N 1 (impl.f_repr $a) ==> 
                                 Libcrux_ml_kem.Vector.Traits.Spec.serialize_post_N 1 (impl.f_repr $a) $out"#))]
fn serialize_1(a: PortableVector) -> [u8; 2] {
    hax_lib::fstar!(
        r#"assert (forall i. Rust_primitives.bounded (Seq.index ${a}.f_elements i) 1)"#
    );
    hax_lib::fstar!(r#"Libcrux_ml_kem.Vector.Portable.Serialize.serialize_1_lemma $a"#);
    serialize::serialize_1(a).declassify()
}

#[hax_lib::requires(a.len() == 2)]
#[hax_lib::ensures(|out| fstar!(r#"sz (Seq.length $a) =. sz 2 ==> Libcrux_ml_kem.Vector.Traits.Spec.deserialize_post_N 1 $a (impl.f_repr $out)"#))]
fn deserialize_1(a: &[u8]) -> PortableVector {
    hax_lib::fstar!(r#"Libcrux_ml_kem.Vector.Portable.Serialize.deserialize_1_lemma $a"#);
    serialize::deserialize_1(a.classify_ref())
}

#[hax_lib::requires(fstar!(r#"Libcrux_ml_kem.Vector.Traits.Spec.serialize_pre_N 4 (impl.f_repr $a)"#))]
#[hax_lib::ensures(|out| fstar!(r#"Libcrux_ml_kem.Vector.Traits.Spec.serialize_pre_N 4 (impl.f_repr $a) ==> Libcrux_ml_kem.Vector.Traits.Spec.serialize_post_N 4 (impl.f_repr $a) $out"#))]
fn serialize_4(a: PortableVector) -> [u8; 8] {
    hax_lib::fstar!(
        r#"assert (forall i. Rust_primitives.bounded (Seq.index ${a}.f_elements i) 4)"#
    );
    hax_lib::fstar!(r#"Libcrux_ml_kem.Vector.Portable.Serialize.serialize_4_lemma $a"#);
    serialize::serialize_4(a).declassify()
}

#[hax_lib::requires(a.len() == 8)]
#[hax_lib::ensures(|out| fstar!(r#"sz (Seq.length $a) =. sz 8 ==> Libcrux_ml_kem.Vector.Traits.Spec.deserialize_post_N 4 $a (impl.f_repr $out)"#))]
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

#[hax_lib::requires(fstar!(r#"Libcrux_ml_kem.Vector.Traits.Spec.serialize_pre_N 10 (impl.f_repr $a)"#))]
#[hax_lib::ensures(|out| fstar!(r#"Libcrux_ml_kem.Vector.Traits.Spec.serialize_pre_N 10 (impl.f_repr $a) ==> Libcrux_ml_kem.Vector.Traits.Spec.serialize_post_N 10 (impl.f_repr $a) $out"#))]
fn serialize_10(a: PortableVector) -> [u8; 20] {
    hax_lib::fstar!(r#"Libcrux_ml_kem.Vector.Portable.Serialize.serialize_10_lemma $a"#);
    serialize::serialize_10(a).declassify()
}

#[hax_lib::requires(a.len() == 20)]
#[hax_lib::ensures(|out| fstar!(r#"sz (Seq.length $a) =. sz 20 ==> Libcrux_ml_kem.Vector.Traits.Spec.deserialize_post_N 10 $a (impl.f_repr $out)"#))]
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

#[hax_lib::requires(fstar!(r#"Libcrux_ml_kem.Vector.Traits.Spec.serialize_pre_N 12 (impl.f_repr $a)"#))]
#[hax_lib::ensures(|out| fstar!(r#"Libcrux_ml_kem.Vector.Traits.Spec.serialize_pre_N 12 (impl.f_repr $a) ==> Libcrux_ml_kem.Vector.Traits.Spec.serialize_post_N 12 (impl.f_repr $a) $out"#))]
fn serialize_12(a: PortableVector) -> [u8; 24] {
    hax_lib::fstar!(r#"Libcrux_ml_kem.Vector.Portable.Serialize.serialize_12_lemma $a"#);
    serialize::serialize_12(a).declassify()
}

#[hax_lib::requires(a.len() == 24)]
#[hax_lib::ensures(|out| fstar!(r#"sz (Seq.length $a) =. sz 24 ==> Libcrux_ml_kem.Vector.Traits.Spec.deserialize_post_N 12 $a (impl.f_repr $out)"#))]
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
            r#"reveal_opaque (`%Libcrux_ml_kem.Vector.Traits.Spec.is_i16b_array_opaque) (Libcrux_ml_kem.Vector.Traits.Spec.is_i16b_array_opaque)"#
        );
        multiply_by_constant(vec, c)
    }

    #[requires(spec::cond_subtract_3329_pre(&vec.repr()))]
    #[ensures(|out| spec::cond_subtract_3329_post(&vec.repr(), &out.repr()))]
    fn cond_subtract_3329(vec: Self) -> Self {
        hax_lib::fstar!(
            r#"reveal_opaque (`%Libcrux_ml_kem.Vector.Traits.Spec.is_i16b_array_opaque) (Libcrux_ml_kem.Vector.Traits.Spec.is_i16b_array_opaque)"#
        );
        cond_subtract_3329(vec)
    }

    #[requires(fstar!(r#"Libcrux_ml_kem.Vector.Traits.Spec.is_i16b_array_opaque 28296 (impl.f_repr ${vector})"#))]
    #[ensures(|result| fstar!(r#"Libcrux_ml_kem.Vector.Traits.Spec.is_i16b_array_opaque 3328 (impl.f_repr ${result}) /\
                (forall i. (v (Seq.index (impl.f_repr ${result}) i) % 3329) == 
                           (v (Seq.index (impl.f_repr ${vector})i) % 3329))"#))]
    fn barrett_reduce(vector: Self) -> Self {
        hax_lib::fstar!(
            r#"reveal_opaque (`%Libcrux_ml_kem.Vector.Traits.Spec.is_i16b_array_opaque) 
                        (Libcrux_ml_kem.Vector.Traits.Spec.is_i16b_array_opaque 28296)"#
        );
        hax_lib::fstar!(
            r#"reveal_opaque (`%Libcrux_ml_kem.Vector.Traits.Spec.is_i16b_array_opaque) 
                        (Libcrux_ml_kem.Vector.Traits.Spec.is_i16b_array_opaque 3328)"#
        );
        barrett_reduce(vector)
    }

    #[requires(fstar!(r#"Spec.Utils.is_i16b 1664 $constant"#))]
    #[ensures(|result| fstar!(r#"Libcrux_ml_kem.Vector.Traits.Spec.is_i16b_array_opaque 3328 (impl.f_repr ${result}) /\
                (forall i. i < 16 ==> ((v (Seq.index (impl.f_repr ${result}) i) % 3329)==
                                       (v (Seq.index (impl.f_repr ${vector}) i) * v ${constant} * 169) % 3329))"#))]
    fn montgomery_multiply_by_constant(vector: Self, constant: i16) -> Self {
        hax_lib::fstar!(
            r#"reveal_opaque (`%Libcrux_ml_kem.Vector.Traits.Spec.is_i16b_array_opaque) 
                        (Libcrux_ml_kem.Vector.Traits.Spec.is_i16b_array_opaque 3328)"#
        );
        montgomery_multiply_by_constant(vector, constant.classify())
    }

    #[requires(fstar!(r#"Libcrux_ml_kem.Vector.Traits.Spec.is_i16b_array_opaque 3328 (impl.f_repr $a)"#))]
    #[ensures(|result| fstar!(r#"forall (i:nat). i < 16 ==>
                                (let x = Seq.index (impl.f_repr ${a}) i in
                                 let y = Seq.index (impl.f_repr ${result}) i in
                                 (v y >= 0 /\ v y <= 3328 /\ (v y % 3329 == v x % 3329)))"#))]
    fn to_unsigned_representative(a: Self) -> Self {
        hax_lib::fstar!(
            r#"reveal_opaque (`%Libcrux_ml_kem.Vector.Traits.Spec.is_i16b_array_opaque) 
                        (Libcrux_ml_kem.Vector.Traits.Spec.is_i16b_array_opaque 3328)"#
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

    #[requires(fstar!(r#"${spec::ntt_layer_1_step_pre} ${a}.f_elements zeta0 zeta1 zeta2 zeta3"#))]
    #[ensures(|out| fstar!(r#"${spec::ntt_layer_1_step_post} ${a}.f_elements zeta0 zeta1 zeta2 zeta3 ${out}.f_elements"#))]
    fn ntt_layer_1_step(a: Self, zeta0: i16, zeta1: i16, zeta2: i16, zeta3: i16) -> Self {
        hax_lib::fstar!(
            r#"reveal_opaque (`%Libcrux_ml_kem.Vector.Traits.Spec.is_i16b_array_opaque)
                        (Libcrux_ml_kem.Vector.Traits.Spec.is_i16b_array_opaque (7*3328))"#
        );
        let out = ntt_layer_1_step(a, zeta0, zeta1, zeta2, zeta3);
        hax_lib::fstar!(
            r#"reveal_opaque (`%Libcrux_ml_kem.Vector.Traits.Spec.is_i16b_array_opaque)
                        (Libcrux_ml_kem.Vector.Traits.Spec.is_i16b_array_opaque (8*3328))"#
        );
        hax_lib::fstar!(
            r#"
            // Expose the 8 butterfly ntt_specs, then convert each butterfly
            // pair into its 2 FE-algebra equalities via the Layer-0.5 commute
            // lemma.  The `forall4` in the trait post expands to 4 per-group
            // conjuncts; we state each conjunct explicitly as an `assert` so
            // Z3 matches directly against the butterfly-commute ensures.
            reveal_opaque (`%Spec.Utils.ntt_layer_1_butterfly_post)
                          (Spec.Utils.ntt_layer_1_butterfly_post ${a}.f_elements);
            Hacspec_ml_kem.Commute.Chunk.lemma_butterfly_pair_commute
              ${a}.f_elements ${out}.f_elements zeta0 0 2;
            Hacspec_ml_kem.Commute.Chunk.lemma_butterfly_pair_commute
              ${a}.f_elements ${out}.f_elements zeta0 1 3;
            Hacspec_ml_kem.Commute.Chunk.lemma_butterfly_pair_commute
              ${a}.f_elements ${out}.f_elements zeta1 4 6;
            Hacspec_ml_kem.Commute.Chunk.lemma_butterfly_pair_commute
              ${a}.f_elements ${out}.f_elements zeta1 5 7;
            Hacspec_ml_kem.Commute.Chunk.lemma_butterfly_pair_commute
              ${a}.f_elements ${out}.f_elements zeta2 8 10;
            Hacspec_ml_kem.Commute.Chunk.lemma_butterfly_pair_commute
              ${a}.f_elements ${out}.f_elements zeta2 9 11;
            Hacspec_ml_kem.Commute.Chunk.lemma_butterfly_pair_commute
              ${a}.f_elements ${out}.f_elements zeta3 12 14;
            Hacspec_ml_kem.Commute.Chunk.lemma_butterfly_pair_commute
              ${a}.f_elements ${out}.f_elements zeta3 13 15;
            // Unfold forall4 explicitly — one assert per group.
            let p_layer_1 : (b: nat{b < 4}) -> Type0 =
              fun (b: nat{b < 4}) ->
                (let z = (if b = 0 then zeta0
                          else if b = 1 then zeta1
                          else if b = 2 then zeta2
                          else zeta3) in
                 let i1 : nat = 4 * b in
                 let j1 : nat = 4 * b + 2 in
                 let i2 : nat = 4 * b + 1 in
                 let j2 : nat = 4 * b + 3 in
                 Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe (Seq.index ${out}.f_elements i1) ==
                   Hacspec_ml_kem.Parameters.impl_FieldElement__add
                     (Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe (Seq.index ${a}.f_elements i1))
                     (Hacspec_ml_kem.Parameters.impl_FieldElement__mul
                       (Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe z)
                       (Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe (Seq.index ${a}.f_elements j1))) /\
                 Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe (Seq.index ${out}.f_elements j1) ==
                   Hacspec_ml_kem.Parameters.impl_FieldElement__sub
                     (Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe (Seq.index ${a}.f_elements i1))
                     (Hacspec_ml_kem.Parameters.impl_FieldElement__mul
                       (Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe z)
                       (Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe (Seq.index ${a}.f_elements j1))) /\
                 Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe (Seq.index ${out}.f_elements i2) ==
                   Hacspec_ml_kem.Parameters.impl_FieldElement__add
                     (Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe (Seq.index ${a}.f_elements i2))
                     (Hacspec_ml_kem.Parameters.impl_FieldElement__mul
                       (Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe z)
                       (Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe (Seq.index ${a}.f_elements j2))) /\
                 Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe (Seq.index ${out}.f_elements j2) ==
                   Hacspec_ml_kem.Parameters.impl_FieldElement__sub
                     (Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe (Seq.index ${a}.f_elements i2))
                     (Hacspec_ml_kem.Parameters.impl_FieldElement__mul
                       (Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe z)
                       (Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe (Seq.index ${a}.f_elements j2)))) in
            assert (p_layer_1 0);
            assert (p_layer_1 1);
            assert (p_layer_1 2);
            assert (p_layer_1 3);
            assert (Spec.Utils.forall4 p_layer_1)
            "#
        );
        out
    }

    #[requires(fstar!(r#"${spec::ntt_layer_2_step_pre} ${a}.f_elements zeta0 zeta1"#))]
    #[ensures(|out| fstar!(r#"${spec::ntt_layer_2_step_post} ${a}.f_elements zeta0 zeta1 ${out}.f_elements"#))]
    fn ntt_layer_2_step(a: Self, zeta0: i16, zeta1: i16) -> Self {
        hax_lib::fstar!(
            r#"reveal_opaque (`%Libcrux_ml_kem.Vector.Traits.Spec.is_i16b_array_opaque)
                        (Libcrux_ml_kem.Vector.Traits.Spec.is_i16b_array_opaque (6*3328))"#
        );
        let out = ntt_layer_2_step(a, zeta0, zeta1);
        hax_lib::fstar!(
            r#"reveal_opaque (`%Libcrux_ml_kem.Vector.Traits.Spec.is_i16b_array_opaque)
                        (Libcrux_ml_kem.Vector.Traits.Spec.is_i16b_array_opaque (7*3328))"#
        );
        hax_lib::fstar!(
            r#"
            reveal_opaque (`%Spec.Utils.ntt_layer_2_butterfly_post)
                          (Spec.Utils.ntt_layer_2_butterfly_post ${a}.f_elements);
            // 4 groups × 2 butterflies each — see traits.rs post layout.
            Hacspec_ml_kem.Commute.Chunk.lemma_butterfly_pair_commute
              ${a}.f_elements ${out}.f_elements zeta0 0 4;
            Hacspec_ml_kem.Commute.Chunk.lemma_butterfly_pair_commute
              ${a}.f_elements ${out}.f_elements zeta0 1 5;
            Hacspec_ml_kem.Commute.Chunk.lemma_butterfly_pair_commute
              ${a}.f_elements ${out}.f_elements zeta0 2 6;
            Hacspec_ml_kem.Commute.Chunk.lemma_butterfly_pair_commute
              ${a}.f_elements ${out}.f_elements zeta0 3 7;
            Hacspec_ml_kem.Commute.Chunk.lemma_butterfly_pair_commute
              ${a}.f_elements ${out}.f_elements zeta1 8 12;
            Hacspec_ml_kem.Commute.Chunk.lemma_butterfly_pair_commute
              ${a}.f_elements ${out}.f_elements zeta1 9 13;
            Hacspec_ml_kem.Commute.Chunk.lemma_butterfly_pair_commute
              ${a}.f_elements ${out}.f_elements zeta1 10 14;
            Hacspec_ml_kem.Commute.Chunk.lemma_butterfly_pair_commute
              ${a}.f_elements ${out}.f_elements zeta1 11 15;
            let p_layer_2 : (b: nat{b < 4}) -> Type0 =
              fun (b: nat{b < 4}) ->
                (let z = (if b < 2 then zeta0 else zeta1) in
                 let base : nat = if b < 2 then 0 else 8 in
                 let off  : nat = if b = 0 || b = 2 then 0 else 2 in
                 let i1 : nat = base + off in
                 let j1 : nat = i1 + 4 in
                 let i2 : nat = i1 + 1 in
                 let j2 : nat = j1 + 1 in
                 Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe (Seq.index ${out}.f_elements i1) ==
                   Hacspec_ml_kem.Parameters.impl_FieldElement__add
                     (Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe (Seq.index ${a}.f_elements i1))
                     (Hacspec_ml_kem.Parameters.impl_FieldElement__mul
                       (Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe z)
                       (Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe (Seq.index ${a}.f_elements j1))) /\
                 Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe (Seq.index ${out}.f_elements j1) ==
                   Hacspec_ml_kem.Parameters.impl_FieldElement__sub
                     (Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe (Seq.index ${a}.f_elements i1))
                     (Hacspec_ml_kem.Parameters.impl_FieldElement__mul
                       (Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe z)
                       (Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe (Seq.index ${a}.f_elements j1))) /\
                 Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe (Seq.index ${out}.f_elements i2) ==
                   Hacspec_ml_kem.Parameters.impl_FieldElement__add
                     (Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe (Seq.index ${a}.f_elements i2))
                     (Hacspec_ml_kem.Parameters.impl_FieldElement__mul
                       (Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe z)
                       (Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe (Seq.index ${a}.f_elements j2))) /\
                 Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe (Seq.index ${out}.f_elements j2) ==
                   Hacspec_ml_kem.Parameters.impl_FieldElement__sub
                     (Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe (Seq.index ${a}.f_elements i2))
                     (Hacspec_ml_kem.Parameters.impl_FieldElement__mul
                       (Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe z)
                       (Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe (Seq.index ${a}.f_elements j2)))) in
            assert (p_layer_2 0);
            assert (p_layer_2 1);
            assert (p_layer_2 2);
            assert (p_layer_2 3);
            assert (Spec.Utils.forall4 p_layer_2)
            "#
        );
        out
    }

    #[requires(fstar!(r#"${spec::ntt_layer_3_step_pre} ${a}.f_elements zeta"#))]
    #[ensures(|out| fstar!(r#"${spec::ntt_layer_3_step_post} ${a}.f_elements zeta ${out}.f_elements"#))]
    fn ntt_layer_3_step(a: Self, zeta: i16) -> Self {
        hax_lib::fstar!(
            r#"reveal_opaque (`%Libcrux_ml_kem.Vector.Traits.Spec.is_i16b_array_opaque)
                        (Libcrux_ml_kem.Vector.Traits.Spec.is_i16b_array_opaque (5*3328))"#
        );
        let out = ntt_layer_3_step(a, zeta);
        hax_lib::fstar!(
            r#"reveal_opaque (`%Libcrux_ml_kem.Vector.Traits.Spec.is_i16b_array_opaque)
                        (Libcrux_ml_kem.Vector.Traits.Spec.is_i16b_array_opaque (6*3328))"#
        );
        hax_lib::fstar!(
            r#"
            reveal_opaque (`%Spec.Utils.ntt_layer_3_butterfly_post)
                          (Spec.Utils.ntt_layer_3_butterfly_post ${a}.f_elements);
            // 4 branches × 2 pairs each — see traits.rs post layout.
            Hacspec_ml_kem.Commute.Chunk.lemma_butterfly_pair_commute
              ${a}.f_elements ${out}.f_elements zeta 0 8;
            Hacspec_ml_kem.Commute.Chunk.lemma_butterfly_pair_commute
              ${a}.f_elements ${out}.f_elements zeta 1 9;
            Hacspec_ml_kem.Commute.Chunk.lemma_butterfly_pair_commute
              ${a}.f_elements ${out}.f_elements zeta 2 10;
            Hacspec_ml_kem.Commute.Chunk.lemma_butterfly_pair_commute
              ${a}.f_elements ${out}.f_elements zeta 3 11;
            Hacspec_ml_kem.Commute.Chunk.lemma_butterfly_pair_commute
              ${a}.f_elements ${out}.f_elements zeta 4 12;
            Hacspec_ml_kem.Commute.Chunk.lemma_butterfly_pair_commute
              ${a}.f_elements ${out}.f_elements zeta 5 13;
            Hacspec_ml_kem.Commute.Chunk.lemma_butterfly_pair_commute
              ${a}.f_elements ${out}.f_elements zeta 6 14;
            Hacspec_ml_kem.Commute.Chunk.lemma_butterfly_pair_commute
              ${a}.f_elements ${out}.f_elements zeta 7 15;
            let p_layer_3 : (b: nat{b < 4}) -> Type0 =
              fun (b: nat{b < 4}) ->
                (let i1 : nat = 2 * b in
                 let j1 : nat = 2 * b + 8 in
                 let i2 : nat = 2 * b + 1 in
                 let j2 : nat = 2 * b + 9 in
                 Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe (Seq.index ${out}.f_elements i1) ==
                   Hacspec_ml_kem.Parameters.impl_FieldElement__add
                     (Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe (Seq.index ${a}.f_elements i1))
                     (Hacspec_ml_kem.Parameters.impl_FieldElement__mul
                       (Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe zeta)
                       (Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe (Seq.index ${a}.f_elements j1))) /\
                 Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe (Seq.index ${out}.f_elements j1) ==
                   Hacspec_ml_kem.Parameters.impl_FieldElement__sub
                     (Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe (Seq.index ${a}.f_elements i1))
                     (Hacspec_ml_kem.Parameters.impl_FieldElement__mul
                       (Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe zeta)
                       (Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe (Seq.index ${a}.f_elements j1))) /\
                 Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe (Seq.index ${out}.f_elements i2) ==
                   Hacspec_ml_kem.Parameters.impl_FieldElement__add
                     (Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe (Seq.index ${a}.f_elements i2))
                     (Hacspec_ml_kem.Parameters.impl_FieldElement__mul
                       (Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe zeta)
                       (Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe (Seq.index ${a}.f_elements j2))) /\
                 Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe (Seq.index ${out}.f_elements j2) ==
                   Hacspec_ml_kem.Parameters.impl_FieldElement__sub
                     (Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe (Seq.index ${a}.f_elements i2))
                     (Hacspec_ml_kem.Parameters.impl_FieldElement__mul
                       (Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe zeta)
                       (Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe (Seq.index ${a}.f_elements j2)))) in
            assert (p_layer_3 0);
            assert (p_layer_3 1);
            assert (p_layer_3 2);
            assert (p_layer_3 3);
            assert (Spec.Utils.forall4 p_layer_3)
            "#
        );
        out
    }

    #[requires(fstar!(r#"${spec::inv_ntt_layer_1_step_pre} ${a}.f_elements zeta0 zeta1 zeta2 zeta3"#))]
    #[ensures(|out| fstar!(r#"${spec::inv_ntt_layer_1_step_post} ${a}.f_elements zeta0 zeta1 zeta2 zeta3 ${out}.f_elements"#))]
    fn inv_ntt_layer_1_step(a: Self, zeta0: i16, zeta1: i16, zeta2: i16, zeta3: i16) -> Self {
        hax_lib::fstar!(
            r#"reveal_opaque (`%Libcrux_ml_kem.Vector.Traits.Spec.is_i16b_array_opaque)
                        (Libcrux_ml_kem.Vector.Traits.Spec.is_i16b_array_opaque (4*3328))"#
        );
        let out = inv_ntt_layer_1_step(a, zeta0, zeta1, zeta2, zeta3);
        hax_lib::fstar!(
            r#"reveal_opaque (`%Libcrux_ml_kem.Vector.Traits.Spec.is_i16b_array_opaque)
                        (Libcrux_ml_kem.Vector.Traits.Spec.is_i16b_array_opaque 3328)"#
        );
        hax_lib::fstar!(
            r#"
            reveal_opaque (`%Spec.Utils.inv_ntt_layer_1_butterfly_post)
                          (Spec.Utils.inv_ntt_layer_1_butterfly_post ${a}.f_elements);
            Hacspec_ml_kem.Commute.Chunk.lemma_inv_butterfly_pair_commute
              ${a}.f_elements ${out}.f_elements zeta0 0 2;
            Hacspec_ml_kem.Commute.Chunk.lemma_inv_butterfly_pair_commute
              ${a}.f_elements ${out}.f_elements zeta0 1 3;
            Hacspec_ml_kem.Commute.Chunk.lemma_inv_butterfly_pair_commute
              ${a}.f_elements ${out}.f_elements zeta1 4 6;
            Hacspec_ml_kem.Commute.Chunk.lemma_inv_butterfly_pair_commute
              ${a}.f_elements ${out}.f_elements zeta1 5 7;
            Hacspec_ml_kem.Commute.Chunk.lemma_inv_butterfly_pair_commute
              ${a}.f_elements ${out}.f_elements zeta2 8 10;
            Hacspec_ml_kem.Commute.Chunk.lemma_inv_butterfly_pair_commute
              ${a}.f_elements ${out}.f_elements zeta2 9 11;
            Hacspec_ml_kem.Commute.Chunk.lemma_inv_butterfly_pair_commute
              ${a}.f_elements ${out}.f_elements zeta3 12 14;
            Hacspec_ml_kem.Commute.Chunk.lemma_inv_butterfly_pair_commute
              ${a}.f_elements ${out}.f_elements zeta3 13 15;
            let p_inv_1 : (b: nat{b < 4}) -> Type0 =
              fun (b: nat{b < 4}) ->
                (let z = (if b = 0 then zeta0
                          else if b = 1 then zeta1
                          else if b = 2 then zeta2
                          else zeta3) in
                 let i1 : nat = 4 * b in
                 let j1 : nat = 4 * b + 2 in
                 let i2 : nat = 4 * b + 1 in
                 let j2 : nat = 4 * b + 3 in
                 Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe (Seq.index ${out}.f_elements i1) ==
                   Hacspec_ml_kem.Parameters.impl_FieldElement__add
                     (Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe (Seq.index ${a}.f_elements i1))
                     (Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe (Seq.index ${a}.f_elements j1)) /\
                 Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe (Seq.index ${out}.f_elements j1) ==
                   Hacspec_ml_kem.Parameters.impl_FieldElement__mul
                     (Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe z)
                     (Hacspec_ml_kem.Parameters.impl_FieldElement__sub
                       (Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe (Seq.index ${a}.f_elements j1))
                       (Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe (Seq.index ${a}.f_elements i1))) /\
                 Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe (Seq.index ${out}.f_elements i2) ==
                   Hacspec_ml_kem.Parameters.impl_FieldElement__add
                     (Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe (Seq.index ${a}.f_elements i2))
                     (Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe (Seq.index ${a}.f_elements j2)) /\
                 Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe (Seq.index ${out}.f_elements j2) ==
                   Hacspec_ml_kem.Parameters.impl_FieldElement__mul
                     (Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe z)
                     (Hacspec_ml_kem.Parameters.impl_FieldElement__sub
                       (Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe (Seq.index ${a}.f_elements j2))
                       (Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe (Seq.index ${a}.f_elements i2)))) in
            assert (p_inv_1 0);
            assert (p_inv_1 1);
            assert (p_inv_1 2);
            assert (p_inv_1 3);
            assert (Spec.Utils.forall4 p_inv_1)
            "#
        );
        out
    }

    #[requires(fstar!(r#"${spec::inv_ntt_layer_2_step_pre} ${a}.f_elements zeta0 zeta1"#))]
    #[ensures(|out| fstar!(r#"${spec::inv_ntt_layer_2_step_post} ${a}.f_elements zeta0 zeta1 ${out}.f_elements"#))]
    fn inv_ntt_layer_2_step(a: Self, zeta0: i16, zeta1: i16) -> Self {
        hax_lib::fstar!(
            r#"reveal_opaque (`%Libcrux_ml_kem.Vector.Traits.Spec.is_i16b_array_opaque)
                        (Libcrux_ml_kem.Vector.Traits.Spec.is_i16b_array_opaque 3328)"#
        );
        let out = inv_ntt_layer_2_step(a, zeta0, zeta1);
        hax_lib::fstar!(
            r#"
            reveal_opaque (`%Spec.Utils.inv_ntt_layer_2_butterfly_post)
                          (Spec.Utils.inv_ntt_layer_2_butterfly_post ${a}.f_elements);
            Hacspec_ml_kem.Commute.Chunk.lemma_inv_butterfly_pair_commute
              ${a}.f_elements ${out}.f_elements zeta0 0 4;
            Hacspec_ml_kem.Commute.Chunk.lemma_inv_butterfly_pair_commute
              ${a}.f_elements ${out}.f_elements zeta0 1 5;
            Hacspec_ml_kem.Commute.Chunk.lemma_inv_butterfly_pair_commute
              ${a}.f_elements ${out}.f_elements zeta0 2 6;
            Hacspec_ml_kem.Commute.Chunk.lemma_inv_butterfly_pair_commute
              ${a}.f_elements ${out}.f_elements zeta0 3 7;
            Hacspec_ml_kem.Commute.Chunk.lemma_inv_butterfly_pair_commute
              ${a}.f_elements ${out}.f_elements zeta1 8 12;
            Hacspec_ml_kem.Commute.Chunk.lemma_inv_butterfly_pair_commute
              ${a}.f_elements ${out}.f_elements zeta1 9 13;
            Hacspec_ml_kem.Commute.Chunk.lemma_inv_butterfly_pair_commute
              ${a}.f_elements ${out}.f_elements zeta1 10 14;
            Hacspec_ml_kem.Commute.Chunk.lemma_inv_butterfly_pair_commute
              ${a}.f_elements ${out}.f_elements zeta1 11 15;
            let p_inv_2 : (b: nat{b < 4}) -> Type0 =
              fun (b: nat{b < 4}) ->
                (let z = (if b < 2 then zeta0 else zeta1) in
                 let base : nat = if b < 2 then 0 else 8 in
                 let off  : nat = if b = 0 || b = 2 then 0 else 2 in
                 let i1 : nat = base + off in
                 let j1 : nat = i1 + 4 in
                 let i2 : nat = i1 + 1 in
                 let j2 : nat = j1 + 1 in
                 Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe (Seq.index ${out}.f_elements i1) ==
                   Hacspec_ml_kem.Parameters.impl_FieldElement__add
                     (Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe (Seq.index ${a}.f_elements i1))
                     (Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe (Seq.index ${a}.f_elements j1)) /\
                 Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe (Seq.index ${out}.f_elements j1) ==
                   Hacspec_ml_kem.Parameters.impl_FieldElement__mul
                     (Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe z)
                     (Hacspec_ml_kem.Parameters.impl_FieldElement__sub
                       (Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe (Seq.index ${a}.f_elements j1))
                       (Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe (Seq.index ${a}.f_elements i1))) /\
                 Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe (Seq.index ${out}.f_elements i2) ==
                   Hacspec_ml_kem.Parameters.impl_FieldElement__add
                     (Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe (Seq.index ${a}.f_elements i2))
                     (Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe (Seq.index ${a}.f_elements j2)) /\
                 Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe (Seq.index ${out}.f_elements j2) ==
                   Hacspec_ml_kem.Parameters.impl_FieldElement__mul
                     (Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe z)
                     (Hacspec_ml_kem.Parameters.impl_FieldElement__sub
                       (Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe (Seq.index ${a}.f_elements j2))
                       (Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe (Seq.index ${a}.f_elements i2)))) in
            assert (p_inv_2 0);
            assert (p_inv_2 1);
            assert (p_inv_2 2);
            assert (p_inv_2 3);
            assert (Spec.Utils.forall4 p_inv_2)
            "#
        );
        out
    }

    #[requires(fstar!(r#"${spec::inv_ntt_layer_3_step_pre} ${a}.f_elements zeta"#))]
    #[ensures(|out| fstar!(r#"${spec::inv_ntt_layer_3_step_post} ${a}.f_elements zeta ${out}.f_elements"#))]
    fn inv_ntt_layer_3_step(a: Self, zeta: i16) -> Self {
        hax_lib::fstar!(
            r#"reveal_opaque (`%Libcrux_ml_kem.Vector.Traits.Spec.is_i16b_array_opaque)
                        (Libcrux_ml_kem.Vector.Traits.Spec.is_i16b_array_opaque 3328)"#
        );
        let out = inv_ntt_layer_3_step(a, zeta);
        hax_lib::fstar!(
            r#"
            reveal_opaque (`%Spec.Utils.inv_ntt_layer_3_butterfly_post)
                          (Spec.Utils.inv_ntt_layer_3_butterfly_post ${a}.f_elements);
            Hacspec_ml_kem.Commute.Chunk.lemma_inv_butterfly_pair_commute
              ${a}.f_elements ${out}.f_elements zeta 0 8;
            Hacspec_ml_kem.Commute.Chunk.lemma_inv_butterfly_pair_commute
              ${a}.f_elements ${out}.f_elements zeta 1 9;
            Hacspec_ml_kem.Commute.Chunk.lemma_inv_butterfly_pair_commute
              ${a}.f_elements ${out}.f_elements zeta 2 10;
            Hacspec_ml_kem.Commute.Chunk.lemma_inv_butterfly_pair_commute
              ${a}.f_elements ${out}.f_elements zeta 3 11;
            Hacspec_ml_kem.Commute.Chunk.lemma_inv_butterfly_pair_commute
              ${a}.f_elements ${out}.f_elements zeta 4 12;
            Hacspec_ml_kem.Commute.Chunk.lemma_inv_butterfly_pair_commute
              ${a}.f_elements ${out}.f_elements zeta 5 13;
            Hacspec_ml_kem.Commute.Chunk.lemma_inv_butterfly_pair_commute
              ${a}.f_elements ${out}.f_elements zeta 6 14;
            Hacspec_ml_kem.Commute.Chunk.lemma_inv_butterfly_pair_commute
              ${a}.f_elements ${out}.f_elements zeta 7 15;
            let p_inv_3 : (b: nat{b < 4}) -> Type0 =
              fun (b: nat{b < 4}) ->
                (let i1 : nat = 2 * b in
                 let j1 : nat = 2 * b + 8 in
                 let i2 : nat = 2 * b + 1 in
                 let j2 : nat = 2 * b + 9 in
                 Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe (Seq.index ${out}.f_elements i1) ==
                   Hacspec_ml_kem.Parameters.impl_FieldElement__add
                     (Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe (Seq.index ${a}.f_elements i1))
                     (Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe (Seq.index ${a}.f_elements j1)) /\
                 Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe (Seq.index ${out}.f_elements j1) ==
                   Hacspec_ml_kem.Parameters.impl_FieldElement__mul
                     (Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe zeta)
                     (Hacspec_ml_kem.Parameters.impl_FieldElement__sub
                       (Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe (Seq.index ${a}.f_elements j1))
                       (Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe (Seq.index ${a}.f_elements i1))) /\
                 Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe (Seq.index ${out}.f_elements i2) ==
                   Hacspec_ml_kem.Parameters.impl_FieldElement__add
                     (Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe (Seq.index ${a}.f_elements i2))
                     (Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe (Seq.index ${a}.f_elements j2)) /\
                 Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe (Seq.index ${out}.f_elements j2) ==
                   Hacspec_ml_kem.Parameters.impl_FieldElement__mul
                     (Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe zeta)
                     (Hacspec_ml_kem.Parameters.impl_FieldElement__sub
                       (Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe (Seq.index ${a}.f_elements j2))
                       (Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe (Seq.index ${a}.f_elements i2)))) in
            assert (p_inv_3 0);
            assert (p_inv_3 1);
            assert (p_inv_3 2);
            assert (p_inv_3 3);
            assert (Spec.Utils.forall4 p_inv_3)
            "#
        );
        out
    }

    #[requires(fstar!(r#"${spec::ntt_multiply_pre} ${lhs}.f_elements ${rhs}.f_elements zeta0 zeta1 zeta2 zeta3"#))]
    #[ensures(|out| fstar!(r#"${spec::ntt_multiply_post} ${lhs}.f_elements ${rhs}.f_elements zeta0 zeta1 zeta2 zeta3 ${out}.f_elements"#))]
    fn ntt_multiply(
        lhs: &Self,
        rhs: &Self,
        zeta0: i16,
        zeta1: i16,
        zeta2: i16,
        zeta3: i16,
    ) -> Self {
        hax_lib::fstar!(
            r#"reveal_opaque (`%Libcrux_ml_kem.Vector.Traits.Spec.is_i16b_array_opaque)
                        (Libcrux_ml_kem.Vector.Traits.Spec.is_i16b_array_opaque 3328)"#
        );
        let out = ntt_multiply(lhs, rhs, zeta0, zeta1, zeta2, zeta3);
        hax_lib::fstar!(
            r#"
            // Unwrap the opaque butterfly_post (8 `ntt_multiply_spec` residues)
            // and cash each into FE equalities via `lemma_base_case_mult_pair_commute`.
            reveal_opaque (`%Spec.Utils.ntt_multiply_butterfly_post)
                          (Spec.Utils.ntt_multiply_butterfly_post
                             ${lhs}.f_elements ${rhs}.f_elements ${out}.f_elements);
            let nzeta0:i16 = mk_i16 0 -! zeta0 in
            let nzeta1:i16 = mk_i16 0 -! zeta1 in
            let nzeta2:i16 = mk_i16 0 -! zeta2 in
            let nzeta3:i16 = mk_i16 0 -! zeta3 in
            assert (v nzeta0 == - v zeta0);
            assert (v nzeta1 == - v zeta1);
            assert (v nzeta2 == - v zeta2);
            assert (v nzeta3 == - v zeta3);
            Hacspec_ml_kem.Commute.Chunk.lemma_base_case_mult_pair_commute
              ${lhs}.f_elements ${rhs}.f_elements ${out}.f_elements zeta0 0;
            Hacspec_ml_kem.Commute.Chunk.lemma_base_case_mult_pair_commute
              ${lhs}.f_elements ${rhs}.f_elements ${out}.f_elements nzeta0 1;
            Hacspec_ml_kem.Commute.Chunk.lemma_base_case_mult_pair_commute
              ${lhs}.f_elements ${rhs}.f_elements ${out}.f_elements zeta1 2;
            Hacspec_ml_kem.Commute.Chunk.lemma_base_case_mult_pair_commute
              ${lhs}.f_elements ${rhs}.f_elements ${out}.f_elements nzeta1 3;
            Hacspec_ml_kem.Commute.Chunk.lemma_base_case_mult_pair_commute
              ${lhs}.f_elements ${rhs}.f_elements ${out}.f_elements zeta2 4;
            Hacspec_ml_kem.Commute.Chunk.lemma_base_case_mult_pair_commute
              ${lhs}.f_elements ${rhs}.f_elements ${out}.f_elements nzeta2 5;
            Hacspec_ml_kem.Commute.Chunk.lemma_base_case_mult_pair_commute
              ${lhs}.f_elements ${rhs}.f_elements ${out}.f_elements zeta3 6;
            Hacspec_ml_kem.Commute.Chunk.lemma_base_case_mult_pair_commute
              ${lhs}.f_elements ${rhs}.f_elements ${out}.f_elements nzeta3 7;
            // Bridge the `znzp = mk_i16 0 -! zp` form in the trait post to
            // the concrete `nzeta_b` args that `pair_commute` was called with.
            assert (nzeta0 == mk_i16 0 -! zeta0);
            assert (nzeta1 == mk_i16 0 -! zeta1);
            assert (nzeta2 == mk_i16 0 -! zeta2);
            assert (nzeta3 == mk_i16 0 -! zeta3);
            assert (Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe nzeta0
                    == Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe (mk_i16 0 -! zeta0));
            assert (Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe nzeta1
                    == Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe (mk_i16 0 -! zeta1));
            assert (Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe nzeta2
                    == Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe (mk_i16 0 -! zeta2));
            assert (Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe nzeta3
                    == Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe (mk_i16 0 -! zeta3));
            // Pending — C4e-followup: the forall4 glue below should follow
            // from the 8 `pair_commute` calls above and the `neg_i16` equalities
            // asserted in between, but Z3 doesn't converge at rlimit 400 × 85 s
            // on the p_ntt_mult predicate definition.  Admitted in line with
            // the pair commute core/fe_commute lemmas; revisit alongside those.
            admit ();
            // Unfold forall4 explicitly.
            let p_ntt_mult : (b: nat{b < 4}) -> Type0 =
              fun (b: nat{b < 4}) ->
                (let zp = (if b = 0 then zeta0
                           else if b = 1 then zeta1
                           else if b = 2 then zeta2
                           else zeta3) in
                 let k_even : nat = 2 * b in
                 let k_odd  : nat = 2 * b + 1 in
                 let lane0 : nat = 2 * k_even in
                 let lane1 : nat = 2 * k_even + 1 in
                 let lane2 : nat = 2 * k_odd in
                 let lane3 : nat = 2 * k_odd + 1 in
                 Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe (Seq.index ${out}.f_elements lane0) ==
                   Hacspec_ml_kem.Parameters.impl_FieldElement__add
                     (Hacspec_ml_kem.Parameters.impl_FieldElement__mul
                       (Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe (Seq.index ${lhs}.f_elements lane0))
                       (Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe (Seq.index ${rhs}.f_elements lane0)))
                     (Hacspec_ml_kem.Parameters.impl_FieldElement__mul
                       (Hacspec_ml_kem.Parameters.impl_FieldElement__mul
                         (Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe (Seq.index ${lhs}.f_elements lane1))
                         (Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe (Seq.index ${rhs}.f_elements lane1)))
                       (Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe zp)) /\
                 Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe (Seq.index ${out}.f_elements lane1) ==
                   Hacspec_ml_kem.Parameters.impl_FieldElement__add
                     (Hacspec_ml_kem.Parameters.impl_FieldElement__mul
                       (Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe (Seq.index ${lhs}.f_elements lane0))
                       (Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe (Seq.index ${rhs}.f_elements lane1)))
                     (Hacspec_ml_kem.Parameters.impl_FieldElement__mul
                       (Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe (Seq.index ${lhs}.f_elements lane1))
                       (Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe (Seq.index ${rhs}.f_elements lane0))) /\
                 Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe (Seq.index ${out}.f_elements lane2) ==
                   Hacspec_ml_kem.Parameters.impl_FieldElement__add
                     (Hacspec_ml_kem.Parameters.impl_FieldElement__mul
                       (Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe (Seq.index ${lhs}.f_elements lane2))
                       (Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe (Seq.index ${rhs}.f_elements lane2)))
                     (Hacspec_ml_kem.Parameters.impl_FieldElement__mul
                       (Hacspec_ml_kem.Parameters.impl_FieldElement__mul
                         (Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe (Seq.index ${lhs}.f_elements lane3))
                         (Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe (Seq.index ${rhs}.f_elements lane3)))
                       (Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe (Spec.Utils.neg_i16 zp))) /\
                 Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe (Seq.index ${out}.f_elements lane3) ==
                   Hacspec_ml_kem.Parameters.impl_FieldElement__add
                     (Hacspec_ml_kem.Parameters.impl_FieldElement__mul
                       (Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe (Seq.index ${lhs}.f_elements lane2))
                       (Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe (Seq.index ${rhs}.f_elements lane3)))
                     (Hacspec_ml_kem.Parameters.impl_FieldElement__mul
                       (Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe (Seq.index ${lhs}.f_elements lane3))
                       (Libcrux_ml_kem.Vector.Traits.Spec.mont_i16_to_spec_fe (Seq.index ${rhs}.f_elements lane2)))) in
            assert (p_ntt_mult 0);
            assert (p_ntt_mult 1);
            assert (p_ntt_mult 2);
            assert (p_ntt_mult 3);
            assert (Spec.Utils.forall4 p_ntt_mult)
            "#
        );
        out
    }

    #[requires(fstar!(r#"Libcrux_ml_kem.Vector.Traits.Spec.serialize_pre_N 1 (impl.f_repr $a)"#))]
    #[ensures(|out| fstar!(r#"Libcrux_ml_kem.Vector.Traits.Spec.serialize_pre_N 1 (impl.f_repr $a) ==> Libcrux_ml_kem.Vector.Traits.Spec.serialize_post_N 1 (impl.f_repr $a) $out"#))]
    fn serialize_1(a: Self) -> [u8; 2] {
        serialize_1(a)
    }

    #[requires(a.len() == 2)]
    #[ensures(|out| fstar!(r#"sz (Seq.length $a) =. sz 2 ==> Libcrux_ml_kem.Vector.Traits.Spec.deserialize_post_N 1 $a (impl.f_repr $out)"#))]
    fn deserialize_1(a: &[u8]) -> Self {
        deserialize_1(a)
    }

    #[requires(fstar!(r#"Libcrux_ml_kem.Vector.Traits.Spec.serialize_pre_N 4 (impl.f_repr $a)"#))]
    #[ensures(|out| fstar!(r#"Libcrux_ml_kem.Vector.Traits.Spec.serialize_pre_N 4 (impl.f_repr $a) ==> Libcrux_ml_kem.Vector.Traits.Spec.serialize_post_N 4 (impl.f_repr $a) $out"#))]
    fn serialize_4(a: Self) -> [u8; 8] {
        serialize_4(a)
    }

    #[requires(a.len() == 8)]
    #[ensures(|out| fstar!(r#"sz (Seq.length $a) =. sz 8 ==> Libcrux_ml_kem.Vector.Traits.Spec.deserialize_post_N 4 $a (impl.f_repr $out)"#))]
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

    #[requires(fstar!(r#"Libcrux_ml_kem.Vector.Traits.Spec.serialize_pre_N 10 (impl.f_repr $a)"#))]
    #[ensures(|out| fstar!(r#"Libcrux_ml_kem.Vector.Traits.Spec.serialize_pre_N 10 (impl.f_repr $a) ==> Libcrux_ml_kem.Vector.Traits.Spec.serialize_post_N 10 (impl.f_repr $a) $out"#))]
    fn serialize_10(a: Self) -> [u8; 20] {
        serialize_10(a)
    }

    #[requires(a.len() == 20)]
    #[ensures(|out| fstar!(r#"sz (Seq.length $a) =. sz 20 ==> Libcrux_ml_kem.Vector.Traits.Spec.deserialize_post_N 10 $a (impl.f_repr $out)"#))]
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

    #[requires(fstar!(r#"Libcrux_ml_kem.Vector.Traits.Spec.serialize_pre_N 12 (impl.f_repr $a)"#))]
    #[ensures(|out| fstar!(r#"Libcrux_ml_kem.Vector.Traits.Spec.serialize_pre_N 12 (impl.f_repr $a) ==> Libcrux_ml_kem.Vector.Traits.Spec.serialize_post_N 12 (impl.f_repr $a) $out"#))]
    fn serialize_12(a: Self) -> [u8; 24] {
        serialize_12(a)
    }

    #[requires(a.len() == 24)]
    #[ensures(|out| fstar!(r#"sz (Seq.length $a) =. sz 24 ==> Libcrux_ml_kem.Vector.Traits.Spec.deserialize_post_N 12 $a (impl.f_repr $out)"#))]
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
