pub const MONTGOMERY_R_SQUARED_MOD_FIELD_MODULUS: i16 = 1353;
pub const FIELD_MODULUS: i16 = 3329;
pub const FIELD_ELEMENTS_IN_VECTOR: usize = 16;
pub const INVERSE_OF_MODULUS_MOD_MONTGOMERY_R: u32 = 62209; // FIELD_MODULUS^{-1} mod MONTGOMERY_R
pub const BARRETT_SHIFT: i32 = 26;
pub const BARRETT_R: i32 = 1 << BARRETT_SHIFT;

#[cfg(hax)]
use hax_lib::prop::ToProp;

// We define a trait that allows us to talk about the contents of a vector.
// This is used extensively in pre- and post-conditions to reason about the code.
// The trait is duplicated for Eurydice to avoid the trait inheritance between Operations and Repr
// This is needed because of this issue: https://github.com/AeneasVerif/eurydice/issues/111
#[cfg(hax)]
#[hax_lib::attributes]
pub trait Repr: Copy + Clone {
    #[requires(true)]
    fn repr(&self) -> [i16; 16];
}

#[cfg(any(eurydice, not(hax)))]
pub trait Repr {}

#[cfg(hax)]
#[allow(dead_code, unused_variables)]
pub(crate) mod spec {

    pub(crate) fn add_pre(lhs: &[i16; 16], rhs: &[i16; 16]) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#"forall i.
            Spec.Utils.is_intb (pow2 15 - 1) 
                (v (Seq.index ${lhs} i) + v (Seq.index ${rhs} i))"#
        )
    }

    pub(crate) fn add_post(lhs: &[i16; 16], rhs: &[i16; 16], result: &[i16; 16]) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#"(forall i. 
                v (Seq.index ${result} i) == 
                v (Seq.index ${lhs} i) + v (Seq.index ${rhs} i))"#
        )
    }

    pub(crate) fn sub_pre(lhs: &[i16; 16], rhs: &[i16; 16]) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#"forall i. 
                Spec.Utils.is_intb (pow2 15 - 1) 
                (v (Seq.index ${lhs} i) - v (Seq.index ${rhs} i))"#
        )
    }

    pub(crate) fn sub_post(lhs: &[i16; 16], rhs: &[i16; 16], result: &[i16; 16]) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#"(forall i. 
                v (Seq.index ${result} i) == 
                v (Seq.index ${lhs} i) - v (Seq.index ${rhs} i))"#
        )
    }

    pub(crate) fn negate_pre(vec: &[i16; 16]) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#"forall i. 
                Spec.Utils.is_intb (pow2 15 - 1) (v (Seq.index ${vec} i))"#
        )
    }

    pub(crate) fn negate_post(vec: &[i16; 16], result: &[i16; 16]) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#"(forall i. 
                v (Seq.index ${result} i) == 
                - (v (Seq.index ${vec} i)))"#
        )
    }

    pub(crate) fn multiply_by_constant_pre(vec: &[i16; 16], c: i16) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#"forall i. 
                Spec.Utils.is_intb (pow2 15 - 1) (v (Seq.index ${vec} i) * v $c)"#
        )
    }

    pub(crate) fn multiply_by_constant_post(
        vec: &[i16; 16],
        c: i16,
        result: &[i16; 16],
    ) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#"(forall i.
                v (Seq.index ${result} i) == 
                v (Seq.index ${vec} i) * v $c)"#
        )
    }

    pub(crate) fn bitwise_and_with_constant_constant_post(
        vec: &[i16; 16],
        c: i16,
        result: &[i16; 16],
    ) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#"$result == 
               Spec.Utils.map_array (fun x -> x &. $c) $vec"#
        )
    }

    pub(crate) fn shift_right_post(
        vec: &[i16; 16],
        shift_by: i32,
        result: &[i16; 16],
    ) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#"(v $shift_by >= 0 /\ v $shift_by < 16) ==>
                $result == 
                Spec.Utils.map_array (fun x -> x >>! ${shift_by}) $vec"#
        )
    }

    pub(crate) fn cond_subtract_3329_pre(vec: &[i16; 16]) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(r#"Spec.Utils.is_i16b_array_opaque (pow2 12 - 1) $vec"#)
    }

    pub(crate) fn cond_subtract_3329_post(vec: &[i16; 16], result: &[i16; 16]) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#"$result == 
                Spec.Utils.map_array (fun x -> 
                    if x >=. (mk_i16 3329) then 
                        x -! (mk_i16 3329) 
                    else x) $vec"#
        )
    }

    pub(crate) fn barrett_reduce_pre(vec: &[i16; 16]) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(r#"Spec.Utils.is_i16b_array_opaque 28296 $vec"#)
    }

    pub(crate) fn barrett_reduce_post(vec: &[i16; 16], result: &[i16; 16]) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#"Spec.Utils.is_i16b_array_opaque 3328 ${result} /\
                (forall i. (v (Seq.index ${result} i) % 3329) == 
                           (v (Seq.index ${vec} i) % 3329))"#
        )
    }

    pub(crate) fn montgomery_multiply_by_constant_pre(vec: &[i16; 16], c: i16) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(r#"Spec.Utils.is_i16b 1664 c"#)
    }

    pub(crate) fn montgomery_multiply_by_constant_post(
        vec: &[i16; 16],
        c: i16,
        result: &[i16; 16],
    ) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#"Spec.Utils.is_i16b_array_opaque 3328 ${result} /\
                (forall i. ((v (Seq.index ${result} i) % 3329)==
                            (v (Seq.index ${vec} i) * v ${c} * 169) % 3329))"#
        )
    }

    pub(crate) fn to_unsigned_representative_pre(vec: &[i16; 16]) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(r#"Spec.Utils.is_i16b_array_opaque 3328 ${vec}"#)
    }

    pub(crate) fn to_unsigned_representative_post(
        vec: &[i16; 16],
        result: &[i16; 16],
    ) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#"forall i.
                let x = Seq.index ${vec} i in
                let y = Seq.index ${result} i in
                (v y >= 0 /\ v y <= 3328 /\ (v y % 3329 == v x % 3329))"#
        )
    }

    pub(crate) fn compress_1_pre(vec: &[i16; 16]) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#"forall i. 
                v (Seq.index ${vec} i) >= 0 /\
                v (Seq.index ${vec} i) < 3329"#
        )
    }

    pub(crate) fn compress_1_post(vec: &[i16; 16], result: &[i16; 16]) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(r#"forall i. bounded (Seq.index ${result} i) 1"#)
    }

    pub(crate) fn compress_pre(vec: &[i16; 16], coefficient_bits: i32) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#"(v $coefficient_bits == 4 \/
                v $coefficient_bits == 5 \/
                v $coefficient_bits == 10 \/
                v $coefficient_bits == 11) /\
                (forall i. 
                    v (Seq.index $vec i) >= 0 /\
                    v (Seq.index $vec i) < 3329)"#
        )
    }

    pub(crate) fn compress_post(
        vec: &[i16; 16],
        coefficient_bits: i32,
        result: &[i16; 16],
    ) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#"(v $coefficient_bits == 4 \/
                v $coefficient_bits == 5 \/
                v $coefficient_bits == 10 \/
                v $coefficient_bits == 11) ==>
                (forall i. bounded (Seq.index ${result} i) (v $coefficient_bits))"#
        )
    }

    pub(crate) fn decompress_1_pre(vec: &[i16; 16]) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#"forall i. 
               let x = Seq.index ${vec} i in 
               (x == mk_i16 0 \/ x == mk_i16 1)"#
        )
    }

    pub(crate) fn decompress_ciphertext_coefficient_pre(
        vec: &[i16; 16],
        coefficient_bits: i32,
    ) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#"(v $coefficient_bits == 4 \/
                v $coefficient_bits == 5 \/
                v $coefficient_bits == 10 \/
                v $coefficient_bits == 11) /\
                (forall i. 
                    v (Seq.index $vec i) >= 0 /\
                    v (Seq.index $vec i) < pow2 (v $coefficient_bits))"#
        )
    }

    pub(crate) fn ntt_layer_1_step_pre(
        vec: &[i16; 16],
        zeta0: i16,
        zeta1: i16,
        zeta2: i16,
        zeta3: i16,
    ) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#" Spec.Utils.is_i16b 1664 $zeta0 /\ Spec.Utils.is_i16b 1664 $zeta1 /\ 
                Spec.Utils.is_i16b 1664 $zeta2 /\ Spec.Utils.is_i16b 1664 $zeta3 /\
                Spec.Utils.is_i16b_array_opaque (7*3328) ${vec}"#
        )
    }

    pub(crate) fn ntt_layer_1_step_post(
        vec: &[i16; 16],
        zeta0: i16,
        zeta1: i16,
        zeta2: i16,
        zeta3: i16,
        result: &[i16; 16],
    ) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(r#"Spec.Utils.is_i16b_array_opaque(8*3328) ${result}"#)
    }

    pub(crate) fn ntt_layer_2_step_pre(vec: &[i16; 16], zeta0: i16, zeta1: i16) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#" Spec.Utils.is_i16b 1664 $zeta0 /\ Spec.Utils.is_i16b 1664 $zeta1 /\ 
                Spec.Utils.is_i16b_array_opaque (6*3328) ${vec}"#
        )
    }

    pub(crate) fn ntt_layer_2_step_post(
        vec: &[i16; 16],
        zeta0: i16,
        zeta1: i16,
        result: &[i16; 16],
    ) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(r#"Spec.Utils.is_i16b_array_opaque (7*3328) ${result}"#)
    }

    pub(crate) fn ntt_layer_3_step_pre(vec: &[i16; 16], zeta0: i16) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#" Spec.Utils.is_i16b 1664 $zeta0 /\
                Spec.Utils.is_i16b_array_opaque (5*3328) ${vec}"#
        )
    }

    pub(crate) fn ntt_layer_3_step_post(
        vec: &[i16; 16],
        zeta0: i16,
        result: &[i16; 16],
    ) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(r#"Spec.Utils.is_i16b_array_opaque (6*3328) ${result}"#)
    }

    pub(crate) fn inv_ntt_layer_1_step_pre(
        vec: &[i16; 16],
        zeta0: i16,
        zeta1: i16,
        zeta2: i16,
        zeta3: i16,
    ) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#" Spec.Utils.is_i16b 1664 zeta0 /\ Spec.Utils.is_i16b 1664 zeta1 /\ 
                Spec.Utils.is_i16b 1664 zeta2 /\ Spec.Utils.is_i16b 1664 zeta3 /\
                Spec.Utils.is_i16b_array_opaque (4*3328) ${vec}"#
        )
    }

    pub(crate) fn inv_ntt_layer_1_step_post(
        vec: &[i16; 16],
        zeta0: i16,
        zeta1: i16,
        zeta2: i16,
        zeta3: i16,
        result: &[i16; 16],
    ) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(r#"Spec.Utils.is_i16b_array_opaque 3328 ${result}"#)
    }

    pub(crate) fn inv_ntt_layer_2_step_pre(
        vec: &[i16; 16],
        zeta0: i16,
        zeta1: i16,
    ) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#" Spec.Utils.is_i16b 1664 zeta0 /\ Spec.Utils.is_i16b 1664 zeta1 /\ 
                Spec.Utils.is_i16b_array_opaque 3328 ${vec}"#
        )
    }

    pub(crate) fn inv_ntt_layer_2_step_post(
        vec: &[i16; 16],
        zeta0: i16,
        zeta1: i16,
        result: &[i16; 16],
    ) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(r#"Spec.Utils.is_i16b_array_opaque 3328 ${result}"#)
    }

    pub(crate) fn inv_ntt_layer_3_step_pre(vec: &[i16; 16], zeta0: i16) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#" Spec.Utils.is_i16b 1664 $zeta0 /\
                Spec.Utils.is_i16b_array_opaque 3328 ${vec}"#
        )
    }

    pub(crate) fn inv_ntt_layer_3_step_post(
        vec: &[i16; 16],
        zeta0: i16,
        result: &[i16; 16],
    ) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(r#"Spec.Utils.is_i16b_array_opaque 3328 ${result}"#)
    }

    pub(crate) fn ntt_multiply_pre(
        lhs: &[i16; 16],
        rhs: &[i16; 16],
        zeta0: i16,
        zeta1: i16,
        zeta2: i16,
        zeta3: i16,
    ) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#" Spec.Utils.is_i16b 1664 zeta0 /\ Spec.Utils.is_i16b 1664 zeta1 /\
                Spec.Utils.is_i16b 1664 zeta2 /\ Spec.Utils.is_i16b 1664 zeta3 /\
                Spec.Utils.is_i16b_array_opaque 3328 ${lhs} /\
                Spec.Utils.is_i16b_array_opaque 3328 ${rhs} "#
        )
    }

    pub(crate) fn ntt_multiply_post(
        lhs: &[i16; 16],
        rhs: &[i16; 16],
        zeta0: i16,
        zeta1: i16,
        zeta2: i16,
        zeta3: i16,
        result: &[i16; 16],
    ) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(r#"Spec.Utils.is_i16b_array_opaque 3328 ${result}"#)
    }

    pub(crate) fn serialize_1_pre(vec: &[i16; 16]) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#"
            Spec.MLKEM.serialize_pre 1 $vec"#
        )
    }

    pub(crate) fn serialize_1_post(vec: &[i16; 16], result: &[u8]) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#"   
            Seq.length ${result} == 2 /\
            (Spec.MLKEM.serialize_pre 1 $vec ==> 
               Spec.MLKEM.serialize_post 1 ${vec} ${result})"#
        )
    }

    pub(crate) fn deserialize_1_pre(input: &[u8]) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(r#"Seq.length ${input} == 2"#)
    }

    pub(crate) fn deserialize_1_post(input: &[u8], result: &[i16; 16]) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#"
            Seq.length ${input} == 2 ==>
            Spec.MLKEM.deserialize_post 1 ${input} ${result}"#
        )
    }

    pub(crate) fn serialize_4_pre(vec: &[i16; 16]) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#"
            Spec.MLKEM.serialize_pre 4 $vec"#
        )
    }

    pub(crate) fn serialize_4_post(vec: &[i16; 16], result: &[u8]) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#"   
            Seq.length ${result} == 8 /\
            (Spec.MLKEM.serialize_pre 4 $vec ==> 
               Spec.MLKEM.serialize_post 4 ${vec} ${result})"#
        )
    }

    pub(crate) fn deserialize_4_pre(input: &[u8]) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(r#"Seq.length ${input} == 8"#)
    }

    pub(crate) fn deserialize_4_post(input: &[u8], result: &[i16; 16]) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#"
            Seq.length ${input} == 8 ==>
            Spec.MLKEM.deserialize_post 4 ${input} ${result}"#
        )
    }

    pub(crate) fn serialize_10_pre(vec: &[i16; 16]) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#" 
            Spec.MLKEM.serialize_pre 10 $vec"#
        )
    }

    pub(crate) fn serialize_10_post(vec: &[i16; 16], result: &[u8]) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#"   
            Seq.length ${result} == 20 /\
            (Spec.MLKEM.serialize_pre 10 $vec ==> 
               Spec.MLKEM.serialize_post 10 ${vec} ${result})"#
        )
    }

    pub(crate) fn deserialize_10_pre(input: &[u8]) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(r#"Seq.length ${input} == 20"#)
    }

    pub(crate) fn deserialize_10_post(input: &[u8], result: &[i16; 16]) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#"
            Seq.length ${input} == 20 ==>
            Spec.MLKEM.deserialize_post 10 ${input} ${result}"#
        )
    }

    pub(crate) fn serialize_12_pre(vec: &[i16; 16]) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#" 
            Spec.MLKEM.serialize_pre 12 $vec"#
        )
    }

    pub(crate) fn serialize_12_post(vec: &[i16; 16], result: &[u8]) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#"   
            Seq.length ${result} == 24 /\
            (Spec.MLKEM.serialize_pre 12 $vec ==> 
               Spec.MLKEM.serialize_post 12 ${vec} ${result})"#
        )
    }

    pub(crate) fn deserialize_12_pre(input: &[u8]) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(r#"Seq.length ${input} == 24"#)
    }

    pub(crate) fn deserialize_12_post(input: &[u8], result: &[i16; 16]) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#"
            Seq.length ${input} == 24 ==>
            Spec.MLKEM.deserialize_post 12 ${input} ${result}"#
        )
    }
}

#[hax_lib::attributes]
pub trait Operations: Copy + Clone + Repr {
    #[allow(non_snake_case)]
    #[requires(true)]
    #[ensures(|result| result.repr() == [0i16; 16])]
    fn ZERO() -> Self;

    #[requires(array.len() == 16)]
    #[ensures(|result| result.repr() == *array)]
    fn from_i16_array(array: &[i16]) -> Self;

    #[requires(true)]
    #[ensures(|result| result == x.repr())]
    fn to_i16_array(x: Self) -> [i16; 16];

    #[requires(array.len() >= 32)]
    fn from_bytes(array: &[u8]) -> Self;

    #[requires(bytes.len() >= 32)]
    #[ensures(|_| future(bytes).len() == bytes.len())]
    fn to_bytes(x: Self, bytes: &mut [u8]);

    // Basic arithmetic
    #[requires(spec::add_pre(&lhs.repr(), &rhs.repr()))]
    #[ensures(|result| spec::add_post(&lhs.repr(), &rhs.repr(), &result.repr()))]
    fn add(lhs: Self, rhs: &Self) -> Self;

    #[requires(spec::sub_pre(&lhs.repr(), &rhs.repr()))]
    #[ensures(|result| spec::sub_post(&lhs.repr(), &rhs.repr(), &result.repr()))]
    fn sub(lhs: Self, rhs: &Self) -> Self;

    #[requires(spec::multiply_by_constant_pre(&vec.repr(), c))]
    #[ensures(|result| spec::multiply_by_constant_post(&vec.repr(), c, &result.repr()))]
    fn multiply_by_constant(vec: Self, c: i16) -> Self;

    // Modular operations
    #[requires(spec::cond_subtract_3329_pre(&v.repr()))]
    #[ensures(|result| spec::cond_subtract_3329_post(&v.repr(), &result.repr()))]
    fn cond_subtract_3329(v: Self) -> Self;

    #[requires(spec::barrett_reduce_pre(&vector.repr()))]
    #[ensures(|result| spec::barrett_reduce_post(&vector.repr(), &result.repr()))]
    fn barrett_reduce(vector: Self) -> Self;

    #[requires(spec::montgomery_multiply_by_constant_pre(&vector.repr(), constant))]
    #[ensures(|result| spec::montgomery_multiply_by_constant_post(&vector.repr(), constant, &result.repr()))]
    fn montgomery_multiply_by_constant(vector: Self, constant: i16) -> Self;

    #[requires(spec::to_unsigned_representative_pre(&a.repr()))]
    #[ensures(|result| spec::to_unsigned_representative_post(&a.repr(), &result.repr()))]
    fn to_unsigned_representative(a: Self) -> Self;

    // Compression
    #[requires(spec::compress_1_pre(&a.repr()))]
    #[ensures(|result| spec::compress_1_post(&a.repr(), &result.repr()))]
    fn compress_1(a: Self) -> Self;

    #[requires(spec::compress_pre(&a.repr(), COEFFICIENT_BITS))]
    #[ensures(|result| spec::compress_post(&a.repr(), COEFFICIENT_BITS, &result.repr()))]
    fn compress<const COEFFICIENT_BITS: i32>(a: Self) -> Self;

    #[requires(spec::decompress_1_pre(&a.repr()))]
    //#[ensures(|result| spec::decompress_1_post(&vector.repr(), &result.repr()))]
    fn decompress_1(a: Self) -> Self;

    #[requires(spec::decompress_ciphertext_coefficient_pre(&a.repr(), COEFFICIENT_BITS))]
    fn decompress_ciphertext_coefficient<const COEFFICIENT_BITS: i32>(a: Self) -> Self;

    // NTT
    #[requires(spec::ntt_layer_1_step_pre(&a.repr(), zeta0, zeta1, zeta2, zeta3))]
    #[ensures(|result| spec::ntt_layer_1_step_post(&a.repr(), zeta0, zeta1, zeta2, zeta3, &result.repr()))]
    fn ntt_layer_1_step(a: Self, zeta0: i16, zeta1: i16, zeta2: i16, zeta3: i16) -> Self;

    #[requires(spec::ntt_layer_2_step_pre(&a.repr(), zeta0, zeta1))]
    #[ensures(|result| spec::ntt_layer_2_step_post(&a.repr(), zeta0, zeta1, &result.repr()))]
    fn ntt_layer_2_step(a: Self, zeta0: i16, zeta1: i16) -> Self;

    #[requires(spec::ntt_layer_3_step_pre(&a.repr(), zeta))]
    #[ensures(|result| spec::ntt_layer_3_step_post(&a.repr(), zeta, &result.repr()))]
    fn ntt_layer_3_step(a: Self, zeta: i16) -> Self;

    #[requires(spec::inv_ntt_layer_1_step_pre(&a.repr(), zeta0, zeta1, zeta2, zeta3))]
    #[ensures(|result| spec::inv_ntt_layer_1_step_post(&a.repr(), zeta0, zeta1, zeta2, zeta3, &result.repr()))]
    fn inv_ntt_layer_1_step(a: Self, zeta0: i16, zeta1: i16, zeta2: i16, zeta3: i16) -> Self;

    #[requires(spec::inv_ntt_layer_2_step_pre(&a.repr(), zeta0, zeta1))]
    #[ensures(|result| spec::inv_ntt_layer_2_step_post(&a.repr(), zeta0, zeta1, &result.repr()))]
    fn inv_ntt_layer_2_step(a: Self, zeta0: i16, zeta1: i16) -> Self;

    #[requires(spec::inv_ntt_layer_3_step_pre(&a.repr(), zeta))]
    #[ensures(|result| spec::inv_ntt_layer_3_step_post(&a.repr(), zeta, &result.repr()))]
    fn inv_ntt_layer_3_step(a: Self, zeta: i16) -> Self;

    #[requires(spec::ntt_multiply_pre(&lhs.repr(), &rhs.repr(), zeta0, zeta1, zeta2, zeta3))]
    #[ensures(|result| spec::ntt_multiply_post(&lhs.repr(), &rhs.repr(), zeta0, zeta1, zeta2, zeta3, &result.repr()))]
    fn ntt_multiply(lhs: &Self, rhs: &Self, zeta0: i16, zeta1: i16, zeta2: i16, zeta3: i16)
        -> Self;

    // Serialization and deserialization
    #[requires(spec::serialize_1_pre(&a.repr()))]
    #[ensures(|result| spec::serialize_1_post(&a.repr(), &result))]
    fn serialize_1(a: Self) -> [u8; 2];

    #[requires(spec::deserialize_1_pre(&a))]
    #[ensures(|result| spec::deserialize_1_post(&a, &result.repr()))]
    fn deserialize_1(a: &[u8]) -> Self;

    #[requires(spec::serialize_4_pre(&a.repr()))]
    #[ensures(|result| spec::serialize_4_post(&a.repr(), &result))]
    fn serialize_4(a: Self) -> [u8; 8];

    #[requires(spec::deserialize_4_pre(&a))]
    #[ensures(|result| spec::deserialize_4_post(&a, &result.repr()))]
    fn deserialize_4(a: &[u8]) -> Self;

    //#[requires(spec::serialize_5_pre(&a.repr()))]
    //#[ensures(|result| spec::serialize_5_post(&a.repr(), &result))]
    fn serialize_5(a: Self) -> [u8; 10];

    #[requires(a.len() == 10)]
    fn deserialize_5(a: &[u8]) -> Self;

    #[requires(spec::serialize_10_pre(&a.repr()))]
    #[ensures(|result| spec::serialize_10_post(&a.repr(), &result))]
    fn serialize_10(a: Self) -> [u8; 20];

    #[requires(spec::deserialize_10_pre(&a))]
    #[ensures(|result| spec::deserialize_10_post(&a, &result.repr()))]
    fn deserialize_10(a: &[u8]) -> Self;

    fn serialize_11(a: Self) -> [u8; 22];
    #[requires(a.len() == 22)]
    fn deserialize_11(a: &[u8]) -> Self;

    #[requires(spec::serialize_12_pre(&a.repr()))]
    #[ensures(|result| spec::serialize_12_post(&a.repr(), &result))]
    fn serialize_12(a: Self) -> [u8; 24];

    #[requires(spec::deserialize_12_pre(&a))]
    #[ensures(|result| spec::deserialize_12_post(&a, &result.repr()))]
    fn deserialize_12(a: &[u8]) -> Self;

    // Rejection sampling
    #[requires(a.len() == 24 && out.len() == 16)]
    #[ensures(|result| (future(out).len() == 16 && result <= 16).to_prop() & (
            hax_lib::forall(|j: usize|
                hax_lib::implies(j < result,
                    future(out)[j] >= 0 && future(out)[j] <= 3328))))]
    fn rej_sample(a: &[u8], out: &mut [i16]) -> usize;
}
