pub const MONTGOMERY_R_SQUARED_MOD_FIELD_MODULUS: i16 = 1353;
pub const FIELD_MODULUS: i16 = 3329;
pub const FIELD_ELEMENTS_IN_VECTOR: usize = 16;
pub const INVERSE_OF_MODULUS_MOD_MONTGOMERY_R: u32 = 62209; // FIELD_MODULUS^{-1} mod MONTGOMERY_R
pub const BARRETT_SHIFT: i32 = 26;
pub const BARRETT_R: i32 = 1 << BARRETT_SHIFT;

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
mod spec {
    pub(crate) fn add_pre(lhs: &[i16; 16], rhs: &[i16; 16]) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#"forall i. i < 16 ==> 
            Spec.Utils.is_intb (pow2 15 - 1) 
                (v (Seq.index ${lhs} i) + v (Seq.index ${rhs} i))"#
        )
    }

    pub(crate) fn add_post(lhs: &[i16; 16], rhs: &[i16; 16], result: &[i16; 16]) -> hax_lib::Prop {
        hax_lib::fstar_prop_expr!(
            r#"forall i. i < 16 ==> 
            (v (Seq.index ${result} i) == 
            v (Seq.index ${lhs} i) + v (Seq.index ${rhs} i))"#
        )
    }
}

#[hax_lib::attributes]
pub trait Operations: Copy + Clone + Repr {
    #[allow(non_snake_case)]
    #[requires(true)]
    #[ensures(|result| fstar!(r#"f_repr $result == Seq.create 16 (mk_i16 0)"#))]
    fn ZERO() -> Self;

    #[requires(array.len() == 16)]
    #[ensures(|_| fstar!(r#"f_repr ${out}_future == $array"#))]
    fn from_i16_array(array: &[i16], out: &mut Self);

    #[requires(true)]
    #[ensures(|_| fstar!(r#"f_repr $x == ${out}_future"#))]
    fn to_i16_array(x: &Self, out: &mut [i16]);

    #[requires(array.len() >= 32)]
    fn from_bytes(array: &[u8], out: &mut Self);

    #[requires(bytes.len() >= 32)]
    #[ensures(|_| future(bytes).len() == bytes.len())]
    fn to_bytes(x: Self, bytes: &mut [u8]);

    // Basic arithmetic
    #[requires(spec::add_pre(&lhs.repr(), &rhs.repr()))]
    #[ensures(|_| spec::add_post(&lhs.repr(), &rhs.repr(), &future(lhs).repr()))]
    fn add(lhs: &mut Self, rhs: &Self);

    #[requires(fstar!(r#"forall i. i < 16 ==> 
        Spec.Utils.is_intb (pow2 15 - 1) (v (Seq.index (f_repr ${lhs}) i) - v (Seq.index (f_repr ${rhs}) i))"#))]
    #[ensures(|_| fstar!(r#"forall i. i < 16 ==> 
        (v (Seq.index (f_repr ${lhs}_future) i) == 
         v (Seq.index (f_repr ${lhs}) i) - v (Seq.index (f_repr ${rhs}) i))"#))]
    fn sub(lhs: &mut Self, rhs: &Self);

    fn negate(vec: &mut Self);

    #[requires(fstar!(r#"forall i. i < 16 ==> 
        Spec.Utils.is_intb (pow2 15 - 1) (v (Seq.index (f_repr ${vec}) i) * v $c)"#))]
    #[ensures(|_| fstar!(r#"forall i. i < 16 ==> 
        (v (Seq.index (f_repr ${vec}_future) i) == 
         v (Seq.index (f_repr ${vec}) i) * v $c)"#))]
    fn multiply_by_constant(vec: &mut Self, c: i16);

    // Bitwise operations
    #[requires(true)]
    #[ensures(|_| fstar!(r#"f_repr vec_future == Spec.Utils.map_array (fun x -> x &. $c) (f_repr $vec)"#))]
    fn bitwise_and_with_constant(vec: &mut Self, c: i16);

    #[requires(SHIFT_BY >= 0 && SHIFT_BY < 16)]
    #[ensures(|_| fstar!(r#"(v_SHIFT_BY >=. (mk_i32 0) /\ v_SHIFT_BY <. (mk_i32 16)) ==> f_repr vec_future == Spec.Utils.map_array (fun x -> x >>! ${SHIFT_BY}) (f_repr $vec)"#))]
    fn shift_right<const SHIFT_BY: i32>(vec: &mut Self);

    // Modular operations
    #[requires(fstar!(r#"Spec.Utils.is_i16b_array (pow2 12 - 1) (f_repr $vec)"#))]
    #[ensures(|_| fstar!(r#"f_repr vec_future == Spec.Utils.map_array (fun x -> if x >=. (mk_i16 3329) then x -! (mk_i16 3329) else x) (f_repr $vec)"#))]
    fn cond_subtract_3329(vec: &mut Self);

    #[requires(fstar!(r#"Spec.Utils.is_i16b_array 28296 (f_repr $vector)"#))]
    #[ensures(|_| fstar!(r#"Spec.Utils.is_i16b_array 3328 (f_repr ${vector}_future) /\
                (forall i. (v (Seq.index (f_repr ${vector}_future) i) % 3329) == 
                           (v (Seq.index (f_repr ${vector})i) % 3329))"#))]
    fn barrett_reduce(vector: &mut Self);

    #[requires(fstar!(r#"Spec.Utils.is_i16b 1664 c"#))]
    #[ensures(|_| fstar!(r#"Spec.Utils.is_i16b_array 3328 (f_repr vec_future) /\
                (forall i. i < 16 ==> ((v (Seq.index (f_repr vec_future) i) % 3329)==
                                       (v (Seq.index (f_repr ${vec}) i) * v ${c} * 169) % 3329))"#))]

    fn montgomery_multiply_by_constant(vec: &mut Self, c: i16);

    #[requires(fstar!(r#"Spec.Utils.is_i16b_array 3328 (f_repr a)"#))]
    #[ensures(|result| fstar!(r#"forall (i:nat). i < 16 ==>
                                (let x = Seq.index (f_repr ${a}) i in
                                 let y = Seq.index (f_repr result) i in
                                 (v y >= 0 /\ v y <= 3328 /\ (v y % 3329 == v x % 3329)))"#))]
    fn to_unsigned_representative(a: Self) -> Self;

    // Compression
    #[requires(fstar!(r#"forall (i:nat). i < 16 ==> v (Seq.index (f_repr $a) i) >= 0 /\
        v (Seq.index (f_repr $a) i) < 3329"#))]
    #[ensures(|_| fstar!(r#"forall (i:nat). i < 16 ==> bounded (Seq.index (f_repr ${a}_future) i) 1"#))]
    fn compress_1(a: &mut Self);
    #[requires(fstar!(r#"(v $COEFFICIENT_BITS == 4 \/
            v $COEFFICIENT_BITS == 5 \/
            v $COEFFICIENT_BITS == 10 \/
            v $COEFFICIENT_BITS == 11) /\
        (forall (i:nat). i < 16 ==> v (Seq.index (f_repr $a) i) >= 0 /\
            v (Seq.index (f_repr $a) i) < 3329)"#))]
    #[ensures(|_| fstar!(r#"(v $COEFFICIENT_BITS == 4 \/
            v $COEFFICIENT_BITS == 5 \/
            v $COEFFICIENT_BITS == 10 \/
            v $COEFFICIENT_BITS == 11) ==>
                (forall (i:nat). i < 16 ==> bounded (Seq.index (f_repr ${a}_future) i) (v $COEFFICIENT_BITS))"#))]
    fn compress<const COEFFICIENT_BITS: i32>(a: &mut Self);

    #[hax_lib::requires(fstar!(r#"forall (i:nat). i < 16 ==>
                                    (let x = Seq.index (f_repr ${a}) i in 
                                     (x == mk_i16 0 \/ x == mk_i16 1))"#))]
    fn decompress_1(a: Self) -> Self;

    #[requires(fstar!(r#"(v $COEFFICIENT_BITS == 4 \/
        v $COEFFICIENT_BITS == 5 \/
        v $COEFFICIENT_BITS == 10 \/
        v $COEFFICIENT_BITS == 11) /\
    (forall (i:nat). i < 16 ==> v (Seq.index (f_repr $a) i) >= 0 /\
        v (Seq.index (f_repr $a) i) < pow2 (v $COEFFICIENT_BITS))"#))]
    fn decompress_ciphertext_coefficient<const COEFFICIENT_BITS: i32>(a: &mut Self);

    // NTT
    #[requires(fstar!(r#"Spec.Utils.is_i16b 1664 zeta0 /\ Spec.Utils.is_i16b 1664 zeta1 /\ 
                       Spec.Utils.is_i16b 1664 zeta2 /\ Spec.Utils.is_i16b 1664 zeta3 /\
                       Spec.Utils.is_i16b_array (11207+5*3328) (f_repr ${a})"#))]
    #[ensures(|_| fstar!(r#"Spec.Utils.is_i16b_array (11207+6*3328) (f_repr ${a}_future)"#))]
    fn ntt_layer_1_step(a: &mut Self, zeta0: i16, zeta1: i16, zeta2: i16, zeta3: i16);
    #[requires(fstar!(r#"Spec.Utils.is_i16b 1664 zeta0 /\ Spec.Utils.is_i16b 1664 zeta1 /\
                       Spec.Utils.is_i16b_array (11207+4*3328) (f_repr ${a})"#))]
    #[ensures(|_| fstar!(r#"Spec.Utils.is_i16b_array (11207+5*3328) (f_repr ${a}_future)"#))]
    fn ntt_layer_2_step(a: &mut Self, zeta0: i16, zeta1: i16);
    #[requires(fstar!(r#"Spec.Utils.is_i16b 1664 zeta /\
                       Spec.Utils.is_i16b_array (11207+3*3328) (f_repr ${a})"#))]
    #[ensures(|_| fstar!(r#"Spec.Utils.is_i16b_array (11207+4*3328) (f_repr ${a}_future)"#))]
    fn ntt_layer_3_step(a: &mut Self, zeta: i16);

    #[requires(fstar!(r#"Spec.Utils.is_i16b 1664 zeta0 /\ Spec.Utils.is_i16b 1664 zeta1 /\ 
                       Spec.Utils.is_i16b 1664 zeta2 /\ Spec.Utils.is_i16b 1664 zeta3 /\
                       Spec.Utils.is_i16b_array (4 * 3328) (f_repr ${a})"#))]
    #[ensures(|_| fstar!(r#"Spec.Utils.is_i16b_array 3328 (f_repr ${a}_future)"#))]
    fn inv_ntt_layer_1_step(a: &mut Self, zeta0: i16, zeta1: i16, zeta2: i16, zeta3: i16);
    #[requires(fstar!(r#"Spec.Utils.is_i16b 1664 zeta0 /\ Spec.Utils.is_i16b 1664 zeta1 /\
                       Spec.Utils.is_i16b_array 3328 (f_repr ${a})"#))]
    #[ensures(|_| fstar!(r#"Spec.Utils.is_i16b_array 3328 (f_repr ${a}_future)"#))]
    fn inv_ntt_layer_2_step(a: &mut Self, zeta0: i16, zeta1: i16);
    #[requires(fstar!(r#"Spec.Utils.is_i16b 1664 zeta/\
                       Spec.Utils.is_i16b_array 3328 (f_repr ${a})"#))]
    #[ensures(|_| fstar!(r#"Spec.Utils.is_i16b_array 3328 (f_repr ${a}_future)"#))]
    fn inv_ntt_layer_3_step(a: &mut Self, zeta: i16);

    #[requires(fstar!(r#"Spec.Utils.is_i16b 1664 zeta0 /\ Spec.Utils.is_i16b 1664 zeta1 /\
                       Spec.Utils.is_i16b 1664 zeta2 /\ Spec.Utils.is_i16b 1664 zeta3 /\
                       Spec.Utils.is_i16b_array 3328 (f_repr ${lhs}) /\
                       Spec.Utils.is_i16b_array 3328 (f_repr ${rhs}) "#))]
    #[ensures(|_| fstar!(r#"Spec.Utils.is_i16b_array 3328 (f_repr ${out}_future)"#))]
    fn ntt_multiply(
        lhs: &Self,
        rhs: &Self,
        out: &mut Self,
        zeta0: i16,
        zeta1: i16,
        zeta2: i16,
        zeta3: i16,
    );

    // Serialization and deserialization
    #[requires(fstar!(r#"Spec.MLKEM.serialize_pre 1 (f_repr $a) /\ Seq.length $out == 2"#))]
    #[ensures(|_| fstar!(r#"(Spec.MLKEM.serialize_pre 1 (f_repr $a) ==> Spec.MLKEM.serialize_post 1 (f_repr $a) ${out}_future)
                        /\ Seq.length ${out}_future == Seq.length $out"#))]
    fn serialize_1(a: &Self, out: &mut [u8]);

    #[requires(a.len() == 2)]
    #[ensures(|_| fstar!(r#"sz (Seq.length $a) =. sz 2 ==> Spec.MLKEM.deserialize_post 1 $a (f_repr ${out}_future)"#))]
    fn deserialize_1(a: &[u8], out: &mut Self);

    #[requires(fstar!(r#"Spec.MLKEM.serialize_pre 4 (f_repr $a) /\ Seq.length $out == 8"#))]
    #[ensures(|_| fstar!(r#"(Spec.MLKEM.serialize_pre 4 (f_repr $a) ==> Spec.MLKEM.serialize_post 4 (f_repr $a) ${out}_future)
                         /\ Seq.length ${out}_future == Seq.length $out"#))]
    fn serialize_4(a: &Self, out: &mut [u8]);

    #[requires(a.len() == 8)]
    #[ensures(|_| fstar!(r#"sz (Seq.length $a) =. sz 8 ==> Spec.MLKEM.deserialize_post 4 $a (f_repr ${out}_future)"#))]
    fn deserialize_4(a: &[u8], out: &mut Self);

    fn serialize_5(a: &Self, out: &mut [u8]);

    #[requires(a.len() == 10)]
    fn deserialize_5(a: &[u8], out: &mut Self);

    #[requires(fstar!(r#"Spec.MLKEM.serialize_pre 10 (f_repr $a) /\ Seq.length $out == 20"#))]
    #[ensures(|_| fstar!(r#"(Spec.MLKEM.serialize_pre 10 (f_repr $a) ==> Spec.MLKEM.serialize_post 10 (f_repr $a) ${out}_future)
                         /\ Seq.length ${out}_future == Seq.length $out"#))]
    fn serialize_10(a: &Self, out: &mut [u8]);

    #[requires(a.len() == 20)]
    #[ensures(|_| fstar!(r#"sz (Seq.length $a) =. sz 20 ==> Spec.MLKEM.deserialize_post 10 $a (f_repr ${out}_future)"#))]
    fn deserialize_10(a: &[u8], out: &mut Self);

    fn serialize_11(a: &Self, out: &mut [u8]);

    #[requires(a.len() == 22)]
    fn deserialize_11(a: &[u8], out: &mut Self);

    #[requires(fstar!(r#"Spec.MLKEM.serialize_pre 12 (f_repr $a) /\ Seq.length $out == 24"#))]
    #[ensures(|_| fstar!(r#"(Spec.MLKEM.serialize_pre 12 (f_repr $a) ==> Spec.MLKEM.serialize_post 12 (f_repr $a) ${out}_future)
                         /\ Seq.length ${out}_future == Seq.length $out"#))]
    fn serialize_12(a: &Self, out: &mut [u8]);

    #[requires(a.len() == 24)]
    #[ensures(|_| fstar!(r#"sz (Seq.length $a) =. sz 24 ==> Spec.MLKEM.deserialize_post 12 $a (f_repr ${out}_future)"#))]
    fn deserialize_12(a: &[u8], out: &mut Self);

    #[requires(a.len() == 24 && out.len() == 16)]
    #[ensures(|result|
        fstar!(r#"Seq.length $out_future == Seq.length $out /\ v $result <= 16"#)
    )]
    fn rej_sample(a: &[u8], out: &mut [i16]) -> usize;
}

// hax does not support trait with default implementations, so we use the following pattern
#[hax_lib::requires(fstar!(r#"Spec.Utils.is_i16b 1664 $fer"#))]
#[inline(always)]
pub fn montgomery_multiply_fe<T: Operations>(v: &mut T, fer: i16) {
    T::montgomery_multiply_by_constant(v, fer)
}

#[hax_lib::fstar::options("--z3rlimit 200 --split_queries always")]
#[hax_lib::requires(fstar!(r#"forall i. let x = Seq.index (i0._super_16084754032855797384.f_repr ${vec}) i in
                                      (x == mk_i16 0 \/ x == mk_i16 1)"#))]
#[inline(always)]
pub fn decompress_1<T: Operations>(vec: &mut T) {
    hax_lib::fstar!(
        r#"assert(forall i. let x = Seq.index (i0._super_16084754032855797384.f_repr ${vec}) i in
                                      ((0 - v x) == 0 \/ (0 - v x) == -1))"#
    );
    hax_lib::fstar!(
        r#"assert(forall i. i < 16 ==>
                                      Spec.Utils.is_intb (pow2 15 - 1)
                                        (0 - v (Seq.index (i0._super_16084754032855797384.f_repr ${vec}) i)))"#
    );

    T::negate(vec);
    hax_lib::fstar!(
        r#"assert(forall i. Seq.index (i0._super_16084754032855797384.f_repr ${vec}) i == mk_i16 0 \/
                                      Seq.index (i0._super_16084754032855797384.f_repr ${vec}) i == mk_i16 (-1))"#
    );
    hax_lib::fstar!(r#"assert (i0.f_bitwise_and_with_constant_pre ${vec} (mk_i16 1665))"#);
    T::bitwise_and_with_constant(vec, 1665);
}
