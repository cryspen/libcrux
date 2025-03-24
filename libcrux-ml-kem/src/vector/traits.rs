pub const MONTGOMERY_R_SQUARED_MOD_FIELD_MODULUS: i16 = 1353;
pub const FIELD_MODULUS: i16 = 3329;
pub const FIELD_ELEMENTS_IN_VECTOR: usize = 16;
pub const INVERSE_OF_MODULUS_MOD_MONTGOMERY_R: u32 = 62209; // FIELD_MODULUS^{-1} mod MONTGOMERY_R
pub const BARRETT_SHIFT: i32 = 26;
pub const BARRETT_R: i32 = 1 << BARRETT_SHIFT;

// We define a trait that allows us to talk about the contents of a vector.
// This is used extensively in pre- and post-conditions to reason about the code.
#[hax_lib::attributes]
pub trait Repr: Copy + Clone {
    #[requires(true)]
    fn repr(x: Self) -> [i16; 16];
}

#[cfg(not(eurydice))]
#[hax_lib::attributes]
pub trait Operations: Copy + Clone + Repr {
    #[allow(non_snake_case)]
    #[requires(true)]
    #[ensures(|result| fstar!(r#"f_repr $result == Seq.create 16 (mk_i16 0)"#))]
    fn ZERO() -> Self;

    #[requires(array.len() == 16)]
    #[ensures(|result| fstar!(r#"f_repr $result == $array"#))]
    fn from_i16_array(array: &[i16]) -> Self;

    #[requires(true)]
    #[ensures(|result| fstar!(r#"f_repr $x == $result"#))]
    fn to_i16_array(x: Self) -> [i16; 16];

    #[requires(array.len() >= 32)]
    fn from_bytes(array: &[u8]) -> Self;

    #[requires(bytes.len() >= 32)]
    fn to_bytes(x: Self, bytes: &mut [u8]);

    // Basic arithmetic
    #[requires(fstar!(r#"forall i. i < 16 ==> 
        Spec.Utils.is_intb (pow2 15 - 1) (v (Seq.index (f_repr ${lhs}) i) + v (Seq.index (f_repr ${rhs}) i))"#))]
    #[ensures(|result| fstar!(r#"forall i. i < 16 ==> 
        (v (Seq.index (f_repr ${result}) i) == 
         v (Seq.index (f_repr ${lhs}) i) + v (Seq.index (f_repr ${rhs}) i))"#))]
    fn add(lhs: Self, rhs: &Self) -> Self;

    #[requires(fstar!(r#"forall i. i < 16 ==> 
        Spec.Utils.is_intb (pow2 15 - 1) (v (Seq.index (f_repr ${lhs}) i) - v (Seq.index (f_repr ${rhs}) i))"#))]
    #[ensures(|result| fstar!(r#"forall i. i < 16 ==> 
        (v (Seq.index (f_repr ${result}) i) == 
         v (Seq.index (f_repr ${lhs}) i) - v (Seq.index (f_repr ${rhs}) i))"#))]
    fn sub(lhs: Self, rhs: &Self) -> Self;

    #[requires(fstar!(r#"forall i. i < 16 ==> 
        Spec.Utils.is_intb (pow2 15 - 1) (v (Seq.index (f_repr ${vec}) i) * v c)"#))]
    #[ensures(|result| fstar!(r#"forall i. i < 16 ==> 
        (v (Seq.index (f_repr ${result}) i) == 
         v (Seq.index (f_repr ${vec}) i) * v c)"#))]
    fn multiply_by_constant(vec: Self, c: i16) -> Self;

    // Bitwise operations
    #[requires(true)]
    #[ensures(|result| fstar!(r#"f_repr $result == Spec.Utils.map_array (fun x -> x &. c) (f_repr $v)"#))]
    fn bitwise_and_with_constant(v: Self, c: i16) -> Self;

    #[requires(SHIFT_BY >= 0 && SHIFT_BY < 16)]
    #[ensures(|result| fstar!(r#"(v_SHIFT_BY >=. (mk_i32 0) /\ v_SHIFT_BY <. (mk_i32 16)) ==> f_repr $result == Spec.Utils.map_array (fun x -> x >>! ${SHIFT_BY}) (f_repr $v)"#))]
    fn shift_right<const SHIFT_BY: i32>(v: Self) -> Self;
    // fn shift_left<const SHIFT_BY: i32>(v: Self) -> Self;

    // Modular operations
    #[requires(fstar!(r#"Spec.Utils.is_i16b_array (pow2 12 - 1) (f_repr $v)"#))]
    #[ensures(|result| fstar!(r#"f_repr $result == Spec.Utils.map_array (fun x -> if x >=. (mk_i16 3329) then x -! (mk_i16 3329) else x) (f_repr $v)"#))]
    fn cond_subtract_3329(v: Self) -> Self;

    #[requires(fstar!(r#"Spec.Utils.is_i16b_array 28296 (f_repr $vector)"#))]
    fn barrett_reduce(vector: Self) -> Self;

    #[requires(fstar!(r#"Spec.Utils.is_i16b 1664 c"#))]
    fn montgomery_multiply_by_constant(v: Self, c: i16) -> Self;

    #[requires(fstar!(r#"Spec.Utils.is_i16b_array 3328 (f_repr a)"#))]
    #[ensures(|result| fstar!(r#"forall (i:nat). i < 16 ==>
                                (let x = Seq.index (f_repr ${a}) i in
                                 let y = Seq.index (f_repr ${result}) i in
                                 (v y >= 0 /\ v y <= 3328 /\ (v y % 3329 == v x % 3329)))"#))]
    fn to_unsigned_representative(a: Self) -> Self;

    // Compression
    #[requires(fstar!(r#"forall (i:nat). i < 16 ==> v (Seq.index (f_repr $a) i) >= 0 /\
        v (Seq.index (f_repr $a) i) < 3329"#))]
    #[ensures(|result| fstar!(r#"forall (i:nat). i < 16 ==> bounded (Seq.index (f_repr $result) i) 1"#))]
    fn compress_1(a: Self) -> Self;
    #[requires(fstar!(r#"(v $COEFFICIENT_BITS == 4 \/
            v $COEFFICIENT_BITS == 5 \/
            v $COEFFICIENT_BITS == 10 \/
            v $COEFFICIENT_BITS == 11) /\
        (forall (i:nat). i < 16 ==> v (Seq.index (f_repr $a) i) >= 0 /\
            v (Seq.index (f_repr $a) i) < 3329)"#))]
    #[ensures(|result| fstar!(r#"(v $COEFFICIENT_BITS == 4 \/
            v $COEFFICIENT_BITS == 5 \/
            v $COEFFICIENT_BITS == 10 \/
            v $COEFFICIENT_BITS == 11) ==>
                (forall (i:nat). i < 16 ==> bounded (Seq.index (f_repr $result) i) (v $COEFFICIENT_BITS))"#))]
    fn compress<const COEFFICIENT_BITS: i32>(a: Self) -> Self;

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
    fn decompress_ciphertext_coefficient<const COEFFICIENT_BITS: i32>(a: Self) -> Self;

    // NTT
    #[requires(fstar!(r#"Spec.Utils.is_i16b 1664 zeta0 /\ Spec.Utils.is_i16b 1664 zeta1 /\ 
                       Spec.Utils.is_i16b 1664 zeta2 /\ Spec.Utils.is_i16b 1664 zeta3 /\
                       Spec.Utils.is_i16b_array (11207+5*3328) (f_repr ${a})"#))]
    #[ensures(|out| fstar!(r#"Spec.Utils.is_i16b_array (11207+6*3328) (f_repr $out)"#))]
    fn ntt_layer_1_step(a: Self, zeta0: i16, zeta1: i16, zeta2: i16, zeta3: i16) -> Self;
    #[requires(fstar!(r#"Spec.Utils.is_i16b 1664 zeta0 /\ Spec.Utils.is_i16b 1664 zeta1 /\
                       Spec.Utils.is_i16b_array (11207+4*3328) (f_repr ${a})"#))]
    #[ensures(|out| fstar!(r#"Spec.Utils.is_i16b_array (11207+5*3328) (f_repr $out)"#))]
    fn ntt_layer_2_step(a: Self, zeta0: i16, zeta1: i16) -> Self;
    #[requires(fstar!(r#"Spec.Utils.is_i16b 1664 zeta /\
                       Spec.Utils.is_i16b_array (11207+3*3328) (f_repr ${a})"#))]
    #[ensures(|out| fstar!(r#"Spec.Utils.is_i16b_array (11207+4*3328) (f_repr $out)"#))]
    fn ntt_layer_3_step(a: Self, zeta: i16) -> Self;

    #[requires(fstar!(r#"Spec.Utils.is_i16b 1664 zeta0 /\ Spec.Utils.is_i16b 1664 zeta1 /\ 
                       Spec.Utils.is_i16b 1664 zeta2 /\ Spec.Utils.is_i16b 1664 zeta3 /\
                       Spec.Utils.is_i16b_array (4 * 3328) (f_repr ${a})"#))]
    #[ensures(|out| fstar!(r#"Spec.Utils.is_i16b_array 3328 (f_repr $out)"#))]
    fn inv_ntt_layer_1_step(a: Self, zeta0: i16, zeta1: i16, zeta2: i16, zeta3: i16) -> Self;
    #[requires(fstar!(r#"Spec.Utils.is_i16b 1664 zeta0 /\ Spec.Utils.is_i16b 1664 zeta1 /\
                       Spec.Utils.is_i16b_array 3328 (f_repr ${a})"#))]
    #[ensures(|out| fstar!(r#"Spec.Utils.is_i16b_array 3328 (f_repr $out)"#))]
    fn inv_ntt_layer_2_step(a: Self, zeta0: i16, zeta1: i16) -> Self;
    #[requires(fstar!(r#"Spec.Utils.is_i16b 1664 zeta/\
                       Spec.Utils.is_i16b_array 3328 (f_repr ${a})"#))]
    #[ensures(|out| fstar!(r#"Spec.Utils.is_i16b_array 3328 (f_repr $out)"#))]
    fn inv_ntt_layer_3_step(a: Self, zeta: i16) -> Self;

    #[requires(fstar!(r#"Spec.Utils.is_i16b 1664 zeta0 /\ Spec.Utils.is_i16b 1664 zeta1 /\
                       Spec.Utils.is_i16b 1664 zeta2 /\ Spec.Utils.is_i16b 1664 zeta3 /\
                       Spec.Utils.is_i16b_array 3328 (f_repr ${lhs}) /\
                       Spec.Utils.is_i16b_array 3328 (f_repr ${rhs}) "#))]
    #[ensures(|out| fstar!(r#"Spec.Utils.is_i16b_array 3328 (f_repr $out)"#))]
    fn ntt_multiply(lhs: &Self, rhs: &Self, zeta0: i16, zeta1: i16, zeta2: i16, zeta3: i16)
        -> Self;

    // Serialization and deserialization
    #[requires(fstar!(r#"Spec.MLKEM.serialize_pre 1 (f_repr $a)"#))]
    #[ensures(|result| fstar!(r#"Spec.MLKEM.serialize_pre 1 (f_repr $a) ==> Spec.MLKEM.serialize_post 1 (f_repr $a) $result"#))]
    fn serialize_1(a: Self) -> [u8; 2];
    #[requires(a.len() == 2)]
    #[ensures(|result| fstar!(r#"sz (Seq.length $a) =. sz 2 ==> Spec.MLKEM.deserialize_post 1 $a (f_repr $result)"#))]
    fn deserialize_1(a: &[u8]) -> Self;

    #[requires(fstar!(r#"Spec.MLKEM.serialize_pre 4 (f_repr $a)"#))]
    #[ensures(|result| fstar!(r#"Spec.MLKEM.serialize_pre 4 (f_repr $a) ==> Spec.MLKEM.serialize_post 4 (f_repr $a) $result"#))]
    fn serialize_4(a: Self) -> [u8; 8];
    #[requires(a.len() == 8)]
    #[ensures(|result| fstar!(r#"sz (Seq.length $a) =. sz 8 ==> Spec.MLKEM.deserialize_post 4 $a (f_repr $result)"#))]
    fn deserialize_4(a: &[u8]) -> Self;

    fn serialize_5(a: Self) -> [u8; 10];
    #[requires(a.len() == 10)]
    fn deserialize_5(a: &[u8]) -> Self;

    #[requires(fstar!(r#"Spec.MLKEM.serialize_pre 10 (f_repr $a)"#))]
    #[ensures(|result| fstar!(r#"Spec.MLKEM.serialize_pre 10 (f_repr $a) ==> Spec.MLKEM.serialize_post 10 (f_repr $a) $result"#))]
    fn serialize_10(a: Self) -> [u8; 20];
    #[requires(a.len() == 20)]
    #[ensures(|result| fstar!(r#"sz (Seq.length $a) =. sz 20 ==> Spec.MLKEM.deserialize_post 10 $a (f_repr $result)"#))]
    fn deserialize_10(a: &[u8]) -> Self;

    fn serialize_11(a: Self) -> [u8; 22];
    #[requires(a.len() == 22)]
    fn deserialize_11(a: &[u8]) -> Self;

    #[requires(fstar!(r#"Spec.MLKEM.serialize_pre 12 (f_repr $a)"#))]
    #[ensures(|result| fstar!(r#"Spec.MLKEM.serialize_pre 12 (f_repr $a) ==> Spec.MLKEM.serialize_post 12 (f_repr $a) $result"#))]
    fn serialize_12(a: Self) -> [u8; 24];
    #[requires(a.len() == 24)]
    #[ensures(|result| fstar!(r#"sz (Seq.length $a) =. sz 24 ==> Spec.MLKEM.deserialize_post 12 $a (f_repr $result)"#))]
    fn deserialize_12(a: &[u8]) -> Self;

    #[requires(a.len() == 24 && out.len() == 16)]
    #[ensures(|result|
        fstar!(r#"Seq.length $out_future == Seq.length $out /\ v $result <= 16"#)
    )]
    fn rej_sample(a: &[u8], out: &mut [i16]) -> usize;
}

// The trait is duplicated for Eurudice to avoid the trait inheritance between Operations and Repr
// This is needed because of this issue: https://github.com/AeneasVerif/eurydice/issues/111
#[cfg(eurydice)]
pub trait Operations: Copy + Clone {
    #[allow(non_snake_case)]
    fn ZERO() -> Self;
    fn from_i16_array(array: &[i16]) -> Self;
    fn to_i16_array(x: Self) -> [i16; 16];
    fn from_bytes(array: &[u8]) -> Self;
    fn to_bytes(x: Self, bytes: &mut [u8]);
    fn add(lhs: Self, rhs: &Self) -> Self;
    fn sub(lhs: Self, rhs: &Self) -> Self;
    fn multiply_by_constant(v: Self, c: i16) -> Self;
    fn bitwise_and_with_constant(v: Self, c: i16) -> Self;
    fn shift_right<const SHIFT_BY: i32>(v: Self) -> Self;
    fn cond_subtract_3329(v: Self) -> Self;
    fn barrett_reduce(vector: Self) -> Self;
    fn montgomery_multiply_by_constant(v: Self, c: i16) -> Self;
    fn to_unsigned_representative(a: Self) -> Self;
    fn compress_1(v: Self) -> Self;
    fn compress<const COEFFICIENT_BITS: i32>(v: Self) -> Self;
    fn decompress_1(a: Self) -> Self;
    fn decompress_ciphertext_coefficient<const COEFFICIENT_BITS: i32>(a: Self) -> Self;
    fn ntt_layer_1_step(a: Self, zeta0: i16, zeta1: i16, zeta2: i16, zeta3: i16) -> Self;
    fn ntt_layer_2_step(a: Self, zeta0: i16, zeta1: i16) -> Self;
    fn ntt_layer_3_step(a: Self, zeta: i16) -> Self;
    fn inv_ntt_layer_1_step(a: Self, zeta0: i16, zeta1: i16, zeta2: i16, zeta3: i16) -> Self;
    fn inv_ntt_layer_2_step(a: Self, zeta0: i16, zeta1: i16) -> Self;
    fn inv_ntt_layer_3_step(a: Self, zeta: i16) -> Self;
    fn ntt_multiply(lhs: &Self, rhs: &Self, zeta0: i16, zeta1: i16, zeta2: i16, zeta3: i16)
        -> Self;
    fn serialize_1(a: Self) -> [u8; 2];
    fn deserialize_1(a: &[u8]) -> Self;
    fn serialize_4(a: Self) -> [u8; 8];
    fn deserialize_4(a: &[u8]) -> Self;
    fn serialize_5(a: Self) -> [u8; 10];
    fn deserialize_5(a: &[u8]) -> Self;
    fn serialize_10(a: Self) -> [u8; 20];
    fn deserialize_10(a: &[u8]) -> Self;
    fn serialize_11(a: Self) -> [u8; 22];
    fn deserialize_11(a: &[u8]) -> Self;
    fn serialize_12(a: Self) -> [u8; 24];
    fn deserialize_12(a: &[u8]) -> Self;
    fn rej_sample(a: &[u8], out: &mut [i16]) -> usize;
}
