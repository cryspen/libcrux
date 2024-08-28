pub const MONTGOMERY_R_SQUARED_MOD_FIELD_MODULUS: i16 = 1353;
pub const FIELD_MODULUS: i16 = 3329;
pub const FIELD_ELEMENTS_IN_VECTOR: usize = 16;
pub const INVERSE_OF_MODULUS_MOD_MONTGOMERY_R: u32 = 62209; // FIELD_MODULUS^{-1} mod MONTGOMERY_R
pub const BARRETT_SHIFT: i32 = 26;
pub const BARRETT_R: i32 = 1 << BARRETT_SHIFT;

#[hax_lib::attributes]
pub trait Repr: Copy + Clone {
    #[requires(true)]
    fn repr(x: Self) -> [i16; 16];
}


#[hax_lib::attributes]
pub trait Operations: Copy + Clone + Repr {
    #[requires(true)]
    #[ensures(|result| fstar!("f_repr $x == $result"))]
    fn to_i16_array(x: Self) -> [i16; 16];

    #[requires(array.len() == 16)]
    #[ensures(|result| fstar!("f_repr $result == $array"))]
    fn from_i16_array(array: &[i16]) -> Self;
   
    #[allow(non_snake_case)]
    #[requires(true)]
    #[ensures(|result| fstar!("f_repr $result == Seq.create 16 0s"))]
    fn ZERO() -> Self;

    // Basic arithmetic
    #[requires(true)]
    #[ensures(|result| fstar!("f_repr $result == Spec.Utils.map2 (+.) (f_repr $lhs) (f_repr $rhs)"))]
    fn add(lhs: Self, rhs: &Self) -> Self;

    #[requires(true)]
    #[ensures(|result| fstar!("f_repr $result == Spec.Utils.map2 (-.) (f_repr $lhs) (f_repr $rhs)"))]
    fn sub(lhs: Self, rhs: &Self) -> Self;

    #[requires(true)]
    #[ensures(|result| fstar!("f_repr $result == Spec.Utils.map_array (fun x -> x *. c) (f_repr $v)"))]
    fn multiply_by_constant(v: Self, c: i16) -> Self;

    // Bitwise operations
    #[requires(true)]
    #[ensures(|result| fstar!("f_repr $result == Spec.Utils.map_array (fun x -> x &. c) (f_repr $v)"))]
    fn bitwise_and_with_constant(v: Self, c: i16) -> Self;

    #[requires(SHIFT_BY >= 0 && SHIFT_BY < 16)]
    #[ensures(|result| fstar!("(v_SHIFT_BY >=. 0l /\\ v_SHIFT_BY <. 16l) ==> f_repr $result == Spec.Utils.map_array (fun x -> x >>! ${SHIFT_BY}) (f_repr $v)"))]
    fn shift_right<const SHIFT_BY: i32>(v: Self) -> Self;
    // fn shift_left<const SHIFT_BY: i32>(v: Self) -> Self;

    // Modular operations
    #[requires(true)]
    #[ensures(|result| fstar!("f_repr $result == Spec.Utils.map_array (fun x -> if x >=. 3329s then x -! 3329s else x) (f_repr $v)"))]
    fn cond_subtract_3329(v: Self) -> Self;

    #[requires(true)]
    fn barrett_reduce(vector: Self) -> Self;

    #[requires(true)]
    fn montgomery_multiply_by_constant(v: Self, c: i16) -> Self;

    // Compression
    #[requires(true)]
    fn compress_1(v: Self) -> Self;
    #[requires(COEFFICIENT_BITS == 4 || COEFFICIENT_BITS == 5 ||
               COEFFICIENT_BITS == 10 || COEFFICIENT_BITS == 11)]
    fn compress<const COEFFICIENT_BITS: i32>(v: Self) -> Self;
    #[requires(COEFFICIENT_BITS == 4 || COEFFICIENT_BITS == 5 ||
        COEFFICIENT_BITS == 10 || COEFFICIENT_BITS == 11)]
    fn decompress_ciphertext_coefficient<const COEFFICIENT_BITS: i32>(v: Self) -> Self;

    // NTT
    #[requires(true)]
    #[hax_lib::ensures(|result|
        fstar!("f_repr $result == Spec.MLKEM.poly_ntt_layer_1_step
            (f_repr $a) $zeta0 $zeta1 $zeta2 $zeta3")
    )]
    fn ntt_layer_1_step(a: Self, zeta0: i16, zeta1: i16, zeta2: i16, zeta3: i16) -> Self;
    #[requires(true)]
    #[hax_lib::ensures(|result|
        fstar!("f_repr $result == Spec.MLKEM.poly_ntt_layer_2_step
            (f_repr $a) $zeta0 $zeta1")
    )]
    fn ntt_layer_2_step(a: Self, zeta0: i16, zeta1: i16) -> Self;
    #[requires(true)]
    #[hax_lib::ensures(|result|
        fstar!("f_repr $result == Spec.MLKEM.poly_ntt_layer_3_step
            (f_repr $a) $zeta")
    )]
    fn ntt_layer_3_step(a: Self, zeta: i16) -> Self;

    #[requires(true)]
    fn inv_ntt_layer_1_step(a: Self, zeta0: i16, zeta1: i16, zeta2: i16, zeta3: i16) -> Self;
    #[requires(true)]
    fn inv_ntt_layer_2_step(a: Self, zeta0: i16, zeta1: i16) -> Self;
    #[requires(true)]
    fn inv_ntt_layer_3_step(a: Self, zeta: i16) -> Self;

    #[requires(true)]
    fn ntt_multiply(lhs: &Self, rhs: &Self, zeta0: i16, zeta1: i16, zeta2: i16, zeta3: i16)
        -> Self;

    // Serialization and deserialization
    #[requires(true)]
    fn serialize_1(a: Self) -> [u8; 2];
    #[requires(true)]
    fn deserialize_1(a: &[u8]) -> Self;

    #[requires(true)]
    fn serialize_4(a: Self) -> [u8; 8];
    #[requires(true)]
    fn deserialize_4(a: &[u8]) -> Self;

    #[requires(true)]
    fn serialize_5(a: Self) -> [u8; 10];
    #[requires(true)]
    fn deserialize_5(a: &[u8]) -> Self;

    #[requires(true)]
    fn serialize_10(a: Self) -> [u8; 20];
    #[requires(true)]
    fn deserialize_10(a: &[u8]) -> Self;

    #[requires(true)]
    fn serialize_11(a: Self) -> [u8; 22];
    #[requires(true)]
    fn deserialize_11(a: &[u8]) -> Self;

    #[requires(true)]
    fn serialize_12(a: Self) -> [u8; 24];
    #[requires(true)]
    fn deserialize_12(a: &[u8]) -> Self;

    #[requires(true)]
    fn rej_sample(a: &[u8], out: &mut [i16]) -> usize;
}

// hax does not support trait with default implementations, so we use the following pattern
pub fn montgomery_multiply_fe<T: Operations>(v: T, fer: i16) -> T {
    T::montgomery_multiply_by_constant(v, fer)
}
pub fn to_standard_domain<T: Operations>(v: T) -> T {
    T::montgomery_multiply_by_constant(v, MONTGOMERY_R_SQUARED_MOD_FIELD_MODULUS as i16)
}

pub fn to_unsigned_representative<T: Operations>(a: T) -> T {
    let t = T::shift_right::<15>(a);
    let fm = T::bitwise_and_with_constant(t, FIELD_MODULUS);
    T::add(a, &fm)
}

pub fn decompress_1<T: Operations>(v: T) -> T {
    hax_lib::fstar!("assert (i1.f_bitwise_and_with_constant_pre (i1.f_ZERO ()) 0s)"); // No idea why, but this helps F* typeclass inference
    T::bitwise_and_with_constant(T::sub(T::ZERO(), &v), 1665)
}

/// Internal vectors.
///
/// Used in the unpacked API.
pub trait VectorType: Operations {}

impl<T: Operations> VectorType for T {}
