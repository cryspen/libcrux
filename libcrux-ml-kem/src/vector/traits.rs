pub const MONTGOMERY_R_SQUARED_MOD_FIELD_MODULUS: i16 = 1353;
pub const FIELD_MODULUS: i16 = 3329;
pub const FIELD_ELEMENTS_IN_VECTOR: usize = 16;
pub const INVERSE_OF_MODULUS_MOD_MONTGOMERY_R: u32 = 62209; // FIELD_MODULUS^{-1} mod MONTGOMERY_R

pub trait Operations: Copy + Clone {
    #[allow(non_snake_case)]
    fn ZERO() -> Self;

    fn from_i16_array(array: &[i16]) -> Self;
    fn to_i16_array(x: Self) -> [i16; 16];

    // Basic arithmetic
    fn add(lhs: Self, rhs: &Self) -> Self;
    fn sub(lhs: Self, rhs: &Self) -> Self;
    fn multiply_by_constant(v: Self, c: i16) -> Self;

    // Bitwise operations
    fn bitwise_and_with_constant(v: Self, c: i16) -> Self;
    fn shift_right<const SHIFT_BY: i32>(v: Self) -> Self;
    // fn shift_left<const SHIFT_BY: i32>(v: Self) -> Self;

    // Modular operations
    fn cond_subtract_3329(v: Self) -> Self;
    fn barrett_reduce(v: Self) -> Self;
    fn montgomery_multiply_by_constant(v: Self, c: i16) -> Self;

    // Compression
    fn compress_1(v: Self) -> Self;
    fn compress<const COEFFICIENT_BITS: i32>(v: Self) -> Self;
    fn decompress_ciphertext_coefficient<const COEFFICIENT_BITS: i32>(v: Self) -> Self;

    // NTT
    fn ntt_layer_1_step(a: Self, zeta0: i16, zeta1: i16, zeta2: i16, zeta3: i16) -> Self;
    fn ntt_layer_2_step(a: Self, zeta0: i16, zeta1: i16) -> Self;
    fn ntt_layer_3_step(a: Self, zeta: i16) -> Self;

    fn inv_ntt_layer_1_step(a: Self, zeta0: i16, zeta1: i16, zeta2: i16, zeta3: i16) -> Self;
    fn inv_ntt_layer_2_step(a: Self, zeta0: i16, zeta1: i16) -> Self;
    fn inv_ntt_layer_3_step(a: Self, zeta: i16) -> Self;

    fn ntt_multiply(lhs: &Self, rhs: &Self, zeta0: i16, zeta1: i16, zeta2: i16, zeta3: i16)
        -> Self;

    // Serialization and deserialization
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
    T::bitwise_and_with_constant(T::sub(T::ZERO(), &v), 1665)
}
