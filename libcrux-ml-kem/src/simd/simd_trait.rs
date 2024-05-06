use crate::arithmetic::MONTGOMERY_R_SQUARED_MOD_FIELD_MODULUS;
use crate::constants::FIELD_MODULUS;

pub(crate) const FIELD_ELEMENTS_IN_VECTOR: usize = 8;

pub(crate) trait Operations {
    #[allow(non_snake_case)]
    fn ZERO() -> Self;

    fn to_i16_array(v: Self) -> [i16; 8];
    fn from_i16_array(array: [i16; 8]) -> Self;

    // Basic arithmetic
//    fn add_constant(v: Self, c: i16) -> Self;
    fn add(lhs: Self, rhs: &Self) -> Self;
    fn sub(lhs: Self, rhs: &Self) -> Self;
    fn multiply_by_constant(v: Self, c: i16) -> Self;

    // Bitwise operations
    fn bitwise_and_with_constant(v: Self, c: i16) -> Self;
    fn shift_right<const SHIFT_BY: i32>(v: Self) -> Self;
//    fn shift_left<const SHIFT_BY: i32>(v: Self) -> Self;

    // Modular operations
    fn cond_subtract_3329(v: Self) -> Self;
    fn barrett_reduce(v: Self) -> Self;
//  fn montgomery_reduce(v: Self) -> Self;

    fn montgomery_multiply_by_constant(v: Self, c: i16) -> Self;

    // Compression
    fn compress_1(v: Self) -> Self;
    fn compress<const COEFFICIENT_BITS: i32>(v: Self) -> Self;
    fn decompress<const COEFFICIENT_BITS: i32>(v: Self) -> Self;

    // NTT
    fn ntt_layer_1_step(a: Self, zeta1: i16, zeta2: i16) -> Self;
    fn ntt_layer_2_step(a: Self, zeta: i16) -> Self;

    fn inv_ntt_layer_1_step(a: Self, zeta1: i16, zeta2: i16) -> Self;
    fn inv_ntt_layer_2_step(a: Self, zeta: i16) -> Self;

    fn ntt_multiply(lhs: &Self, rhs: &Self, zeta0: i16, zeta1: i16) -> Self;

    // Serialization and deserialization
    fn serialize_1(a: Self) -> u8;
    fn deserialize_1(a: u8) -> Self;

    fn serialize_4(a: Self) -> [u8; 4];
    fn deserialize_4(a: &[u8]) -> Self;

    fn serialize_5(a: Self) -> [u8; 5];
    fn deserialize_5(a: &[u8]) -> Self;

    fn serialize_10(a: Self) -> [u8; 10];
    fn deserialize_10(a: &[u8]) -> Self;

    fn serialize_11(a: Self) -> [u8; 11];
    fn deserialize_11(a: &[u8]) -> Self;

    fn serialize_12(a: Self) -> [u8; 12];
    fn deserialize_12(a: &[u8]) -> Self;
}

// hax does not support trait with default implementations, so we use the following patter
pub(crate) trait GenericOperations {
    fn montgomery_multiply_fe_by_fer(v: Self, fer: i16) -> Self;
    fn to_standard_domain(v: Self) -> Self;
    fn to_unsigned_representative(a: Self) -> Self;
    fn decompress_1(v: Self) -> Self;
}

impl<T: Operations + Clone + Copy> GenericOperations for T {
    #[inline(always)]
    fn montgomery_multiply_fe_by_fer(v: Self, fer: i16) -> Self {
        Self::montgomery_multiply_by_constant(v, fer)
    }

    #[inline(always)]
    fn to_standard_domain(v: Self) -> Self {
        Self::montgomery_multiply_by_constant(v, MONTGOMERY_R_SQUARED_MOD_FIELD_MODULUS as i16)
    }
     
    fn to_unsigned_representative(a: Self) -> Self {
        let t = Self::shift_right::<15>(a);
        let fm = Self::bitwise_and_with_constant(t, FIELD_MODULUS as i16);
        Self::add(a, &fm)
    }

    fn decompress_1(v: Self) -> Self {
        Self::bitwise_and_with_constant(Self::sub(Self::ZERO(), &v), 1665)
    }
}
