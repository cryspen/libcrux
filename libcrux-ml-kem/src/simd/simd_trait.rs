use crate::arithmetic::MONTGOMERY_R_SQUARED_MOD_FIELD_MODULUS;
use crate::constants::FIELD_MODULUS;

pub(crate) const FIELD_ELEMENTS_IN_VECTOR: usize = 8;

pub(crate) trait Operations: Clone + Copy {
    #[allow(non_snake_case)]
    fn ZERO() -> Self;

    fn to_i32_array(v: Self) -> [i32; 8];
    fn from_i32_array(array: [i32; 8]) -> Self;

    // Basic arithmetic
    fn add_constant(v: Self, c: i32) -> Self;
    fn add(lhs: Self, rhs: &Self) -> Self;
    fn sub(lhs: Self, rhs: &Self) -> Self;
    fn multiply_by_constant(v: Self, c: i32) -> Self;

    // Bitwise operations
    fn bitwise_and_with_constant(v: Self, c: i32) -> Self;
    fn shift_right<const SHIFT_BY: i32>(v: Self) -> Self;
    fn shift_left<const SHIFT_BY: i32>(v: Self) -> Self;

    // Modular operations
    fn cond_subtract_3329(v: Self) -> Self;
    fn barrett_reduce(v: Self) -> Self;
    fn montgomery_reduce(v: Self) -> Self;

    // Compression
    fn compress_1(v: Self) -> Self;
    fn compress<const COEFFICIENT_BITS: i32>(v: Self) -> Self;

    // NTT
    fn ntt_layer_1_step(a: Self, zeta1: i32, zeta2: i32) -> Self;
    fn ntt_layer_2_step(a: Self, zeta: i32) -> Self;

    fn inv_ntt_layer_1_step(a: Self, zeta1: i32, zeta2: i32) -> Self;
    fn inv_ntt_layer_2_step(a: Self, zeta: i32) -> Self;

    fn ntt_multiply(lhs: &Self, rhs: &Self, zeta0: i32, zeta1: i32) -> Self;

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

// XXX: hax does not support trait with default implementations, so we use the following patter
pub(crate) trait GenericOperations {
    fn montgomery_multiply_fe_by_fer(v: Self, fer: i32) -> Self;
    fn to_standard_domain(v: Self) -> Self;
    fn to_unsigned_representative(a: Self) -> Self;
    fn decompress_1(v: Self) -> Self;
    fn decompress<const COEFFICIENT_BITS: i32>(v: Self) -> Self;
}

impl<T: Operations + Clone + Copy> GenericOperations for T {
    #[inline(always)]
    fn montgomery_multiply_fe_by_fer(v: Self, fer: i32) -> Self {
        let t = Self::multiply_by_constant(v, fer);
        Self::montgomery_reduce(t)
    }

    #[inline(always)]
    fn to_standard_domain(v: Self) -> Self {
        let t = Self::multiply_by_constant(v, MONTGOMERY_R_SQUARED_MOD_FIELD_MODULUS);
        Self::montgomery_reduce(t)
    }

    #[inline(always)]
    fn to_unsigned_representative(a: Self) -> Self {
        let t = Self::shift_right::<31>(a);
        let fm = Self::bitwise_and_with_constant(t, FIELD_MODULUS);
        Self::add(a, &fm)
    }

    #[inline(always)]
    fn decompress_1(v: Self) -> Self {
        Self::bitwise_and_with_constant(Self::sub(Self::ZERO(), &v), 1665)
    }

    #[inline(always)]
    fn decompress<const COEFFICIENT_BITS: i32>(v: Self) -> Self {
        let mut decompressed = Self::multiply_by_constant(v, FIELD_MODULUS);
        decompressed = Self::add_constant(
            Self::shift_left::<1>(decompressed),
            1i32 << COEFFICIENT_BITS,
        );
        let decompressed_1 = Self::shift_right::<{ COEFFICIENT_BITS }>(decompressed);
        let decompressed_2 = Self::shift_right::<1>(decompressed_1);
        decompressed_2
    }
}
