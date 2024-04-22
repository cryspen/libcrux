use crate::arithmetic::MONTGOMERY_R_SQUARED_MOD_FIELD_MODULUS;
use crate::constants::FIELD_MODULUS;

#[cfg(feature = "simd128")]
pub(crate) type IntVec = super::intvec128::IntVec;

#[cfg(not(feature = "simd128"))]
pub(crate) type IntVec = super::intvec32::IntVec;

pub(crate) const SIZE_VEC: usize = 8;

// Eventually, this should only be used for debugging
// In the meantime, it allows us to convert between different vector representations
#[inline(always)]
pub(crate) fn to_i32_array(a: IntVec) -> [i32; 8] {
    #[cfg(all(target_arch = "aarch64", feature = "simd128"))]
    let res = simd128::to_i32_array(&a);
    #[cfg(any(not(target_arch = "aarch64"), not(feature = "simd128")))]
    let res = fallback::to_i32_array(a);
    res
}

// This function is currently used in sampling (until we figure out how to vectorize sampling)
// Eventually, this should only be used for debugging
// In the meantime, it allows us to convert between different vector representations
#[inline(always)]
pub(crate) fn from_i32_array(a: [i32; 8]) -> IntVec {
    #[cfg(all(target_arch = "aarch64", feature = "simd128"))]
    let res = simd128::from_i32_array(a);
    #[cfg(any(not(target_arch = "aarch64"), not(feature = "simd128")))]
    let res = fallback::from_i32_array(a);
    res
}

// This is used to initialize polynomials, but is actually tricky for vector representations
// Replace with a function
pub(crate) const ZERO_VEC: IntVec = fallback::ZERO_VEC;

// Basic addition with a constant
#[inline(always)]
pub(crate) fn add_constant(lhs: IntVec, rhs: i32) -> IntVec {
    fallback::add_constant(lhs, rhs)
}

// Basic addition
#[inline(always)]
pub(crate) fn add(lhs: IntVec, rhs: &IntVec) -> IntVec {
    fallback::add(lhs, rhs)
}

// Basic subtraction
#[inline(always)]
pub(crate) fn sub(lhs: IntVec, rhs: &IntVec) -> IntVec {
    fallback::sub(lhs, rhs)
}

// Basic multiplication with constant
#[inline(always)]
pub(crate) fn mul_constant(lhs: IntVec, rhs: i32) -> IntVec {
    fallback::mul_constant(lhs, rhs)
}

// Basic multiplication with constant
#[inline(always)]
pub(crate) fn bit_and_constant(lhs: IntVec, rhs: i32) -> IntVec {
    fallback::bit_and_constant(lhs, rhs)
}

// Basic arithmetic shift right
#[inline(always)]
pub(crate) fn right_shift(lhs: IntVec, rhs: u8) -> IntVec {
    fallback::right_shift(lhs, rhs)
}

// Basic shift left
#[inline(always)]
pub(crate) fn left_shift(lhs: IntVec, rhs: u8) -> IntVec {
    fallback::left_shift(lhs, rhs)
}

// Basic modulus
#[inline(always)]
pub(crate) fn modulus_constant_var_time(lhs: IntVec, rhs: i32) -> IntVec {
    fallback::modulus_constant_var_time(lhs, rhs)
}

/// Arithmetic and serialization unctions that need specialized implementations

// Barrett: needs specialized implementation since i32 gets multiplied to obtain intermediate i64
#[inline(always)]
pub(crate) fn barrett_reduce(a: IntVec) -> IntVec {
    fallback::barrett_reduce(a)
}

// Montgomery: mostly generic but uses a u32->i16->i32 conversion that may need specialized treatment
#[inline(always)]
pub(crate) fn montgomery_reduce(a: IntVec) -> IntVec {
    fallback::montgomery_reduce(a)
}

// Compress Message Coefficient: mostly generic but uses some i16 arithmetic
#[inline(always)]
pub(crate) fn compress_1(a: IntVec) -> IntVec {
    fallback::compress_1(a)
}

// Compress Ciphertext Coefficient: mostly generic but uses some i64 arithmetic
#[inline(always)]
pub(crate) fn compress(coefficient_bits: u8, a: IntVec) -> IntVec {
    fallback::compress(coefficient_bits, a)
}

/// NTT
///
#[inline(always)]
pub(crate) fn ntt_layer_1_step(a: IntVec, zeta1: i32, zeta2: i32) -> IntVec {
    fallback::ntt_layer_1_step(a, zeta1, zeta2)
}

#[inline(always)]
pub(crate) fn ntt_layer_2_step(a: IntVec, zeta: i32) -> IntVec {
    fallback::ntt_layer_2_step(a, zeta)
}

#[inline(always)]
pub(crate) fn inv_ntt_layer_1_step(a: IntVec, zeta1: i32, zeta2: i32) -> IntVec {
    fallback::inv_ntt_layer_1_step(a, zeta1, zeta2)
}

#[inline(always)]
pub(crate) fn inv_ntt_layer_2_step(a: IntVec, zeta: i32) -> IntVec {
    fallback::inv_ntt_layer_2_step(a, zeta)
}

#[inline(always)]
pub(crate) fn ntt_multiply(lhs: &IntVec, rhs: &IntVec, zeta0: i32, zeta1: i32) -> IntVec {
    fallback::ntt_multiply(lhs, rhs, zeta0, zeta1)
}

/// SERIALIZE - DESERIALIZE
///
#[inline(always)]
pub(crate) fn serialize_1(a: IntVec) -> u8 {
    fallback::serialize_1(a)
}

#[inline(always)]
pub(crate) fn deserialize_1(a: u8) -> IntVec {
    fallback::deserialize_1(a)
}

#[inline(always)]
pub(crate) fn serialize_5(a: IntVec) -> [u8; 5] {
    fallback::serialize_5(a)
}

#[inline(always)]
pub(crate) fn deserialize_5(bytes: &[u8]) -> IntVec {
    fallback::deserialize_5(bytes)
}

#[inline(always)]
pub(crate) fn serialize_4(a: IntVec) -> [u8; 4] {
    fallback::serialize_4(a)
}

#[inline(always)]
pub(crate) fn deserialize_4(bytes: &[u8]) -> IntVec {
    fallback::deserialize_4(bytes)
}

#[inline(always)]
pub(crate) fn serialize_10(a: IntVec) -> [u8; 10] {
    fallback::serialize_10(a)
}

#[inline(always)]
pub(crate) fn deserialize_10(bytes: &[u8]) -> IntVec {
    fallback::deserialize_10(bytes)
}

#[inline(always)]
pub(crate) fn serialize_11(a: IntVec) -> [u8; 11] {
    fallback::serialize_11(a)
}

#[inline(always)]
pub(crate) fn deserialize_11(bytes: &[u8]) -> IntVec {
    fallback::deserialize_11(bytes)
}

#[inline(always)]
pub(crate) fn serialize_12(a: IntVec) -> [u8; 12] {
    fallback::serialize_12(a)
}

#[inline(always)]
pub(crate) fn deserialize_12(bytes: &[u8]) -> IntVec {
    fallback::deserialize_12(bytes)
}

/// Pointwise Arithmetic Operations: generic
///

#[inline(always)]
pub(crate) fn to_standard_domain(a: IntVec) -> IntVec {
    let t = mul_constant(a, MONTGOMERY_R_SQUARED_MOD_FIELD_MODULUS);
    montgomery_reduce(t)
}

#[inline(always)]
pub(crate) fn to_unsigned_representative(a: IntVec) -> IntVec {
    let t = right_shift(a, 31);
    let fm = bit_and_constant(t, FIELD_MODULUS);
    add(a, &fm)
}

#[inline(always)]
pub(crate) fn montgomery_multiply_fe_by_fer(a: IntVec, b: i32) -> IntVec {
    let t = mul_constant(a, b);
    montgomery_reduce(t)
}

#[inline(always)]
pub(crate) fn decompress_1(a: IntVec) -> IntVec {
    bit_and_constant(sub(ZERO_VEC, &a), 1665)
}

#[inline(always)]
pub(crate) fn decompress(coefficient_bits: u8, a: IntVec) -> IntVec {
    let mut decompressed = mul_constant(a, FIELD_MODULUS);
    decompressed = add_constant(left_shift(decompressed, 1), 1i32 << coefficient_bits);
    decompressed = right_shift(decompressed, coefficient_bits + 1);
    decompressed
}
