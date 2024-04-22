use super::arithmetic::MONTGOMERY_R_SQUARED_MOD_FIELD_MODULUS;
use super::constants::FIELD_MODULUS;
use super::intvec32;

#[cfg(all(target_arch = "aarch64", feature = "simd128"))]
use super::intvec128;

#[cfg(all(target_arch = "aarch64", feature = "simd128"))]
pub(crate) type IntVec = intvec128::IntVec;

#[cfg(any(not(target_arch = "aarch64"), not(feature = "simd128")))]
pub(crate) type IntVec = intvec32::IntVec;

pub(crate) const SIZE_VEC: usize = 8;

// Eventually, this should only be used for debugging
// In the meantime, it allows us to convert between different vector representations
#[inline(always)]
pub(crate) fn int_vec_to_i32_array(a: IntVec) -> [i32; 8] {
    #[cfg(all(target_arch = "aarch64", feature = "simd128"))]
    let res = intvec128::int_vec_to_i32_array(&a);
    #[cfg(any(not(target_arch = "aarch64"), not(feature = "simd128")))]
    let res = intvec32::int_vec_to_i32_array(a);
    res
}

// This function is currently used in sampling (until we figure out how to vectorize sampling)
// Eventually, this should only be used for debugging
// In the meantime, it allows us to convert between different vector representations
#[inline(always)]
pub(crate) fn int_vec_from_i32_array(a: [i32; 8]) -> IntVec {
    #[cfg(all(target_arch = "aarch64", feature = "simd128"))]
    let res = intvec128::int_vec_from_i32_array(a);
    #[cfg(any(not(target_arch = "aarch64"), not(feature = "simd128")))]
    let res = intvec32::int_vec_from_i32_array(a);
    res
}

// This is used to initialize polynomials, but is actually tricky for vector representations
// Replace with a function
pub(crate) const ZERO_VEC: IntVec = intvec32::ZERO_VEC;

// Basic addition with a constant
#[inline(always)]
pub(crate) fn add_int_vec_constant(lhs: IntVec, rhs: i32) -> IntVec {
    intvec32::add_int_vec_constant(lhs, rhs)
}

// Basic addition
#[inline(always)]
pub(crate) fn add_int_vec(lhs: IntVec, rhs: &IntVec) -> IntVec {
    intvec32::add_int_vec(lhs, rhs)
}

// Basic subtraction
#[inline(always)]
pub(crate) fn sub_int_vec(lhs: IntVec, rhs: &IntVec) -> IntVec {
    intvec32::sub_int_vec(lhs, rhs)
}

// Basic multiplication with constant
#[inline(always)]
pub(crate) fn mul_int_vec_constant(lhs: IntVec, rhs: i32) -> IntVec {
    intvec32::mul_int_vec_constant(lhs, rhs)
}

// Basic multiplication with constant
#[inline(always)]
pub(crate) fn bit_and_int_vec_constant(lhs: IntVec, rhs: i32) -> IntVec {
    intvec32::bit_and_int_vec_constant(lhs, rhs)
}

// Basic arithmetic shift right
#[inline(always)]
pub(crate) fn right_shift_int_vec(lhs: IntVec, rhs: u8) -> IntVec {
    intvec32::right_shift_int_vec(lhs, rhs)
}

// Basic shift left
#[inline(always)]
pub(crate) fn left_shift_int_vec(lhs: IntVec, rhs: u8) -> IntVec {
    intvec32::left_shift_int_vec(lhs, rhs)
}

// Basic modulus
#[inline(always)]
pub(crate) fn modulus_int_vec_constant_var_time(lhs: IntVec, rhs: i32) -> IntVec {
    intvec32::modulus_int_vec_constant_var_time(lhs, rhs)
}

/// Arithmetic and serialization unctions that need specialized implementations

// Barrett: needs specialized implementation since i32 gets multiplied to obtain intermediate i64
#[inline(always)]
pub(crate) fn barrett_reduce_int_vec(a: IntVec) -> IntVec {
    intvec32::barrett_reduce_int_vec(a)
}

// Montgomery: mostly generic but uses a u32->i16->i32 conversion that may need specialized treatment
#[inline(always)]
pub(crate) fn montgomery_reduce_int_vec(a: IntVec) -> IntVec {
    intvec32::montgomery_reduce_int_vec(a)
}

// Compress Message Coefficient: mostly generic but uses some i16 arithmetic
#[inline(always)]
pub(crate) fn compress_1_int_vec(a: IntVec) -> IntVec {
    intvec32::compress_1_int_vec(a)
}

// Compress Ciphertext Coefficient: mostly generic but uses some i64 arithmetic
#[inline(always)]
pub(crate) fn compress_int_vec(coefficient_bits: u8, a: IntVec) -> IntVec {
    intvec32::compress_int_vec(coefficient_bits, a)
}

/// NTT
///
#[inline(always)]
pub(crate) fn ntt_layer_1_int_vec_step(a: IntVec, zeta1: i32, zeta2: i32) -> IntVec {
    intvec32::ntt_layer_1_int_vec_step(a, zeta1, zeta2)
}

#[inline(always)]
pub(crate) fn ntt_layer_2_int_vec_step(a: IntVec, zeta: i32) -> IntVec {
    intvec32::ntt_layer_2_int_vec_step(a, zeta)
}

#[inline(always)]
pub(crate) fn inv_ntt_layer_1_int_vec_step(a: IntVec, zeta1: i32, zeta2: i32) -> IntVec {
    intvec32::inv_ntt_layer_1_int_vec_step(a, zeta1, zeta2)
}

#[inline(always)]
pub(crate) fn inv_ntt_layer_2_int_vec_step(a: IntVec, zeta: i32) -> IntVec {
    intvec32::inv_ntt_layer_2_int_vec_step(a, zeta)
}

#[inline(always)]
pub(crate) fn ntt_multiply_int_vec(lhs: &IntVec, rhs: &IntVec, zeta0: i32, zeta1: i32) -> IntVec {
    intvec32::ntt_multiply_int_vec(lhs, rhs, zeta0, zeta1)
}

/// SERIALIZE - DESERIALIZE
///
#[inline(always)]
pub(crate) fn serialize_1_int_vec(a: IntVec) -> u8 {
    intvec32::serialize_1_int_vec(a)
}

#[inline(always)]
pub(crate) fn deserialize_1_int_vec(a: u8) -> IntVec {
    intvec32::deserialize_1_int_vec(a)
}

#[inline(always)]
pub(crate) fn serialize_5_int_vec(a: IntVec) -> [u8; 5] {
    intvec32::serialize_5_int_vec(a)
}

#[inline(always)]
pub(crate) fn deserialize_5_int_vec(bytes: &[u8]) -> IntVec {
    intvec32::deserialize_5_int_vec(bytes)
}

#[inline(always)]
pub(crate) fn serialize_4_int_vec(a: IntVec) -> [u8; 4] {
    intvec32::serialize_4_int_vec(a)
}

#[inline(always)]
pub(crate) fn deserialize_4_int_vec(bytes: &[u8]) -> IntVec {
    intvec32::deserialize_4_int_vec(bytes)
}

#[inline(always)]
pub(crate) fn serialize_10_int_vec(a: IntVec) -> [u8; 10] {
    intvec32::serialize_10_int_vec(a)
}

#[inline(always)]
pub(crate) fn deserialize_10_int_vec(bytes: &[u8]) -> IntVec {
    intvec32::deserialize_10_int_vec(bytes)
}

#[inline(always)]
pub(crate) fn serialize_11_int_vec(a: IntVec) -> [u8; 11] {
    intvec32::serialize_11_int_vec(a)
}

#[inline(always)]
pub(crate) fn deserialize_11_int_vec(bytes: &[u8]) -> IntVec {
    intvec32::deserialize_11_int_vec(bytes)
}

#[inline(always)]
pub(crate) fn serialize_12_int_vec(a: IntVec) -> [u8; 12] {
    intvec32::serialize_12_int_vec(a)
}

#[inline(always)]
pub(crate) fn deserialize_12_int_vec(bytes: &[u8]) -> IntVec {
    intvec32::deserialize_12_int_vec(bytes)
}

/// Pointwise Arithmetic Operations: generic
///

#[inline(always)]
pub(crate) fn to_standard_domain_int_vec(a: IntVec) -> IntVec {
    let t = mul_int_vec_constant(a, MONTGOMERY_R_SQUARED_MOD_FIELD_MODULUS);
    montgomery_reduce_int_vec(t)
}

#[inline(always)]
pub(crate) fn to_unsigned_representative_int_vec(a: IntVec) -> IntVec {
    let t = right_shift_int_vec(a, 31);
    let fm = bit_and_int_vec_constant(t, FIELD_MODULUS);
    add_int_vec(a, &fm)
}

#[inline(always)]
pub(crate) fn montgomery_multiply_fe_by_fer_int_vec(a: IntVec, b: i32) -> IntVec {
    let t = mul_int_vec_constant(a, b);
    montgomery_reduce_int_vec(t)
}

#[inline(always)]
pub(crate) fn decompress_1_int_vec(a: IntVec) -> IntVec {
    bit_and_int_vec_constant(sub_int_vec(ZERO_VEC, &a), 1665)
}

#[inline(always)]
pub(crate) fn decompress_int_vec(coefficient_bits: u8, a: IntVec) -> IntVec {
    let mut decompressed = mul_int_vec_constant(a, FIELD_MODULUS);
    decompressed = add_int_vec_constant(
        left_shift_int_vec(decompressed, 1),
        1i32 << coefficient_bits,
    );
    decompressed = right_shift_int_vec(decompressed, coefficient_bits + 1);
    decompressed
}
