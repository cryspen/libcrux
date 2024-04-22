#![allow(dead_code)]
use crate::{
    polynomial::{from_i32_array, to_i32_array},
    simd::fallback,
};
use core::arch::aarch64::*;

#[derive(Clone, Copy)]
pub(crate) struct IntVec {
    low: int32x4_t,
    high: int32x4_t,
}

pub(crate) const SIZE_VEC: usize = 8;

pub(crate) fn ZERO_VEC() -> IntVec {
    IntVec {
        low: unsafe { vdupq_n_s32(0) },
        high: unsafe { vdupq_n_s32(0) },
    }
}

// Eventually, this should only be used for debugging
// In the meantime, it allows us to convert between different vector representations
#[inline(always)]
pub(crate) fn to_i32_array(a: &IntVec) -> [i32; 8] {
    let mut out = [0i32; 8];
    unsafe { vst1q_s32(out[0..4].as_mut_ptr() as *mut i32, a.low) }
    unsafe { vst1q_s32(out[4..8].as_mut_ptr() as *mut i32, a.high) }
    out
}

// This function is used in sampling (until we figure out how to vectorize it)
// Eventually, this should only be used for debugging
// In the meantime, it allows us to convert between different vector representations
#[inline(always)]
pub(crate) fn from_i32_array(a: [i32; 8]) -> IntVec {
    IntVec {
        low: unsafe { vld1q_s32(a[0..4].as_ptr() as *const i32) },
        high: unsafe { vld1q_s32(a[4..8].as_ptr() as *const i32) },
    }
}

// Basic addition with a constant
#[inline(always)]
pub(crate) fn add_constant(mut lhs: IntVec, rhs: i32) -> IntVec {
    let rhs = unsafe { vdupq_n_s32(rhs) };
    lhs.low = unsafe { vaddq_s32(lhs.low, rhs) };
    lhs.high = unsafe { vaddq_s32(lhs.high, rhs) };
    lhs
}

// Basic addition
#[inline(always)]
pub(crate) fn add(mut lhs: IntVec, rhs: &IntVec) -> IntVec {
    lhs.low = unsafe { vaddq_s32(lhs.low, rhs.low) };
    lhs.high = unsafe { vaddq_s32(lhs.high, rhs.high) };
    lhs
}

// Basic subtraction
#[inline(always)]
pub(crate) fn sub(mut lhs: IntVec, rhs: &IntVec) -> IntVec {
    lhs.low = unsafe { vsubq_s32(lhs.low, rhs.low) };
    lhs.high = unsafe { vsubq_s32(lhs.high, rhs.high) };
    lhs
}

// Basic multiplication with constant
#[inline(always)]
pub(crate) fn mul_constant(mut lhs: IntVec, rhs: i32) -> IntVec {
    lhs.low = unsafe { vmulq_n_s32(lhs.low, rhs) };
    lhs.high = unsafe { vmulq_n_s32(lhs.high, rhs) };
    lhs
}

// Basic multiplication with constant
#[inline(always)]
pub(crate) fn bit_and_constant(mut lhs: IntVec, rhs: i32) -> IntVec {
    let rhs = unsafe { vdupq_n_s32(rhs) };
    lhs.low = unsafe { vandq_s32(lhs.low, rhs) };
    lhs.high = unsafe { vandq_s32(lhs.high, rhs) };
    lhs
}

// Basic arithmetic shift right
#[inline(always)]
pub(crate) fn right_shift(mut lhs: IntVec, rhs: u8) -> IntVec {
    // Should find special cases of this
    // e.g when doing a right shift just to propagate signed bits, use vclezq_s32 instead
    let rhs = unsafe { vdupq_n_s32(-(rhs as i32)) };
    lhs.low = unsafe { vshlq_s32(lhs.low, rhs) };
    lhs.high = unsafe { vshlq_s32(lhs.high, rhs) };
    lhs
}

// Basic shift left
#[inline(always)]
pub(crate) fn left_shift(mut lhs: IntVec, rhs: u8) -> IntVec {
    let rhs = unsafe { vdupq_n_s32(rhs as i32) };
    lhs.low = unsafe { vshlq_s32(lhs.low, rhs) };
    lhs.high = unsafe { vshlq_s32(lhs.high, rhs) };
    lhs
}

// Basic modulus
#[inline(always)]
pub(crate) fn modulus_constant_var_time(lhs: IntVec, rhs: i32) -> IntVec {
    let mut i32s = to_i32_array(&lhs);
    for i in 0..SIZE_VEC {
        i32s[i] = i32s[i] % rhs;
    }
    from_i32_array(i32s)
}

/// Arithmetic and serialization unctions that need specialized implementations

// Barrett: needs specialized implementation since i32 gets multiplied to obtain intermediate i64
#[inline(always)]
pub(crate) fn barrett_reduce(a: IntVec) -> IntVec {
    let input = fallback::from_i32_array(to_i32_array(&a));
    let output = fallback::barrett_reduce(input);
    from_i32_array(fallback::to_i32_array(output))
}

// Montgomery: mostly generic but uses a u32->i16->i32 conversion that may need specialized treatment
#[inline(always)]
pub(crate) fn montgomery_reduce(a: IntVec) -> IntVec {
    let input = fallback::from_i32_array(to_i32_array(&a));
    let output = fallback::montgomery_reduce(input);
    from_i32_array(fallback::to_i32_array(output))
}

// Compress Message Coefficient: mostly generic but uses some i16 arithmetic
#[inline(always)]
pub(crate) fn compress_1(a: IntVec) -> IntVec {
    let input = fallback::from_i32_array(to_i32_array(&a));
    let output = fallback::compress_1(input);
    from_i32_array(fallback::to_i32_array(output))
}

// Compress Ciphertext Coefficient: mostly generic but uses some i64 arithmetic
#[inline(always)]
pub(crate) fn compress(coefficient_bits: u8, a: IntVec) -> IntVec {
    let input = fallback::from_i32_array(to_i32_array(&a));
    let output = fallback::compress(coefficient_bits, input);
    from_i32_array(fallback::to_i32_array(output))
}

/// NTT
///
#[inline(always)]
pub(crate) fn ntt_layer_1_step(a: IntVec, zeta1: i32, zeta2: i32) -> IntVec {
    let input = fallback::from_i32_array(to_i32_array(&a));
    let output = fallback::ntt_layer_1_step(input, zeta1, zeta2);
    from_i32_array(fallback::to_i32_array(output))
}

#[inline(always)]
pub(crate) fn ntt_layer_2_step(a: IntVec, zeta: i32) -> IntVec {
    let input = fallback::from_i32_array(to_i32_array(&a));
    let output = fallback::ntt_layer_2_step(input, zeta);
    from_i32_array(fallback::to_i32_array(output))
}

#[inline(always)]
pub(crate) fn inv_ntt_layer_1_step(a: IntVec, zeta1: i32, zeta2: i32) -> IntVec {
    let input = fallback::from_i32_array(to_i32_array(&a));
    let output = fallback::inv_ntt_layer_1_step(input, zeta1, zeta2);
    from_i32_array(fallback::to_i32_array(output))
}

#[inline(always)]
pub(crate) fn inv_ntt_layer_2_step(a: IntVec, zeta: i32) -> IntVec {
    let input = fallback::from_i32_array(to_i32_array(&a));
    let output = fallback::inv_ntt_layer_2_step(input, zeta);
    from_i32_array(fallback::to_i32_array(output))
}

#[inline(always)]
pub(crate) fn ntt_multiply(lhs: &IntVec, rhs: &IntVec, zeta0: i32, zeta1: i32) -> IntVec {
    let input1 = fallback::from_i32_array(to_i32_array(lhs));
    let input2 = fallback::from_i32_array(to_i32_array(rhs));
    let output = fallback::ntt_multiply(&input1, &input2, zeta0, zeta1);
    from_i32_array(fallback::to_i32_array(output))
}

/// SERIALIZE - DESERIALIZE
///
#[inline(always)]
pub(crate) fn serialize_1(a: IntVec) -> u8 {
    let input = fallback::from_i32_array(to_i32_array(&a));
    fallback::serialize_1(input)
}

#[inline(always)]
pub(crate) fn deserialize_1(a: u8) -> IntVec {
    let output = fallback::deserialize_1(a);
    from_i32_array(fallback::to_i32_array(output))
}

#[inline(always)]
pub(crate) fn serialize_5(a: IntVec) -> [u8; 5] {
    let input = fallback::from_i32_array(to_i32_array(&a));
    fallback::serialize_5(input)
}

#[inline(always)]
pub(crate) fn deserialize_5(a: &[u8]) -> IntVec {
    let output = fallback::deserialize_5(a);
    from_i32_array(fallback::to_i32_array(output))
}

#[inline(always)]
pub(crate) fn serialize_4(a: IntVec) -> [u8; 4] {
    let input = fallback::from_i32_array(to_i32_array(&a));
    fallback::serialize_4(input)
}

#[inline(always)]
pub(crate) fn deserialize_4(a: &[u8]) -> IntVec {
    let output = fallback::deserialize_4(a);
    from_i32_array(fallback::to_i32_array(output))
}

#[inline(always)]
pub(crate) fn serialize_10(a: IntVec) -> [u8; 10] {
    let input = fallback::from_i32_array(to_i32_array(&a));
    fallback::serialize_10(input)
}

#[inline(always)]
pub(crate) fn deserialize_10(a: &[u8]) -> IntVec {
    let output = fallback::deserialize_10(a);
    from_i32_array(fallback::to_i32_array(output))
}

#[inline(always)]
pub(crate) fn serialize_11(a: IntVec) -> [u8; 11] {
    let input = fallback::from_i32_array(to_i32_array(&a));
    fallback::serialize_11(input)
}

#[inline(always)]
pub(crate) fn deserialize_11(a: &[u8]) -> IntVec {
    let output = fallback::deserialize_11(a);
    from_i32_array(fallback::to_i32_array(output))
}

#[inline(always)]
pub(crate) fn serialize_12(a: IntVec) -> [u8; 12] {
    let input = fallback::from_i32_array(to_i32_array(&a));
    fallback::serialize_12(input)
}

#[inline(always)]
pub(crate) fn deserialize_12(a: &[u8]) -> IntVec {
    let output = fallback::deserialize_12(a);
    from_i32_array(fallback::to_i32_array(output))
}
