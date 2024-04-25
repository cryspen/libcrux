use crate::simd::{portable, simd_trait::*};
use core::arch::aarch64::*;

#[derive(Clone, Copy)]
pub(crate) struct SIMD128Vector {
    low: int32x4_t,
    high: int32x4_t,
}

#[allow(non_snake_case)]
#[inline(always)]
fn ZERO() -> SIMD128Vector {
    SIMD128Vector {
        low: unsafe { vdupq_n_s32(0) },
        high: unsafe { vdupq_n_s32(0) },
    }
}

#[inline(always)]
fn to_i32_array(v: SIMD128Vector) -> [i32; 8] {
    let mut out = [0i32; 8];

    unsafe { vst1q_s32(out[0..4].as_mut_ptr() as *mut i32, v.low) }
    unsafe { vst1q_s32(out[4..8].as_mut_ptr() as *mut i32, v.high) }

    out
}

#[inline(always)]
fn from_i32_array(array: [i32; 8]) -> SIMD128Vector {
    SIMD128Vector {
        low: unsafe { vld1q_s32(array[0..4].as_ptr() as *const i32) },
        high: unsafe { vld1q_s32(array[4..8].as_ptr() as *const i32) },
    }
}

#[inline(always)]
fn add_constant(mut v: SIMD128Vector, c: i32) -> SIMD128Vector {
    let c = unsafe { vdupq_n_s32(c) };

    v.low = unsafe { vaddq_s32(v.low, c) };
    v.high = unsafe { vaddq_s32(v.high, c) };

    v
}

#[inline(always)]
fn add(mut lhs: SIMD128Vector, rhs: &SIMD128Vector) -> SIMD128Vector {
    lhs.low = unsafe { vaddq_s32(lhs.low, rhs.low) };
    lhs.high = unsafe { vaddq_s32(lhs.high, rhs.high) };
    lhs
}

#[inline(always)]
fn sub(mut lhs: SIMD128Vector, rhs: &SIMD128Vector) -> SIMD128Vector {
    lhs.low = unsafe { vsubq_s32(lhs.low, rhs.low) };
    lhs.high = unsafe { vsubq_s32(lhs.high, rhs.high) };
    lhs
}

#[inline(always)]
fn multiply_by_constant(mut v: SIMD128Vector, c: i32) -> SIMD128Vector {
    v.low = unsafe { vmulq_n_s32(v.low, c) };
    v.high = unsafe { vmulq_n_s32(v.high, c) };

    v
}

#[inline(always)]
fn bitwise_and_with_constant(mut v: SIMD128Vector, c: i32) -> SIMD128Vector {
    let c = unsafe { vdupq_n_s32(c) };

    v.low = unsafe { vandq_s32(v.low, c) };
    v.high = unsafe { vandq_s32(v.high, c) };

    v
}

#[inline(always)]
fn shift_right<const SHIFT_BY: i32>(mut v: SIMD128Vector) -> SIMD128Vector {
    // Should find special cases of this
    // e.g when doing a right shift just to propagate signed bits, use vclezq_s32 instead
    v.low = unsafe { vshrq_n_s32(v.low, SHIFT_BY) };
    v.high = unsafe { vshrq_n_s32(v.high, SHIFT_BY) };
    v
}

#[inline(always)]
fn shift_left<const SHIFT_BY: i32>(mut lhs: SIMD128Vector) -> SIMD128Vector {
    lhs.low = unsafe { vshlq_n_s32(lhs.low, SHIFT_BY) };
    lhs.high = unsafe { vshlq_n_s32(lhs.high, SHIFT_BY) };
    lhs
}

#[inline(always)]
fn cond_subtract_3329(mut v: SIMD128Vector) -> SIMD128Vector {
    let c = unsafe { vdupq_n_s32(3329) };
    let m0 = unsafe { vreinterpretq_s32_u32(vcgeq_s32(v.low, c)) };
    let m1 = unsafe { vreinterpretq_s32_u32(vcgeq_s32(v.high, c)) };
    let rhs0 = unsafe { vandq_s32(m0, c) };
    let rhs1 = unsafe { vandq_s32(m1, c) };
    v.low = unsafe { vsubq_s32(v.low, rhs0) };
    v.high = unsafe { vsubq_s32(v.high, rhs1) };
    v
}

const BARRETT_MULTIPLIER: i32 = 20159;

#[inline(always)]
fn barrett_reduce(mut v: SIMD128Vector) -> SIMD128Vector {
    // let t = (i64::from(value) * BARRETT_MULTIPLIER) + (BARRETT_R >> 1);
    // let quotient = (t >> BARRETT_SHIFT) as i32;
    // let result = value - (quotient * FIELD_MODULUS);

    let adder = unsafe { vdupq_n_s64(33554432) };
    let low0 = unsafe { vmull_n_s32(vget_low_s32(v.low), BARRETT_MULTIPLIER) };
    let low1 = unsafe { vmull_n_s32(vget_high_s32(v.low), BARRETT_MULTIPLIER) };
    let high0 = unsafe { vmull_n_s32(vget_low_s32(v.high), BARRETT_MULTIPLIER) };
    let high1 = unsafe { vmull_n_s32(vget_high_s32(v.high), BARRETT_MULTIPLIER) };
    let low0 = unsafe { vshrq_n_s64(vaddq_s64(low0,adder),26) };
    let low1 = unsafe { vshrq_n_s64(vaddq_s64(low1,adder),26) };
    let high0 = unsafe { vshrq_n_s64(vaddq_s64(high0,adder),26) };
    let high1 = unsafe { vshrq_n_s64(vaddq_s64(high1,adder),26) };
    let low = unsafe { vcombine_s32(vmovn_s64(low0),vmovn_s64(low1)) };
    let high = unsafe { vcombine_s32(vmovn_s64(high0),vmovn_s64(high1)) };
    let low = unsafe { vmulq_n_s32(low,3329) };
    let high = unsafe { vmulq_n_s32(high,3329) };
    v.low = unsafe { vsubq_s32(v.low,low) };
    v.high = unsafe { vsubq_s32(v.high,high) };
    v
}

#[inline(always)]
fn montgomery_reduce(v: SIMD128Vector) -> SIMD128Vector {
    let input = portable::PortableVector::from_i32_array(SIMD128Vector::to_i32_array(v));
    let output = portable::PortableVector::montgomery_reduce(input);

    SIMD128Vector::from_i32_array(portable::PortableVector::to_i32_array(output))
}

#[inline(always)]
fn compress_1(v: SIMD128Vector) -> SIMD128Vector {
    let input = portable::PortableVector::from_i32_array(SIMD128Vector::to_i32_array(v));
    let output = portable::PortableVector::compress_1(input);

    SIMD128Vector::from_i32_array(portable::PortableVector::to_i32_array(output))
}

#[inline(always)]
fn compress(coefficient_bits: u8, v: SIMD128Vector) -> SIMD128Vector {
    let input = portable::PortableVector::from_i32_array(SIMD128Vector::to_i32_array(v));
    let output = portable::PortableVector::compress(coefficient_bits, input);

    SIMD128Vector::from_i32_array(portable::PortableVector::to_i32_array(output))
}

#[inline(always)]
fn ntt_layer_1_step(v: SIMD128Vector, zeta1: i32, zeta2: i32) -> SIMD128Vector {
    let input = portable::PortableVector::from_i32_array(SIMD128Vector::to_i32_array(v));
    let output = portable::PortableVector::ntt_layer_1_step(input, zeta1, zeta2);

    SIMD128Vector::from_i32_array(portable::PortableVector::to_i32_array(output))
}

#[inline(always)]
fn ntt_layer_2_step(v: SIMD128Vector, zeta: i32) -> SIMD128Vector {
    let input = portable::PortableVector::from_i32_array(SIMD128Vector::to_i32_array(v));
    let output = portable::PortableVector::ntt_layer_2_step(input, zeta);

    SIMD128Vector::from_i32_array(portable::PortableVector::to_i32_array(output))
}

#[inline(always)]
fn inv_ntt_layer_1_step(v: SIMD128Vector, zeta1: i32, zeta2: i32) -> SIMD128Vector {
    let input = portable::PortableVector::from_i32_array(SIMD128Vector::to_i32_array(v));
    let output = portable::PortableVector::inv_ntt_layer_1_step(input, zeta1, zeta2);

    SIMD128Vector::from_i32_array(portable::PortableVector::to_i32_array(output))
}

#[inline(always)]
fn inv_ntt_layer_2_step(v: SIMD128Vector, zeta: i32) -> SIMD128Vector {
    let input = portable::PortableVector::from_i32_array(SIMD128Vector::to_i32_array(v));
    let output = portable::PortableVector::inv_ntt_layer_2_step(input, zeta);

    SIMD128Vector::from_i32_array(portable::PortableVector::to_i32_array(output))
}

#[inline(always)]
fn ntt_multiply(lhs: &SIMD128Vector, rhs: &SIMD128Vector, zeta0: i32, zeta1: i32) -> SIMD128Vector {
    let input1 = portable::PortableVector::from_i32_array(SIMD128Vector::to_i32_array(*lhs));
    let input2 = portable::PortableVector::from_i32_array(SIMD128Vector::to_i32_array(*rhs));

    let output = portable::PortableVector::ntt_multiply(&input1, &input2, zeta0, zeta1);

    SIMD128Vector::from_i32_array(portable::PortableVector::to_i32_array(output))
}

#[inline(always)]
fn serialize_1(a: SIMD128Vector) -> u8 {
    let input = portable::PortableVector::from_i32_array(SIMD128Vector::to_i32_array(a));

    portable::PortableVector::serialize_1(input)
}

#[inline(always)]
fn deserialize_1(a: u8) -> SIMD128Vector {
    let output = portable::PortableVector::deserialize_1(a);

    SIMD128Vector::from_i32_array(portable::PortableVector::to_i32_array(output))
}

#[inline(always)]
fn serialize_4(v: SIMD128Vector) -> [u8; 4] {
    let input = portable::PortableVector::from_i32_array(SIMD128Vector::to_i32_array(v));
    portable::PortableVector::serialize_4(input)
}

#[inline(always)]
fn deserialize_4(v: &[u8]) -> SIMD128Vector {
    let output = portable::PortableVector::deserialize_4(v);

    SIMD128Vector::from_i32_array(portable::PortableVector::to_i32_array(output))
}

#[inline(always)]
fn serialize_5(v: SIMD128Vector) -> [u8; 5] {
    let input = portable::PortableVector::from_i32_array(SIMD128Vector::to_i32_array(v));

    portable::PortableVector::serialize_5(input)
}

#[inline(always)]
fn deserialize_5(v: &[u8]) -> SIMD128Vector {
    let output = portable::PortableVector::deserialize_5(v);

    SIMD128Vector::from_i32_array(portable::PortableVector::to_i32_array(output))
}

#[inline(always)]
fn serialize_10(v: SIMD128Vector) -> [u8; 10] {
    let input = portable::PortableVector::from_i32_array(SIMD128Vector::to_i32_array(v));
    portable::PortableVector::serialize_10(input)
}

#[inline(always)]
fn deserialize_10(v: &[u8]) -> SIMD128Vector {
    let output = portable::PortableVector::deserialize_10(v);

    SIMD128Vector::from_i32_array(portable::PortableVector::to_i32_array(output))
}

#[inline(always)]
fn serialize_11(v: SIMD128Vector) -> [u8; 11] {
    let input = portable::PortableVector::from_i32_array(SIMD128Vector::to_i32_array(v));
    portable::PortableVector::serialize_11(input)
}

#[inline(always)]
fn deserialize_11(v: &[u8]) -> SIMD128Vector {
    let output = portable::PortableVector::deserialize_11(v);

    SIMD128Vector::from_i32_array(portable::PortableVector::to_i32_array(output))
}

#[inline(always)]
fn serialize_12(v: SIMD128Vector) -> [u8; 12] {
    let input = portable::PortableVector::from_i32_array(SIMD128Vector::to_i32_array(v));

    portable::PortableVector::serialize_12(input)
}

#[inline(always)]
fn deserialize_12(v: &[u8]) -> SIMD128Vector {
    let output = portable::PortableVector::deserialize_12(v);

    SIMD128Vector::from_i32_array(portable::PortableVector::to_i32_array(output))
}

impl Operations for SIMD128Vector {
    fn ZERO() -> Self {
        ZERO()
    }

    fn to_i32_array(v: Self) -> [i32; 8] {
        to_i32_array(v)
    }

    fn from_i32_array(array: [i32; 8]) -> Self {
        from_i32_array(array)
    }

    fn add_constant(v: Self, c: i32) -> Self {
        add_constant(v, c)
    }

    fn add(lhs: Self, rhs: &Self) -> Self {
        add(lhs, rhs)
    }

    fn sub(lhs: Self, rhs: &Self) -> Self {
        sub(lhs, rhs)
    }

    fn multiply_by_constant(v: Self, c: i32) -> Self {
        multiply_by_constant(v, c)
    }

    fn bitwise_and_with_constant(v: Self, c: i32) -> Self {
        bitwise_and_with_constant(v, c)
    }

    fn shift_right<const SHIFT_BY: i32>(v: Self) -> Self {
        shift_right::<SHIFT_BY>(v)
    }

    fn shift_left<const SHIFT_BY: i32>(v: Self) -> Self {
        shift_left::<SHIFT_BY>(v)
    }

    fn cond_subtract_3329(v: Self) -> Self {
        cond_subtract_3329(v)
    }

    fn barrett_reduce(v: Self) -> Self {
        barrett_reduce(v)
    }

    fn montgomery_reduce(v: Self) -> Self {
        montgomery_reduce(v)
    }

    fn compress_1(v: Self) -> Self {
        compress_1(v)
    }

    fn compress(coefficient_bits: u8, v: Self) -> Self {
        compress(coefficient_bits, v)
    }

    fn ntt_layer_1_step(a: Self, zeta1: i32, zeta2: i32) -> Self {
        ntt_layer_1_step(a, zeta1, zeta2)
    }

    fn ntt_layer_2_step(a: Self, zeta: i32) -> Self {
        ntt_layer_2_step(a, zeta)
    }

    fn inv_ntt_layer_1_step(a: Self, zeta1: i32, zeta2: i32) -> Self {
        inv_ntt_layer_1_step(a, zeta1, zeta2)
    }

    fn inv_ntt_layer_2_step(a: Self, zeta: i32) -> Self {
        inv_ntt_layer_2_step(a, zeta)
    }

    fn ntt_multiply(lhs: &Self, rhs: &Self, zeta0: i32, zeta1: i32) -> Self {
        ntt_multiply(lhs, rhs, zeta0, zeta1)
    }

    fn serialize_1(a: Self) -> u8 {
        serialize_1(a)
    }

    fn deserialize_1(a: u8) -> Self {
        deserialize_1(a)
    }

    fn serialize_4(a: Self) -> [u8; 4] {
        serialize_4(a)
    }

    fn deserialize_4(a: &[u8]) -> Self {
        deserialize_4(a)
    }

    fn serialize_5(a: Self) -> [u8; 5] {
        serialize_5(a)
    }

    fn deserialize_5(a: &[u8]) -> Self {
        deserialize_5(a)
    }

    fn serialize_10(a: Self) -> [u8; 10] {
        serialize_10(a)
    }

    fn deserialize_10(a: &[u8]) -> Self {
        deserialize_10(a)
    }

    fn serialize_11(a: Self) -> [u8; 11] {
        serialize_11(a)
    }

    fn deserialize_11(a: &[u8]) -> Self {
        deserialize_11(a)
    }

    fn serialize_12(a: Self) -> [u8; 12] {
        serialize_12(a)
    }

    fn deserialize_12(a: &[u8]) -> Self {
        deserialize_12(a)
    }
}
