//! # Libcrux aarch64 optimized polynomials
//!
//! FIXME: This is kyber specific for now.

use core::arch::aarch64::*;

use libcrux_traits::{Operations, FIELD_MODULUS, INVERSE_OF_MODULUS_MOD_MONTGOMERY_R};

#[derive(Clone, Copy)]
pub struct SIMD128Vector {
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
    // This is what we are trying to do in portable:
    // let t = (i64::from(value) * BARRETT_MULTIPLIER) + (BARRETT_R >> 1);
    // let quotient = (t >> BARRETT_SHIFT) as i32;
    // let result = value - (quotient * FIELD_MODULUS);
    let adder = unsafe { vdupq_n_s64(33554432) };
    let low0 = unsafe { vmull_n_s32(vget_low_s32(v.low), BARRETT_MULTIPLIER) };
    let high0 = unsafe { vmull_n_s32(vget_low_s32(v.high), BARRETT_MULTIPLIER) };
    let low1 = unsafe { vmull_high_n_s32(v.low, BARRETT_MULTIPLIER) };
    let high1 = unsafe { vmull_high_n_s32(v.high, BARRETT_MULTIPLIER) };
    let low0 = unsafe { vshrq_n_s64(vaddq_s64(low0, adder), 26) };
    let low1 = unsafe { vshrq_n_s64(vaddq_s64(low1, adder), 26) };
    let high0 = unsafe { vshrq_n_s64(vaddq_s64(high0, adder), 26) };
    let high1 = unsafe { vshrq_n_s64(vaddq_s64(high1, adder), 26) };
    let low = unsafe { vcombine_s32(vmovn_s64(low0), vmovn_s64(low1)) };
    let high = unsafe { vcombine_s32(vmovn_s64(high0), vmovn_s64(high1)) };
    let low = unsafe { vmulq_n_s32(low, 3329) };
    let high = unsafe { vmulq_n_s32(high, 3329) };
    v.low = unsafe { vsubq_s32(v.low, low) };
    v.high = unsafe { vsubq_s32(v.high, high) };
    v
}

#[inline(always)]
fn montgomery_reduce_i32x2_t(v: int32x2_t) -> int32x2_t {
    // This is what we are trying to do in portable:
    // let t = get_n_least_significant_bits(MONTGOMERY_SHIFT, value as u32)
    //     * INVERSE_OF_MODULUS_MOD_MONTGOMERY_R;
    // let k = get_n_least_significant_bits(MONTGOMERY_SHIFT, t) as i16;
    // let k_times_modulus = (k as i32) * FIELD_MODULUS;
    // let c = k_times_modulus >> MONTGOMERY_SHIFT;
    // let value_high = value >> MONTGOMERY_SHIFT;
    // value_high - c

    let m = unsafe { vdup_n_s32(0x0000ffff) };
    let t0 = unsafe { vand_s32(v, m) };
    let t0 = unsafe { vmul_n_s32(t0, INVERSE_OF_MODULUS_MOD_MONTGOMERY_R as i32) };
    let t0 = unsafe { vreinterpret_s16_s32(t0) };
    let t0 = unsafe { vmull_n_s16(t0, FIELD_MODULUS as i16) };
    let c0 = unsafe { vshrq_n_s32::<16>(t0) };
    let c0 = unsafe { vmovn_s64(vreinterpretq_s64_s32(c0)) };
    let v0 = unsafe { vshr_n_s32::<16>(v) };
    let v = unsafe { vsub_s32(v0, c0) };
    v
}

#[inline(always)]
fn montgomery_reduce_i32x4_t(v: int32x4_t) -> int32x4_t {
    // This is what we are trying to do in portable:
    // let t = get_n_least_significant_bits(MONTGOMERY_SHIFT, value as u32)
    //     * INVERSE_OF_MODULUS_MOD_MONTGOMERY_R;
    // let k = get_n_least_significant_bits(MONTGOMERY_SHIFT, t) as i16;
    // let k_times_modulus = (k as i32) * FIELD_MODULUS;
    // let c = k_times_modulus >> MONTGOMERY_SHIFT;
    // let value_high = value >> MONTGOMERY_SHIFT;
    //value_high - c

    let t = unsafe {
        vreinterpretq_s16_s32(vmulq_n_s32(v, INVERSE_OF_MODULUS_MOD_MONTGOMERY_R as i32))
    };
    let c = unsafe { vreinterpretq_s32_s16(vqdmulhq_n_s16(t, FIELD_MODULUS as i16)) };
    let c = unsafe { vshrq_n_s32::<17>(vshlq_n_s32::<16>(c)) };
    let v = unsafe { vshrq_n_s32::<16>(v) };
    let v = unsafe { vsubq_s32(v, c) };
    v
}

#[inline(always)]
fn montgomery_reduce(mut v: SIMD128Vector) -> SIMD128Vector {
    // This is what we are trying to do in portable:
    // let t = get_n_least_significant_bits(MONTGOMERY_SHIFT, value as u32)
    //     * INVERSE_OF_MODULUS_MOD_MONTGOMERY_R;
    // let k = get_n_least_significant_bits(MONTGOMERY_SHIFT, t) as i16;
    // let k_times_modulus = (k as i32) * FIELD_MODULUS;
    // let c = k_times_modulus >> MONTGOMERY_SHIFT;
    // let value_high = value >> MONTGOMERY_SHIFT;
    //value_high - c

    let mixed = unsafe { vtrn1q_s16(vreinterpretq_s16_s32(v.low), vreinterpretq_s16_s32(v.high)) };
    let k = unsafe { vmulq_n_s16(mixed, INVERSE_OF_MODULUS_MOD_MONTGOMERY_R as i16) };
    let c = unsafe { vreinterpretq_s32_s16(vqdmulhq_n_s16(k, FIELD_MODULUS as i16)) };

    let c_low = unsafe { vshrq_n_s32::<17>(vshlq_n_s32::<16>(c)) };
    let c_high = unsafe { vshrq_n_s32::<17>(c) };
    let v_low = unsafe { vshrq_n_s32::<16>(v.low) };
    let v_high = unsafe { vshrq_n_s32::<16>(v.high) };

    v.low = unsafe { vsubq_s32(v_low, c_low) };
    v.high = unsafe { vsubq_s32(v_high, c_high) };
    v
}

#[inline(always)]
fn compress_1(mut v: SIMD128Vector) -> SIMD128Vector {
    // This is what we are trying to do in portable:
    // let shifted: i16 = 1664 - (fe as i16);
    // let mask = shifted >> 15;
    // let shifted_to_positive = mask ^ shifted;
    // let shifted_positive_in_range = shifted_to_positive - 832;
    // ((shifted_positive_in_range >> 15) & 1) as u8

    let mixed = unsafe { vtrn1q_s16(vreinterpretq_s16_s32(v.low), vreinterpretq_s16_s32(v.high)) };
    let half = unsafe { vdupq_n_s16(1664) };
    let quarter = unsafe { vdupq_n_s16(832) };
    let shifted = unsafe { vsubq_s16(half, mixed) };
    let mask = unsafe { vshrq_n_s16::<15>(shifted) };
    let shifted_to_positive = unsafe { veorq_s16(mask, shifted) };
    let shifted_positive_in_range = unsafe { vsubq_s16(shifted_to_positive, quarter) };
    let res = unsafe {
        vreinterpretq_s32_u16(vshrq_n_u16::<15>(vreinterpretq_u16_s16(
            shifted_positive_in_range,
        )))
    };
    let mask = unsafe { vdupq_n_s32(0xffff) };
    v.low = unsafe { vandq_s32(res, mask) };
    v.high = unsafe { vshrq_n_s32::<16>(res) };
    v
}

#[inline(always)]
fn mask_n_least_significant_bits(coefficient_bits: i32) -> i32 {
    match coefficient_bits {
        4 => 0x0f,
        5 => 0x1f,
        10 => 0x3ff,
        11 => 0x7ff,
        x => (1 << x) - 1,
    }
}

#[inline(always)]
fn compress<const COEFFICIENT_BITS: i32>(mut v: SIMD128Vector) -> SIMD128Vector {
    // This is what we are trying to do in portable:
    // let mut compressed = (fe as u64) << coefficient_bits;
    // compressed += 1664 as u64;
    // compressed *= 10_321_340;
    // compressed >>= 35;
    // get_n_least_significant_bits(coefficient_bits, compressed as u32) as FieldElement

    let half = unsafe { vdupq_n_s32(1664) };
    let low = unsafe { vshlq_n_s32::<COEFFICIENT_BITS>(v.low) };
    let high = unsafe { vshlq_n_s32::<COEFFICIENT_BITS>(v.high) };
    let low = unsafe { vaddq_s32(low, half) };
    let high = unsafe { vaddq_s32(high, half) };
    let low = unsafe { vqdmulhq_n_s32(low, 10_321_340) };
    let high = unsafe { vqdmulhq_n_s32(high, 10_321_340) };
    let low = unsafe { vshrq_n_s32::<4>(low) };
    let high = unsafe { vshrq_n_s32::<4>(high) };
    let mask = unsafe { vdupq_n_s32(mask_n_least_significant_bits(COEFFICIENT_BITS)) };
    v.low = unsafe { vandq_s32(low, mask) };
    v.high = unsafe { vandq_s32(high, mask) };
    v
}

#[inline(always)]
fn ntt_layer_1_step(mut v: SIMD128Vector, zeta1: i32, zeta2: i32) -> SIMD128Vector {
    // This is what we are trying to do, pointwise for every pair of elements:
    // let t = simd::Vector::montgomery_multiply_fe_by_fer(b, zeta_r);
    // b = simd::Vector::sub(a, &t);
    // a = simd::Vector::add(a, &t);

    let low0 = unsafe { vget_low_s32(v.low) };
    let low1 = unsafe { vget_high_s32(v.low) };
    let high0 = unsafe { vget_low_s32(v.high) };
    let high1 = unsafe { vget_high_s32(v.high) };
    let low_tmp = unsafe { vmul_n_s32(low1, zeta1) };
    let high_tmp = unsafe { vmul_n_s32(high1, zeta2) };
    let low_tmp = montgomery_reduce_i32x2_t(low_tmp);
    let high_tmp = montgomery_reduce_i32x2_t(high_tmp);
    let low1 = unsafe { vsub_s32(low0, low_tmp) };
    let high1 = unsafe { vsub_s32(high0, high_tmp) };
    let low0 = unsafe { vadd_s32(low0, low_tmp) };
    let high0 = unsafe { vadd_s32(high0, high_tmp) };
    v.low = unsafe { vcombine_s32(low0, low1) };
    v.high = unsafe { vcombine_s32(high0, high1) };
    v
}

#[inline(always)]
fn ntt_layer_2_step(mut v: SIMD128Vector, zeta: i32) -> SIMD128Vector {
    // This is what we are trying to do for every four elements:
    // let t = simd::Vector::montgomery_multiply_fe_by_fer(b, zeta_r);
    // b = simd::Vector::sub(a, &t);
    // a = simd::Vector::add(a, &t);

    let tmp = unsafe { vmulq_n_s32(v.high, zeta) };
    let tmp = montgomery_reduce_i32x4_t(tmp);
    v.high = unsafe { vsubq_s32(v.low, tmp) };
    v.low = unsafe { vaddq_s32(v.low, tmp) };
    v
}

#[inline(always)]
fn inv_ntt_layer_1_step(mut v: SIMD128Vector, zeta1: i32, zeta2: i32) -> SIMD128Vector {
    // This is what we are trying to do for every two elements:
    //let a_minus_b = simd::Vector::sub(b, &a);
    //a = simd::Vector::add(a, &b);
    //b = simd::Vector::montgomery_multiply_fe_by_fer(a_minus_b, zeta_r);
    //(a, b)

    let low0 = unsafe { vget_low_s32(v.low) };
    let low1 = unsafe { vget_high_s32(v.low) };
    let high0 = unsafe { vget_low_s32(v.high) };
    let high1 = unsafe { vget_high_s32(v.high) };
    let low_a_minus_b = unsafe { vsub_s32(low1, low0) };
    let high_a_minus_b = unsafe { vsub_s32(high1, high0) };
    let low0 = unsafe { vadd_s32(low0, low1) };
    let high0 = unsafe { vadd_s32(high0, high1) };
    let low_tmp = unsafe { vmul_n_s32(low_a_minus_b, zeta1) };
    let high_tmp = unsafe { vmul_n_s32(high_a_minus_b, zeta2) };
    let low1 = montgomery_reduce_i32x2_t(low_tmp);
    let high1 = montgomery_reduce_i32x2_t(high_tmp);
    v.low = unsafe { vcombine_s32(low0, low1) };
    v.high = unsafe { vcombine_s32(high0, high1) };
    v
}

#[inline(always)]
fn inv_ntt_layer_2_step(mut v: SIMD128Vector, zeta: i32) -> SIMD128Vector {
    // This is what we are trying to do for every four elements:
    //let a_minus_b = simd::Vector::sub(b, &a);
    //a = simd::Vector::add(a, &b);
    //b = simd::Vector::montgomery_multiply_fe_by_fer(a_minus_b, zeta_r);
    //(a, b)

    let tmp = unsafe { vsubq_s32(v.high, v.low) };
    v.low = unsafe { vaddq_s32(v.low, v.high) };
    let tmp = unsafe { vmulq_n_s32(tmp, zeta) };
    v.high = montgomery_reduce_i32x4_t(tmp);
    v
}

#[inline(always)]
fn ntt_multiply(lhs: &SIMD128Vector, rhs: &SIMD128Vector, zeta0: i32, zeta1: i32) -> SIMD128Vector {
    // This is what we are trying to do for pairs of two elements:
    // montgomery_reduce(a0 * b0 + montgomery_reduce(a1 * b1) * zeta),
    // montgomery_reduce(a0 * b1 + a1 * b0)

    let a0 = unsafe { vtrn1q_s32(lhs.low, lhs.high) }; // a0, a4, a2, a6
    let a1 = unsafe { vtrn2q_s32(lhs.low, lhs.high) }; // a1, a5, a3, a7
    let b0 = unsafe { vtrn1q_s32(rhs.low, rhs.high) }; // b0, b4, b2, b6
    let b1 = unsafe { vtrn2q_s32(rhs.low, rhs.high) }; // b1, b5, b3, b7

    let zetas: [i32; 4] = [zeta0, zeta1, -zeta0, -zeta1];
    let zeta = unsafe { vld1q_s32(zetas.as_ptr() as *const i32) };
    let a1b1 = unsafe { vmulq_s32(a1, b1) };
    let a0b0 = unsafe { vmulq_s32(a0, b0) };
    let a0b1 = unsafe { vmulq_s32(a0, b1) };

    let snd = unsafe { vmlaq_s32(a0b1, a1, b0) };
    let a1b1 = montgomery_reduce_i32x4_t(a1b1);

    let fst = unsafe { vmlaq_s32(a0b0, a1b1, zeta) };
    let fst = montgomery_reduce_i32x4_t(fst);
    let snd = montgomery_reduce_i32x4_t(snd);

    SIMD128Vector {
        low: unsafe { vtrn1q_s32(fst, snd) },
        high: unsafe { vtrn2q_s32(fst, snd) },
    }
}

#[inline(always)]
fn serialize_1(v: SIMD128Vector) -> u8 {
    let shifter0: [u32; 4] = [0, 1, 2, 3];
    let shifter1: [u32; 4] = [4, 5, 6, 7];
    let shift0 = unsafe { vld1q_s32(shifter0.as_ptr() as *const i32) };
    let shift1 = unsafe { vld1q_s32(shifter1.as_ptr() as *const i32) };
    let low = unsafe { vshlq_s32(v.low, shift0) };
    let high = unsafe { vshlq_s32(v.high, shift1) };
    let low = unsafe { vaddvq_s32(low) };
    let high = unsafe { vaddvq_s32(high) };
    (low | high) as u8
}

#[inline(always)]
fn deserialize_1(a: u8) -> SIMD128Vector {
    let dup = unsafe { vdupq_n_s32(a as i32) };
    let shifter0: [i32; 4] = [0, -1, -2, -3];
    let shifter1: [i32; 4] = [-4, -5, -6, -7];
    let shift0 = unsafe { vld1q_s32(shifter0.as_ptr() as *const i32) };
    let shift1 = unsafe { vld1q_s32(shifter1.as_ptr() as *const i32) };
    let low = unsafe { vshlq_s32(dup, shift0) };
    let high = unsafe { vshlq_s32(dup, shift1) };
    SIMD128Vector {
        low: unsafe { vandq_s32(low, vdupq_n_s32(1)) },
        high: unsafe { vandq_s32(high, vdupq_n_s32(1)) },
    }
}

#[inline(always)]
fn serialize_4(v: SIMD128Vector) -> [u8; 4] {
    let shifter0: [i32; 4] = [0, 4, 8, 12];
    let shifter1: [i32; 4] = [16, 20, 24, 28];
    let shift0 = unsafe { vld1q_s32(shifter0.as_ptr() as *const i32) };
    let shift1 = unsafe { vld1q_s32(shifter1.as_ptr() as *const i32) };
    let lowt = unsafe { vshlq_s32(v.low, shift0) };
    let hight = unsafe { vshlq_s32(v.high, shift1) };
    let low = unsafe { vaddvq_s32(lowt) };
    let high = unsafe { vaddvq_s32(hight) };
    (low | high).to_le_bytes()
}

#[inline(always)]
fn deserialize_4(v: &[u8]) -> SIMD128Vector {
    let input = u32::from_le_bytes(v.try_into().unwrap());
    let mut low = [0i32; 4];
    let mut high = [0i32; 4];
    low[0] = (input & 0x0f) as i32;
    low[1] = ((input >> 4) & 0x0f) as i32;
    low[2] = ((input >> 8) & 0x0f) as i32;
    low[3] = ((input >> 12) & 0x0f) as i32;
    high[0] = ((input >> 16) & 0x0f) as i32;
    high[1] = ((input >> 20) & 0x0f) as i32;
    high[2] = ((input >> 24) & 0x0f) as i32;
    high[3] = ((input >> 28) & 0x0f) as i32;
    SIMD128Vector {
        low: unsafe { vld1q_s32(low.as_ptr() as *const i32) },
        high: unsafe { vld1q_s32(high.as_ptr() as *const i32) },
    }
}

#[inline(always)]
fn serialize_5(v: SIMD128Vector) -> [u8; 5] {
    let lowt = unsafe { vtrn1q_s32(v.low, v.high) }; // a0, a4, a2, a6
    let hight = unsafe { vtrn2q_s32(v.low, v.high) }; // a1, a5, a3, a7
    let mixt = unsafe { vsliq_n_s32::<5>(lowt, hight) }; // a1a0, a5a4, a3a2, a7a6

    let lowt = unsafe { vmovl_s32(vget_low_s32(mixt)) }; // a1a0, a5a4
    let hight = unsafe { vmovl_s32(vget_high_s32(mixt)) }; // a3a2, a7a6
    let mixt = unsafe { vsliq_n_s64::<10>(lowt, hight) }; // a3a2a1a0, a7a6a5a4
    let mut result2 = [0i64; 2];
    unsafe { vst1q_s64(result2.as_mut_ptr() as *mut i64, mixt) };

    let result_i64 = result2[0] | (result2[1] << 20);
    let mut result = [0u8; 5];
    result.copy_from_slice(&result_i64.to_le_bytes()[0..5]);
    result
}

#[inline(always)]
fn deserialize_5(v: &[u8]) -> SIMD128Vector {
    let mut input = [0u8; 8];
    input[0..5].copy_from_slice(&v[0..5]);
    let input = u64::from_le_bytes(input);

    let mut low = [0i32; 4];
    let mut high = [0i32; 4];

    low[0] = (input & 0x1F) as i32;
    low[1] = ((input >> 5) & 0x1F) as i32;
    low[2] = ((input >> 10) & 0x1F) as i32;
    low[3] = ((input >> 15) & 0x1F) as i32;
    high[0] = ((input >> 20) & 0x1F) as i32;
    high[1] = ((input >> 25) & 0x1F) as i32;
    high[2] = ((input >> 30) & 0x1F) as i32;
    high[3] = ((input >> 35) & 0x1F) as i32;

    SIMD128Vector {
        low: unsafe { vld1q_s32(low.as_ptr() as *const i32) },
        high: unsafe { vld1q_s32(high.as_ptr() as *const i32) },
    }
}

#[inline(always)]
fn serialize_10(v: SIMD128Vector) -> [u8; 10] {
    let lowt = unsafe { vtrn1q_s32(v.low, v.high) }; // a0, a4, a2, a6
    let hight = unsafe { vtrn2q_s32(v.low, v.high) }; // a1, a5, a3, a7
    let mixt = unsafe { vsliq_n_s32::<10>(lowt, hight) }; // a1a0, a5a4, a3a2, a7a6

    let lowt = unsafe { vmovl_s32(vget_low_s32(mixt)) }; // a1a0, a5a4
    let hight = unsafe { vmovl_s32(vget_high_s32(mixt)) }; // a3a2, a7a6
    let mixt = unsafe { vsliq_n_s64::<20>(lowt, hight) };

    let index_arr: [u8; 16] = [0, 1, 2, 3, 4, 8, 9, 10, 11, 12, 10, 11, 12, 13, 14, 15];
    let index = unsafe { vld1q_u8(index_arr.as_ptr() as *const u8) };
    let mixt = unsafe { vqtbl1q_u8(vreinterpretq_u8_s64(mixt), index) };

    let mut result16 = [0u8; 16];
    unsafe { vst1q_u8(result16.as_mut_ptr() as *mut u8, mixt) };
    let mut result10 = [0u8; 10];
    result10.copy_from_slice(&result16[0..10]);
    result10
}

#[inline(always)]
fn deserialize_10(v: &[u8]) -> SIMD128Vector {
    let mut input0 = [0u8; 8];
    let mut input1 = [0u8; 8];
    input0[0..5].copy_from_slice(&v[0..5]);
    input1[0..5].copy_from_slice(&v[5..10]);
    let input0 = u64::from_le_bytes(input0);
    let input1 = u64::from_le_bytes(input1);
    let mut low = [0i32; 4];
    let mut high = [0i32; 4];
    low[0] = (input0 & 0x3ff) as i32;
    low[1] = ((input0 & 0xffc00) >> 10) as i32;
    low[2] = ((input0 & 0x3ff00000) >> 20) as i32;
    low[3] = ((input0 & 0xffc0000000) >> 30) as i32;
    high[0] = (input1 & 0x3ff) as i32;
    high[1] = ((input1 & 0xffc00) >> 10) as i32;
    high[2] = ((input1 & 0x3ff00000) >> 20) as i32;
    high[3] = ((input1 & 0xffc0000000) >> 30) as i32;
    SIMD128Vector {
        low: unsafe { vld1q_s32(low.as_ptr() as *const i32) },
        high: unsafe { vld1q_s32(high.as_ptr() as *const i32) },
    }
}

#[inline(always)]
fn serialize_11(v: SIMD128Vector) -> [u8; 11] {
    let input = to_i32_array(v);
    let mut result = [0u8; 11];
    result[0] = input[0] as u8; // 3 left in 0
    result[1] = ((input[0] >> 8) | (input[1] << 3)) as u8; // 6 left in 1
    result[2] = ((input[1] >> 5) | (input[2] << 6)) as u8; // 9 left in 2
    result[3] = (input[2] >> 2) as u8; // 1 left in 2
    result[4] = ((input[2] >> 10) | (input[3] << 1)) as u8; // 4 left in 3
    result[5] = ((input[3] >> 7) | (input[4] << 4)) as u8; // 7 left in 4
    result[6] = ((input[4] >> 4) | (input[5] << 7)) as u8; // 10 left in 5
    result[7] = (input[5] >> 1) as u8; // 2 left in 5
    result[8] = ((input[5] >> 9) | (input[6] << 2)) as u8; // 5 left in 6
    result[9] = ((input[6] >> 6) | (input[7] << 5)) as u8; // 8 left in 7
    result[10] = (input[7] >> 3) as u8;
    result
}

#[inline(always)]
fn deserialize_11(v: &[u8]) -> SIMD128Vector {
    let mut input0 = [0u8; 8];
    let mut input1 = [0u8; 8];
    input0[0..6].copy_from_slice(&v[0..6]);
    input1[0..6].copy_from_slice(&v[5..11]);
    let input0 = u64::from_le_bytes(input0);
    let input1 = u64::from_le_bytes(input1);

    let mut low = [0i32; 4];
    let mut high = [0i32; 4];

    low[0] = (input0 & 0x7FF) as i32;
    low[1] = ((input0 >> 11) & 0x7FF) as i32;
    low[2] = ((input0 >> 22) & 0x7FF) as i32;
    low[3] = ((input0 >> 33) & 0x7FF) as i32;
    high[0] = ((input1 >> 4) & 0x7FF) as i32;
    high[1] = ((input1 >> 15) & 0x7FF) as i32;
    high[2] = ((input1 >> 26) & 0x7FF) as i32;
    high[3] = ((input1 >> 37) & 0x7FF) as i32;

    SIMD128Vector {
        low: unsafe { vld1q_s32(low.as_ptr() as *const i32) },
        high: unsafe { vld1q_s32(high.as_ptr() as *const i32) },
    }
}

#[inline(always)]
fn serialize_12(v: SIMD128Vector) -> [u8; 12] {
    let lowt = unsafe { vtrn1q_s32(v.low, v.high) }; // a0, a4, a2, a6
    let hight = unsafe { vtrn2q_s32(v.low, v.high) }; // a1, a5, a3, a7
    let mixt = unsafe { vsliq_n_s32::<12>(lowt, hight) }; // a1a0, a5a4, a3a2, a7a6

    let index_arr: [u8; 16] = [0, 1, 2, 8, 9, 10, 4, 5, 6, 12, 13, 14, 12, 13, 14, 15];
    let index = unsafe { vld1q_u8(index_arr.as_ptr() as *const u8) };
    let mixt = unsafe { vqtbl1q_u8(vreinterpretq_u8_s32(mixt), index) };

    let mut result16 = [0u8; 16];
    unsafe { vst1q_u8(result16.as_mut_ptr() as *mut u8, mixt) };
    let mut result12 = [0u8; 12];
    result12.copy_from_slice(&result16[0..12]);
    result12
}

#[inline(always)]
fn deserialize_12(v: &[u8]) -> SIMD128Vector {
    let mut input0 = [0u8; 8];
    let mut input1 = [0u8; 8];
    input0[0..6].copy_from_slice(&v[0..6]);
    input1[0..6].copy_from_slice(&v[6..12]);
    let input0 = u64::from_le_bytes(input0);
    let input1 = u64::from_le_bytes(input1);
    let mut low = [0i32; 4];
    let mut high = [0i32; 4];
    low[0] = (input0 & 0xfff) as i32;
    low[1] = ((input0 & 0xfff000) >> 12) as i32;
    low[2] = ((input0 & 0xfff000000) >> 24) as i32;
    low[3] = ((input0 & 0xfff000000000) >> 36) as i32;
    high[0] = (input1 & 0xfff) as i32;
    high[1] = ((input1 & 0xfff000) >> 12) as i32;
    high[2] = ((input1 & 0xfff000000) >> 24) as i32;
    high[3] = ((input1 & 0xfff000000000) >> 36) as i32;
    SIMD128Vector {
        low: unsafe { vld1q_s32(low.as_mut_ptr() as *mut i32) },
        high: unsafe { vld1q_s32(high.as_mut_ptr() as *mut i32) },
    }
}

impl Operations for SIMD128Vector {
    #[inline(always)]
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

    fn compress<const COEFFICIENT_BITS: i32>(v: Self) -> Self {
        compress::<COEFFICIENT_BITS>(v)
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
