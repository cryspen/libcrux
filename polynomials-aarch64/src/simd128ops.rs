#![forbid(unsafe_code)]

use crate::neon::*;
use libcrux_traits::{FIELD_MODULUS, INVERSE_OF_MODULUS_MOD_MONTGOMERY_R};

#[derive(Clone, Copy)]
pub struct SIMD128Vector {
    pub low: int16x8_t,
    pub high: int16x8_t,
}

#[allow(non_snake_case)]
#[inline(always)]
pub(crate) fn ZERO() -> SIMD128Vector {
    SIMD128Vector {
        low: _vdupq_n_s16(0),
        high: _vdupq_n_s16(0),
    }
}

#[inline(always)]
pub(crate) fn to_i16_array(v: SIMD128Vector) -> [i16; 16] {
    let mut out = [0i16; 16];
    _vst1q_s16(&mut out[0..8], v.low);
    _vst1q_s16(&mut out[8..16], v.high);
    out
}

#[inline(always)]
pub(crate) fn from_i16_array(array: [i16; 16]) -> SIMD128Vector {
    SIMD128Vector {
        low: _vld1q_s16(&array[0..8]),
        high: _vld1q_s16(&array[8..16]),
    }
}

#[inline(always)]
pub(crate) fn add(mut lhs: SIMD128Vector, rhs: &SIMD128Vector) -> SIMD128Vector {
    lhs.low = _vaddq_s16(lhs.low, rhs.low);
    lhs.high = _vaddq_s16(lhs.high, rhs.high);
    lhs
}

#[inline(always)]
pub(crate) fn sub(mut lhs: SIMD128Vector, rhs: &SIMD128Vector) -> SIMD128Vector {
    lhs.low = _vsubq_s16(lhs.low, rhs.low);
    lhs.high = _vsubq_s16(lhs.high, rhs.high);
    lhs
}

#[inline(always)]
pub(crate) fn multiply_by_constant(mut v: SIMD128Vector, c: i16) -> SIMD128Vector {
    v.low = _vmulq_n_s16(v.low, c);
    v.high = _vmulq_n_s16(v.high, c);
    v
}

#[inline(always)]
pub(crate) fn bitwise_and_with_constant(mut v: SIMD128Vector, c: i16) -> SIMD128Vector {
    let c = _vdupq_n_s16(c);
    v.low = _vandq_s16(v.low, c);
    v.high = _vandq_s16(v.high, c);
    v
}

#[inline(always)]
pub(crate) fn shift_right<const SHIFT_BY: i32>(mut v: SIMD128Vector) -> SIMD128Vector {
    // Should find special cases of this
    // e.g when doing a right shift just to propagate signed bits, use vclezq_s32 instead
    v.low = _vshrq_n_s16::<SHIFT_BY>(v.low);
    v.high = _vshrq_n_s16::<SHIFT_BY>(v.high);
    v
}

#[inline(always)]
pub(crate) fn shift_left<const SHIFT_BY: i32>(mut lhs: SIMD128Vector) -> SIMD128Vector {
    lhs.low = _vshlq_n_s16::<SHIFT_BY>(lhs.low);
    lhs.high = _vshlq_n_s16::<SHIFT_BY>(lhs.high);
    lhs
}

#[inline(always)]
pub(crate) fn cond_subtract_3329(mut v: SIMD128Vector) -> SIMD128Vector {
    let c = _vdupq_n_s16(3329);
    let m0 = _vcgeq_s16(v.low, c);
    let m1 = _vcgeq_s16(v.high, c);
    let c0 = _vandq_s16(c, _vreinterpretq_s16_u16(m0));
    let c1 = _vandq_s16(c, _vreinterpretq_s16_u16(m1));
    v.low = _vsubq_s16(v.low, c0);
    v.high = _vsubq_s16(v.high, c1);
    v
}

const BARRETT_MULTIPLIER: i16 = 20159;

#[inline(always)]
fn barrett_reduce_int16x8_t(v: int16x8_t) -> int16x8_t {
    //let pv = crate::simd::portable::from_i16_array(to_i16_array(v));
    //from_i16_array(crate::simd::portable::to_i16_array(crate::simd::portable::barrett_reduce(pv)))

    // This is what we are trying to do in portable:
    // let t = (value as i16 * BARRETT_MULTIPLIER) + (BARRETT_R >> 1);
    // let quotient = (t >> BARRETT_SHIFT) as i16;
    // let result = value - (quotient * FIELD_MODULUS);

    let adder = _vdupq_n_s16(1024);
    let vec = _vqdmulhq_n_s16(v, BARRETT_MULTIPLIER as i16);
    let vec = _vaddq_s16(vec, adder);
    let quotient = _vshrq_n_s16::<11>(vec);
    let sub = _vmulq_n_s16(quotient, FIELD_MODULUS);
    _vsubq_s16(v, sub)
}

#[inline(always)]
pub(crate) fn barrett_reduce(mut v: SIMD128Vector) -> SIMD128Vector {
    //let pv = crate::simd::portable::from_i16_array(to_i16_array(v));
    //from_i16_array(crate::simd::portable::to_i16_array(crate::simd::portable::barrett_reduce(pv)))

    // This is what we are trying to do in portable:
    // let t = (value as i16 * BARRETT_MULTIPLIER) + (BARRETT_R >> 1);
    // let quotient = (t >> BARRETT_SHIFT) as i16;
    // let result = value - (quotient * FIELD_MODULUS);

    v.low = barrett_reduce_int16x8_t(v.low);
    v.high = barrett_reduce_int16x8_t(v.high);
    v
}

#[inline(always)]
fn montgomery_reduce_int16x8_t(low: int16x8_t, high: int16x8_t) -> int16x8_t {
    // This is what we are trying to do in portable:
    // let k = low as i16 * INVERSE_OF_MODULUS_MOD_MONTGOMERY_R;
    // let k_times_modulus = (k as i16 as i16) * (FIELD_MODULUS as i16);
    // let c = (k_times_modulus >> MONTGOMERY_SHIFT) as i16;
    // high - c

    let k = _vreinterpretq_s16_u16(_vmulq_n_u16(
        _vreinterpretq_u16_s16(low),
        INVERSE_OF_MODULUS_MOD_MONTGOMERY_R as u16,
    ));
    let c = _vshrq_n_s16::<1>(_vqdmulhq_n_s16(k, FIELD_MODULUS as i16));
    _vsubq_s16(high, c)
}

#[inline(always)]
fn montgomery_multiply_by_constant_int16x8_t(v: int16x8_t, c: i16) -> int16x8_t {
    // This is what we are trying to do in portable:
    // let value = v as i16 * c
    // let k = (value as i16) as i16 * INVERSE_OF_MODULUS_MOD_MONTGOMERY_R;
    // let k_times_modulus = (k as i16 as i16) * (FIELD_MODULUS as i16);
    // let c = (k_times_modulus >> MONTGOMERY_SHIFT) as i16;
    // let value_high = (value >> MONTGOMERY_SHIFT) as i16;
    // value_high - c

    let v_low = _vmulq_n_s16(v, c);
    let v_high = _vshrq_n_s16::<1>(_vqdmulhq_n_s16(v, c));
    montgomery_reduce_int16x8_t(v_low, v_high)
}

#[inline(always)]
fn montgomery_multiply_int16x8_t(v: int16x8_t, c: int16x8_t) -> int16x8_t {
    // This is what we are trying to do in portable:
    // let value = v as i16 * c
    // let k = (value as i16) as i16 * INVERSE_OF_MODULUS_MOD_MONTGOMERY_R;
    // let k_times_modulus = (k as i16 as i16) * (FIELD_MODULUS as i16);
    // let c = (k_times_modulus >> MONTGOMERY_SHIFT) as i16;
    // let value_high = (value >> MONTGOMERY_SHIFT) as i16;
    // value_high - c

    let v_low = _vmulq_s16(v, c);
    let v_high = _vshrq_n_s16::<1>(_vqdmulhq_s16(v, c));
    montgomery_reduce_int16x8_t(v_low, v_high)
}

#[inline(always)]
pub(crate) fn montgomery_multiply_by_constant(mut v: SIMD128Vector, c: i16) -> SIMD128Vector {
    v.low = montgomery_multiply_by_constant_int16x8_t(v.low, c);
    v.high = montgomery_multiply_by_constant_int16x8_t(v.high, c);
    v
}

#[inline(always)]
pub(crate) fn compress_1(mut v: SIMD128Vector) -> SIMD128Vector {
    // This is what we are trying to do in portable:
    // let shifted: i16 = 1664 - (fe as i16);
    // let mask = shifted >> 15;
    // let shifted_to_positive = mask ^ shifted;
    // let shifted_positive_in_range = shifted_to_positive - 832;
    // ((shifted_positive_in_range >> 15) & 1) as u8

    let half = _vdupq_n_s16(1664);
    let quarter = _vdupq_n_s16(832);

    let shifted = _vsubq_s16(half, v.low);
    let mask = _vshrq_n_s16::<15>(shifted);
    let shifted_to_positive = _veorq_s16(mask, shifted);
    let shifted_positive_in_range = _vsubq_s16(shifted_to_positive, quarter);
    v.low = _vreinterpretq_s16_u16(_vshrq_n_u16::<15>(_vreinterpretq_u16_s16(
        shifted_positive_in_range,
    )));

    let shifted = _vsubq_s16(half, v.high);
    let mask = _vshrq_n_s16::<15>(shifted);
    let shifted_to_positive = _veorq_s16(mask, shifted);
    let shifted_positive_in_range = _vsubq_s16(shifted_to_positive, quarter);
    v.high = _vreinterpretq_s16_u16(_vshrq_n_u16::<15>(_vreinterpretq_u16_s16(
        shifted_positive_in_range,
    )));

    v
}

#[inline(always)]
fn mask_n_least_significant_bits(coefficient_bits: i16) -> i16 {
    match coefficient_bits {
        4 => 0x0f,
        5 => 0x1f,
        10 => 0x3ff,
        11 => 0x7ff,
        x => (1 << x) - 1,
    }
}

#[inline(always)]
fn compress_int32x4_t<const COEFFICIENT_BITS: i32>(v: uint32x4_t) -> uint32x4_t {
    // This is what we are trying to do in portable:
    // let mut compressed = (fe as u64) << coefficient_bits;
    // compressed += 1664 as u64;
    // compressed *= 10_321_340;
    // compressed >>= 35;
    // get_n_least_significant_bits(coefficient_bits, compressed as u32) as FieldElement
    let half = _vdupq_n_u32(1664);
    let compressed = _vshlq_n_u32::<COEFFICIENT_BITS>(v);
    let compressed = _vaddq_u32(compressed, half);
    let compressed = _vreinterpretq_u32_s32(_vqdmulhq_n_s32(
        _vreinterpretq_s32_u32(compressed),
        10_321_340,
    ));
    let compressed = _vshrq_n_u32::<4>(compressed);
    compressed
}

#[inline(always)]
pub(crate) fn compress<const COEFFICIENT_BITS: i32>(mut v: SIMD128Vector) -> SIMD128Vector {
    // This is what we are trying to do in portable:
    // let mut compressed = (fe as u64) << coefficient_bits;
    // compressed += 1664 as u64;
    // compressed *= 10_321_340;
    // compressed >>= 35;
    // get_n_least_significant_bits(coefficient_bits, compressed as u32) as FieldElement

    let mask = _vdupq_n_s16(mask_n_least_significant_bits(COEFFICIENT_BITS as i16));
    let mask16 = _vdupq_n_u32(0xffff);

    let low0 = _vandq_u32(_vreinterpretq_u32_s16(v.low), mask16); //a0, a2, a4, a6
    let low1 = _vshrq_n_u32::<16>(_vreinterpretq_u32_s16(v.low)); //a1, a3, a5, a7
    let high0 = _vandq_u32(_vreinterpretq_u32_s16(v.high), mask16); //a0, a2, a4, a6
    let high1 = _vshrq_n_u32::<16>(_vreinterpretq_u32_s16(v.high)); //a1, a3, a5, a7

    let low0 = compress_int32x4_t::<COEFFICIENT_BITS>(low0);
    let low1 = compress_int32x4_t::<COEFFICIENT_BITS>(low1);
    let high0 = compress_int32x4_t::<COEFFICIENT_BITS>(high0);
    let high1 = compress_int32x4_t::<COEFFICIENT_BITS>(high1);

    let low = _vtrn1q_s16(_vreinterpretq_s16_u32(low0), _vreinterpretq_s16_u32(low1));
    let high = _vtrn1q_s16(_vreinterpretq_s16_u32(high0), _vreinterpretq_s16_u32(high1));

    v.low = _vandq_s16(low, mask);
    v.high = _vandq_s16(high, mask);
    v
}

#[inline(always)]
fn decompress_uint32x4_t<const COEFFICIENT_BITS: i32>(v: uint32x4_t) -> uint32x4_t {
    let coeff = _vdupq_n_u32(1 << (COEFFICIENT_BITS - 1));
    let decompressed = _vmulq_n_u32(v, FIELD_MODULUS as u32);
    let decompressed = _vaddq_u32(decompressed, coeff);
    let decompressed = _vshrq_n_u32::<COEFFICIENT_BITS>(decompressed);

    decompressed
}

#[inline(always)]
pub(crate) fn decompress_ciphertext_coefficient<const COEFFICIENT_BITS: i32>(mut v: SIMD128Vector) -> SIMD128Vector {
    let mask16 = _vdupq_n_u32(0xffff);
    let low0 = _vandq_u32(_vreinterpretq_u32_s16(v.low), mask16);
    let low1 = _vshrq_n_u32::<16>(_vreinterpretq_u32_s16(v.low));
    let high0 = _vandq_u32(_vreinterpretq_u32_s16(v.high), mask16);
    let high1 = _vshrq_n_u32::<16>(_vreinterpretq_u32_s16(v.high));

    let low0 = decompress_uint32x4_t::<COEFFICIENT_BITS>(low0);
    let low1 = decompress_uint32x4_t::<COEFFICIENT_BITS>(low1);
    let high0 = decompress_uint32x4_t::<COEFFICIENT_BITS>(high0);
    let high1 = decompress_uint32x4_t::<COEFFICIENT_BITS>(high1);

    v.low = _vtrn1q_s16(_vreinterpretq_s16_u32(low0), _vreinterpretq_s16_u32(low1));
    v.high = _vtrn1q_s16(_vreinterpretq_s16_u32(high0), _vreinterpretq_s16_u32(high1));
    v
}

#[inline(always)]
pub(crate) fn ntt_layer_1_step(
    mut v: SIMD128Vector,
    zeta1: i16,
    zeta2: i16,
    zeta3: i16,
    zeta4: i16,
) -> SIMD128Vector {
    // This is what we are trying to do, pointwise for every pair of elements:
    // let t = simd::Vector::montgomery_multiply_fe_by_fer(b, zeta_r);
    // b = simd::Vector::sub(a, &t);
    // a = simd::Vector::add(a, &t);

    let zetas = [zeta1, zeta1, zeta3, zeta3, zeta2, zeta2, zeta4, zeta4];
    let zeta = _vld1q_s16(&zetas);
    let dup_a = _vreinterpretq_s16_s32(_vtrn1q_s32(
        _vreinterpretq_s32_s16(v.low),
        _vreinterpretq_s32_s16(v.high),
    ));
    let dup_b = _vreinterpretq_s16_s32(_vtrn2q_s32(
        _vreinterpretq_s32_s16(v.low),
        _vreinterpretq_s32_s16(v.high),
    ));
    let t = montgomery_multiply_int16x8_t(dup_b, zeta);
    let b = _vsubq_s16(dup_a, t);
    let a = _vaddq_s16(dup_a, t);

    v.low = _vreinterpretq_s16_s32(_vtrn1q_s32(
        _vreinterpretq_s32_s16(a),
        _vreinterpretq_s32_s16(b),
    ));
    v.high = _vreinterpretq_s16_s32(_vtrn2q_s32(
        _vreinterpretq_s32_s16(a),
        _vreinterpretq_s32_s16(b),
    ));
    v
}

#[inline(always)]
pub(crate) fn ntt_layer_2_step(mut v: SIMD128Vector, zeta1: i16, zeta2: i16) -> SIMD128Vector {
    // This is what we are trying to do for every four elements:
    // let t = simd::Vector::montgomery_multiply_fe_by_fer(b, zeta_r);
    // b = simd::Vector::sub(a, &t);
    // a = simd::Vector::add(a, &t);

    let zetas = [zeta1, zeta1, zeta1, zeta1, zeta2, zeta2, zeta2, zeta2];
    let zeta = _vld1q_s16(&zetas);
    let dup_a = _vreinterpretq_s16_s64(_vtrn1q_s64(
        _vreinterpretq_s64_s16(v.low),
        _vreinterpretq_s64_s16(v.high),
    ));
    let dup_b = _vreinterpretq_s16_s64(_vtrn2q_s64(
        _vreinterpretq_s64_s16(v.low),
        _vreinterpretq_s64_s16(v.high),
    ));
    let t = montgomery_multiply_int16x8_t(dup_b, zeta);
    let b = _vsubq_s16(dup_a, t);
    let a = _vaddq_s16(dup_a, t);

    v.low = _vreinterpretq_s16_s64(_vtrn1q_s64(
        _vreinterpretq_s64_s16(a),
        _vreinterpretq_s64_s16(b),
    ));
    v.high = _vreinterpretq_s16_s64(_vtrn2q_s64(
        _vreinterpretq_s64_s16(a),
        _vreinterpretq_s64_s16(b),
    ));
    v
}

#[inline(always)]
pub(crate) fn ntt_layer_3_step(mut v: SIMD128Vector, zeta: i16) -> SIMD128Vector {
    // This is what we are trying to do for every four elements:
    // let t = simd::Vector::montgomery_multiply_fe_by_fer(b, zeta_r);
    // b = simd::Vector::sub(a, &t);
    // a = simd::Vector::add(a, &t);

    let zeta = _vdupq_n_s16(zeta);
    let t = montgomery_multiply_int16x8_t(v.high, zeta);
    v.high = _vsubq_s16(v.low, t);
    v.low = _vaddq_s16(v.low, t);
    v
}

#[inline(always)]
pub(crate) fn inv_ntt_layer_1_step(
    mut v: SIMD128Vector,
    zeta1: i16,
    zeta2: i16,
    zeta3: i16,
    zeta4: i16,
) -> SIMD128Vector {
    // This is what we are trying to do for every two elements:
    //let a_minus_b = simd::Vector::sub(b, &a);
    //a = simd::Vector::add(a, &b);
    //b = simd::Vector::montgomery_multiply_fe_by_fer(a_minus_b, zeta_r);
    //(a, b)

    let zetas = [zeta1, zeta1, zeta3, zeta3, zeta2, zeta2, zeta4, zeta4];
    let zeta = _vld1q_s16(&zetas);

    let a = _vreinterpretq_s16_s32(_vtrn1q_s32(
        _vreinterpretq_s32_s16(v.low),
        _vreinterpretq_s32_s16(v.high),
    ));
    let b = _vreinterpretq_s16_s32(_vtrn2q_s32(
        _vreinterpretq_s32_s16(v.low),
        _vreinterpretq_s32_s16(v.high),
    ));

    let b_minus_a = _vsubq_s16(b, a);
    let a = _vaddq_s16(a, b);
    let a = barrett_reduce_int16x8_t(a);
    let b = montgomery_multiply_int16x8_t(b_minus_a, zeta);

    v.low = _vreinterpretq_s16_s32(_vtrn1q_s32(
        _vreinterpretq_s32_s16(a),
        _vreinterpretq_s32_s16(b),
    ));
    v.high = _vreinterpretq_s16_s32(_vtrn2q_s32(
        _vreinterpretq_s32_s16(a),
        _vreinterpretq_s32_s16(b),
    ));
    v
}

#[inline(always)]
pub(crate) fn inv_ntt_layer_2_step(mut v: SIMD128Vector, zeta1: i16, zeta2: i16) -> SIMD128Vector {
    // This is what we are trying to do for every four elements:
    //let a_minus_b = simd::Vector::sub(b, &a);
    //a = simd::Vector::add(a, &b);
    //b = simd::Vector::montgomery_multiply_fe_by_fer(a_minus_b, zeta_r);
    //(a, b)

    let zetas = [zeta1, zeta1, zeta1, zeta1, zeta2, zeta2, zeta2, zeta2];
    let zeta = _vld1q_s16(&zetas);

    let a = _vreinterpretq_s16_s64(_vtrn1q_s64(
        _vreinterpretq_s64_s16(v.low),
        _vreinterpretq_s64_s16(v.high),
    ));
    let b = _vreinterpretq_s16_s64(_vtrn2q_s64(
        _vreinterpretq_s64_s16(v.low),
        _vreinterpretq_s64_s16(v.high),
    ));

    let b_minus_a = _vsubq_s16(b, a);
    let a = _vaddq_s16(a, b);
    let b = montgomery_multiply_int16x8_t(b_minus_a, zeta);

    v.low = _vreinterpretq_s16_s64(_vtrn1q_s64(
        _vreinterpretq_s64_s16(a),
        _vreinterpretq_s64_s16(b),
    ));
    v.high = _vreinterpretq_s16_s64(_vtrn2q_s64(
        _vreinterpretq_s64_s16(a),
        _vreinterpretq_s64_s16(b),
    ));
    v
}

#[inline(always)]
pub(crate) fn inv_ntt_layer_3_step(mut v: SIMD128Vector, zeta: i16) -> SIMD128Vector {
    // This is what we are trying to do for every four elements:
    //let a_minus_b = simd::Vector::sub(b, &a);
    //a = simd::Vector::add(a, &b);
    //b = simd::Vector::montgomery_multiply_fe_by_fer(a_minus_b, zeta_r);
    //(a, b)

    let zeta = _vdupq_n_s16(zeta);
    let b_minus_a = _vsubq_s16(v.high, v.low);
    v.low = _vaddq_s16(v.low, v.high);
    v.high = montgomery_multiply_int16x8_t(b_minus_a, zeta);
    v
}

#[inline(always)]
pub(crate) fn ntt_multiply(
    lhs: &SIMD128Vector,
    rhs: &SIMD128Vector,
    zeta1: i16,
    zeta2: i16,
    zeta3: i16,
    zeta4: i16,
) -> SIMD128Vector {
    // This is what we are trying to do for pairs of two elements:
    // montgomery_reduce(a0 * b0 + montgomery_reduce(a1 * b1) * zeta),
    // montgomery_reduce(a0 * b1 + a1 * b0)
    //let lhsp = crate::simd::portable::from_i16_array(to_i16_array(lhs.clone()));
    //let rhsp = crate::simd::portable::from_i16_array(to_i16_array(rhs.clone()));
    //let mulp = crate::simd::portable::ntt_multiply(&lhsp,&rhsp,zeta0,zeta1);
    //from_i16_array(crate::simd::portable::to_i16_array(mulp))

    let zetas: [i16; 8] = [zeta1, zeta3, -zeta1, -zeta3, zeta2, zeta4, -zeta2, -zeta4];
    let zeta = _vld1q_s16(&zetas);

    let a0 = _vtrn1q_s16(lhs.low, lhs.high); // a0, a8, a2, a10, ...
    let a1 = _vtrn2q_s16(lhs.low, lhs.high); // a1, a9, a3, a11, ...
    let b0 = _vtrn1q_s16(rhs.low, rhs.high); // b0, b8, b2, b10, ...
    let b1 = _vtrn2q_s16(rhs.low, rhs.high); // b1, b9, b3, b11, ...

    let a1b1 = montgomery_multiply_int16x8_t(a1, b1);
    let a1b1_low = _vmull_s16(_vget_low_s16(a1b1), _vget_low_s16(zeta)); // a1b1z, a9b9z, a3b3z, a11b11z
    let a1b1_high = _vmull_high_s16(a1b1, zeta); // a5b5z, a13b13z, a7b7z, a15b15z

    let fst_low =
        _vreinterpretq_s16_s32(_vmlal_s16(a1b1_low, _vget_low_s16(a0), _vget_low_s16(b0))); // 0, 8, 2, 10
    let fst_high = _vreinterpretq_s16_s32(_vmlal_high_s16(a1b1_high, a0, b0)); // 4, 12, 6, 14

    let a0b1_low = _vmull_s16(_vget_low_s16(a0), _vget_low_s16(b1));
    let a0b1_high = _vmull_high_s16(a0, b1);

    let snd_low =
        _vreinterpretq_s16_s32(_vmlal_s16(a0b1_low, _vget_low_s16(a1), _vget_low_s16(b0))); // 1, 9, 3, 11
    let snd_high = _vreinterpretq_s16_s32(_vmlal_high_s16(a0b1_high, a1, b0)); // 5, 13, 7, 15

    let fst_low16 = _vtrn1q_s16(fst_low, fst_high); // 0,4,8,12,2,6,10,14
    let fst_high16 = _vtrn2q_s16(fst_low, fst_high);
    let snd_low16 = _vtrn1q_s16(snd_low, snd_high); // 1,5,9,13,3,7,11,15
    let snd_high16 = _vtrn2q_s16(snd_low, snd_high);

    let fst = montgomery_reduce_int16x8_t(fst_low16, fst_high16); // 0,4,8,12,2,6,10,14
    let snd = montgomery_reduce_int16x8_t(snd_low16, snd_high16); // 1,5,9,13,3,7,11,15

    let low0 = _vreinterpretq_s32_s16(_vtrn1q_s16(fst, snd)); // 0,1,8,9,2,3,10,11
    let high0 = _vreinterpretq_s32_s16(_vtrn2q_s16(fst, snd)); // 4,5,12,13,6,7,14,15

    let low1 = _vreinterpretq_s16_s32(_vtrn1q_s32(low0, high0)); // 0,1,4,5,2,3,6,7
    let high1 = _vreinterpretq_s16_s32(_vtrn2q_s32(low0, high0)); // 8,9,12,13,10,11,14,15

    let indexes: [u8; 16] = [0, 1, 2, 3, 8, 9, 10, 11, 4, 5, 6, 7, 12, 13, 14, 15];
    let index = _vld1q_u8(&indexes);
    let low2 = _vreinterpretq_s16_u8(_vqtbl1q_u8(_vreinterpretq_u8_s16(low1), index));
    let high2 = _vreinterpretq_s16_u8(_vqtbl1q_u8(_vreinterpretq_u8_s16(high1), index));

    SIMD128Vector {
        low: low2,
        high: high2,
    }
}

#[inline(always)]
pub(crate) fn serialize_1(v: SIMD128Vector) -> [u8; 2] {
    let shifter: [i16; 8] = [0, 1, 2, 3, 4, 5, 6, 7];
    let shift = _vld1q_s16(&shifter);
    let low = _vshlq_s16(v.low, shift);
    let high = _vshlq_s16(v.high, shift);
    let low = _vaddvq_s16(low);
    let high = _vaddvq_s16(high);
    [low as u8, high as u8]
}

#[inline(always)]
pub(crate) fn deserialize_1(a: &[u8]) -> SIMD128Vector {
    let one = _vdupq_n_s16(1);
    let low = _vdupq_n_s16(a[0] as i16);
    let high = _vdupq_n_s16(a[1] as i16);
    let shifter: [i16; 8] = [0, 0xff, -2, -3, -4, -5, -6, -7];
    let shift = _vld1q_s16(&shifter);
    let low = _vshlq_s16(low, shift);
    let high = _vshlq_s16(high, shift);
    SIMD128Vector {
        low: _vandq_s16(low, one),
        high: _vandq_s16(high, one),
    }
}

#[inline(always)]
pub(crate) fn serialize_4(v: SIMD128Vector) -> [u8; 8] {
    let shifter: [i16; 8] = [0, 4, 8, 12, 0, 4, 8, 12];
    let shift = _vld1q_s16(&shifter);
    let lowt = _vshlq_u16(_vreinterpretq_u16_s16(v.low), shift);
    let hight = _vshlq_u16(_vreinterpretq_u16_s16(v.high), shift);
    let sum0 = _vaddv_u16(_vget_low_u16(lowt)) as u64;
    let sum1 = _vaddv_u16(_vget_high_u16(lowt)) as u64;
    let sum2 = _vaddv_u16(_vget_low_u16(hight)) as u64;
    let sum3 = _vaddv_u16(_vget_high_u16(hight)) as u64;
    let sum = sum0 | (sum1 << 16) | (sum2 << 32) | (sum3 << 48);
    sum.to_le_bytes()
}

#[inline(always)]
pub(crate) fn deserialize_4(v: &[u8]) -> SIMD128Vector {
    let input = u64::from_le_bytes(v.try_into().unwrap());
    let mut low = [0i16; 8];
    let mut high = [0i16; 8];
    low[0] = (input & 0x0f) as i16;
    low[1] = ((input >> 4) & 0x0f) as i16;
    low[2] = ((input >> 8) & 0x0f) as i16;
    low[3] = ((input >> 12) & 0x0f) as i16;
    low[4] = ((input >> 16) & 0x0f) as i16;
    low[5] = ((input >> 20) & 0x0f) as i16;
    low[6] = ((input >> 24) & 0x0f) as i16;
    low[7] = ((input >> 28) & 0x0f) as i16;
    high[0] = ((input >> 32) & 0x0f) as i16;
    high[1] = ((input >> 36) & 0x0f) as i16;
    high[2] = ((input >> 40) & 0x0f) as i16;
    high[3] = ((input >> 44) & 0x0f) as i16;
    high[4] = ((input >> 48) & 0x0f) as i16;
    high[5] = ((input >> 52) & 0x0f) as i16;
    high[6] = ((input >> 56) & 0x0f) as i16;
    high[7] = ((input >> 60) & 0x0f) as i16;
    SIMD128Vector {
        low: _vld1q_s16(&low),
        high: _vld1q_s16(&high),
    }
}

#[inline(always)]
pub(crate) fn serialize_5(v: SIMD128Vector) -> [u8; 10] {
    let mut res = [0u8; 10];
    let out = to_i16_array(v);
    res[0] = (out[0] | out[1] << 5) as u8;
    res[1] = (out[1] >> 3 | out[2] << 2 | out[3] << 7) as u8;
    res[2] = (out[3] >> 1 | out[4] << 4) as u8;
    res[3] = (out[4] >> 4 | out[5] << 1 | out[6] << 6) as u8;
    res[4] = (out[6] >> 2 | out[7] << 3) as u8;
    res[5] = (out[8 + 0] | out[8 + 1] << 5) as u8;
    res[6] = (out[8 + 1] >> 3 | out[8 + 2] << 2 | out[8 + 3] << 7) as u8;
    res[7] = (out[8 + 3] >> 1 | out[8 + 4] << 4) as u8;
    res[8] = (out[8 + 4] >> 4 | out[8 + 5] << 1 | out[8 + 6] << 6) as u8;
    res[9] = (out[8 + 6] >> 2 | out[8 + 7] << 3) as u8;
    res
}

#[inline(always)]
pub(crate) fn deserialize_5(v: &[u8]) -> SIMD128Vector {
    let mut input0 = [0u8; 8];
    input0[0..5].copy_from_slice(&v[0..5]);
    let low64 = u64::from_le_bytes(input0);
    let mut input1 = [0u8; 8];
    input1[0..5].copy_from_slice(&v[5..10]);
    let high64 = u64::from_le_bytes(input1);

    let mut low = [0i16; 8];
    let mut high = [0i16; 8];

    low[0] = (low64 & 0x1F) as i16;
    low[1] = ((low64 >> 5) & 0x1F) as i16;
    low[2] = ((low64 >> 10) & 0x1F) as i16;
    low[3] = ((low64 >> 15) & 0x1F) as i16;
    low[4] = ((low64 >> 20) & 0x1F) as i16;
    low[5] = ((low64 >> 25) & 0x1F) as i16;
    low[6] = ((low64 >> 30) & 0x1F) as i16;
    low[7] = ((low64 >> 35) & 0x1F) as i16;

    high[0] = (high64 & 0x1F) as i16;
    high[1] = ((high64 >> 5) & 0x1F) as i16;
    high[2] = ((high64 >> 10) & 0x1F) as i16;
    high[3] = ((high64 >> 15) & 0x1F) as i16;
    high[4] = ((high64 >> 20) & 0x1F) as i16;
    high[5] = ((high64 >> 25) & 0x1F) as i16;
    high[6] = ((high64 >> 30) & 0x1F) as i16;
    high[7] = ((high64 >> 35) & 0x1F) as i16;

    SIMD128Vector {
        low: _vld1q_s16(&low),
        high: _vld1q_s16(&high),
    }
}

#[inline(always)]
pub(crate) fn serialize_10(v: SIMD128Vector) -> [u8; 20] {
    let low0 = _vreinterpretq_s32_s16(_vtrn1q_s16(v.low, v.low)); // a0, a0, a2, a2, a4, a4, a6, a6
    let low1 = _vreinterpretq_s32_s16(_vtrn2q_s16(v.low, v.low)); // a1, a1, a3, a3, a5, a5, a7, a7
    let mixt = _vsliq_n_s32::<10>(low0, low1); // a1a0, a3a2, a5a4, a7a6

    let low0 = _vreinterpretq_s64_s32(_vtrn1q_s32(mixt, mixt)); // a1a0, a1a0, a5a4, a5a4
    let low1 = _vreinterpretq_s64_s32(_vtrn2q_s32(mixt, mixt)); // a3a2, a3a2, a7a6, a7a6
    let low_mix = _vsliq_n_s64::<20>(low0, low1); // a3a2a1a0, a7a6a5a4

    let high0 = _vreinterpretq_s32_s16(_vtrn1q_s16(v.high, v.high)); // a0, a0, a2, a2, a4, a4, a6, a6
    let high1 = _vreinterpretq_s32_s16(_vtrn2q_s16(v.high, v.high)); // a1, a1, a3, a3, a5, a5, a7, a7
    let mixt = _vsliq_n_s32::<10>(high0, high1); // a1a0, a3a2, a5a4, a7a6

    let high0 = _vreinterpretq_s64_s32(_vtrn1q_s32(mixt, mixt)); // a1a0, a1a0, a5a4, a5a4
    let high1 = _vreinterpretq_s64_s32(_vtrn2q_s32(mixt, mixt)); // a3a2, a3a2, a7a6, a7a6
    let high_mix = _vsliq_n_s64::<20>(high0, high1); // a3a2a1a0, a7a6a5a4

    let mut result32 = [0u8; 32];
    _vst1q_u8(&mut result32[0..16], _vreinterpretq_u8_s64(low_mix));
    _vst1q_u8(&mut result32[16..32], _vreinterpretq_u8_s64(high_mix));
    let mut result = [0u8; 20];
    result[0..5].copy_from_slice(&result32[0..5]);
    result[5..10].copy_from_slice(&result32[8..13]);
    result[10..15].copy_from_slice(&result32[16..21]);
    result[15..20].copy_from_slice(&result32[24..29]);
    result
}

#[inline(always)]
pub(crate) fn deserialize_10(v: &[u8]) -> SIMD128Vector {
    let mut input0 = [0u8; 8];
    let mut input1 = [0u8; 8];
    let mut input2 = [0u8; 4];
    input0.copy_from_slice(&v[0..8]);
    input1.copy_from_slice(&v[8..16]);
    input2.copy_from_slice(&v[16..20]);
    let input0 = u64::from_le_bytes(input0);
    let input1 = u64::from_le_bytes(input1);
    let input2 = u32::from_le_bytes(input2);
    let mut low = [0i16; 8];
    let mut high = [0i16; 8];
    low[0] = (input0 & 0x3ff) as i16;
    low[1] = ((input0 >> 10) & 0x3ff) as i16;
    low[2] = ((input0 >> 20) & 0x3ff) as i16;
    low[3] = ((input0 >> 30) & 0x3ff) as i16;
    low[4] = ((input0 >> 40) & 0x3ff) as i16;
    low[5] = ((input0 >> 50) & 0x3ff) as i16;
    low[6] = (((input0 >> 60) | (input1 << 4)) & 0x3ff) as i16;
    low[7] = ((input1 >> 6) & 0x3ff) as i16;
    high[0] = ((input1 >> 16) & 0x3ff) as i16;
    high[1] = ((input1 >> 26) & 0x3ff) as i16;
    high[2] = ((input1 >> 36) & 0x3ff) as i16;
    high[3] = ((input1 >> 46) & 0x3ff) as i16;
    high[4] = ((((input1 >> 56) as u32) | (input2 << 8)) & 0x3ff) as i16;
    high[5] = ((input2 >> 2) & 0x3ff) as i16;
    high[6] = ((input2 >> 12) & 0x3ff) as i16;
    high[7] = ((input2 >> 22) & 0x3ff) as i16;

    SIMD128Vector {
        low: _vld1q_s16(&low),
        high: _vld1q_s16(&high),
    }
}

#[inline(always)]
pub(crate) fn serialize_11(v: SIMD128Vector) -> [u8; 22] {
    let input = to_i16_array(v);
    let mut result = [0u8; 22];
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

    result[11 + 0] = input[8 + 0] as u8; // 3 left in 0
    result[11 + 1] = ((input[8 + 0] >> 8) | (input[8 + 1] << 3)) as u8; // 6 left in 1
    result[11 + 2] = ((input[8 + 1] >> 5) | (input[8 + 2] << 6)) as u8; // 9 left in 2
    result[11 + 3] = (input[8 + 2] >> 2) as u8; // 1 left in 2
    result[11 + 4] = ((input[8 + 2] >> 10) | (input[8 + 3] << 1)) as u8; // 4 left in 3
    result[11 + 5] = ((input[8 + 3] >> 7) | (input[8 + 4] << 4)) as u8; // 7 left in 4
    result[11 + 6] = ((input[8 + 4] >> 4) | (input[8 + 5] << 7)) as u8; // 10 left in 5
    result[11 + 7] = (input[8 + 5] >> 1) as u8; // 2 left in 5
    result[11 + 8] = ((input[8 + 5] >> 9) | (input[8 + 6] << 2)) as u8; // 5 left in 6
    result[11 + 9] = ((input[8 + 6] >> 6) | (input[8 + 7] << 5)) as u8; // 8 left in 7
    result[11 + 10] = (input[8 + 7] >> 3) as u8;
    result
}

#[inline(always)]
pub(crate) fn deserialize_11(v: &[u8]) -> SIMD128Vector {
    let mut input0 = [0u8; 8];
    let mut input1 = [0u8; 8];
    let mut input2 = [0u8; 8];
    input0.copy_from_slice(&v[0..8]);
    input1.copy_from_slice(&v[8..16]);
    input2[0..6].copy_from_slice(&v[16..22]);
    let input0 = u64::from_le_bytes(input0);
    let input1 = u64::from_le_bytes(input1);
    let input2 = u64::from_le_bytes(input2);

    let mut low = [0i16; 8];
    let mut high = [0i16; 8];

    low[0] = (input0 & 0x7FF) as i16;
    low[1] = ((input0 >> 11) & 0x7FF) as i16;
    low[2] = ((input0 >> 22) & 0x7FF) as i16;
    low[3] = ((input0 >> 33) & 0x7FF) as i16;
    low[4] = ((input0 >> 44) & 0x7FF) as i16;
    low[5] = (((input0 >> 55) | (input1 << 9)) & 0x7FF) as i16;
    low[6] = ((input1 >> 2) & 0x7FF) as i16;
    low[7] = ((input1 >> 13) & 0x7FF) as i16;

    high[0] = ((input1 >> 24) & 0x7FF) as i16;
    high[1] = ((input1 >> 35) & 0x7FF) as i16;
    high[2] = ((input1 >> 46) & 0x7FF) as i16;
    high[3] = (((input1 >> 57) | (input2 << 7)) & 0x7FF) as i16;
    high[4] = ((input2 >> 4) & 0x7FF) as i16;
    high[5] = ((input2 >> 15) & 0x7FF) as i16;
    high[6] = ((input2 >> 26) & 0x7FF) as i16;
    high[7] = ((input2 >> 37) & 0x7FF) as i16;

    SIMD128Vector {
        low: _vld1q_s16(&low),
        high: _vld1q_s16(&high),
    }
}

#[inline(always)]
pub(crate) fn serialize_12(v: SIMD128Vector) -> [u8; 24] {
    let low0 = _vreinterpretq_s32_s16(_vtrn1q_s16(v.low, v.low)); // a0, a0, a2, a2, a4, a4, a6, a6
    let low1 = _vreinterpretq_s32_s16(_vtrn2q_s16(v.low, v.low)); // a1, a1, a3, a3, a5, a5, a7, a7
    let mixt = _vsliq_n_s32::<12>(low0, low1); // a1a0, a3a2, a5a4, a7a6

    let low0 = _vreinterpretq_s64_s32(_vtrn1q_s32(mixt, mixt)); // a1a0, a1a0, a5a4, a5a4
    let low1 = _vreinterpretq_s64_s32(_vtrn2q_s32(mixt, mixt)); // a3a2, a3a2, a7a6, a7a6
    let low_mix = _vsliq_n_s64::<24>(low0, low1); // a3a2a1a0, a7a6a5a4

    let high0 = _vreinterpretq_s32_s16(_vtrn1q_s16(v.high, v.high)); // a0, a0, a2, a2, a4, a4, a6, a6
    let high1 = _vreinterpretq_s32_s16(_vtrn2q_s16(v.high, v.high)); // a1, a1, a3, a3, a5, a5, a7, a7
    let mixt = _vsliq_n_s32::<12>(high0, high1); // a1a0, a3a2, a5a4, a7a6

    let high0 = _vreinterpretq_s64_s32(_vtrn1q_s32(mixt, mixt)); // a1a0, a1a0, a5a4, a5a4
    let high1 = _vreinterpretq_s64_s32(_vtrn2q_s32(mixt, mixt)); // a3a2, a3a2, a7a6, a7a6
    let high_mix = _vsliq_n_s64::<24>(high0, high1); // a3a2a1a0, a7a6a5a4

    let mut result32 = [0u8; 32];
    _vst1q_u8(&mut result32[0..16], _vreinterpretq_u8_s64(low_mix));
    _vst1q_u8(&mut result32[16..32], _vreinterpretq_u8_s64(high_mix));
    let mut result = [0u8; 24];
    result[0..6].copy_from_slice(&result32[0..6]);
    result[6..12].copy_from_slice(&result32[8..14]);
    result[12..18].copy_from_slice(&result32[16..22]);
    result[18..24].copy_from_slice(&result32[24..30]);
    result
}

#[inline(always)]
pub(crate) fn deserialize_12(v: &[u8]) -> SIMD128Vector {
    let indexes: [u8; 16] = [0, 1, 1, 2, 3, 4, 4, 5, 6, 7, 7, 8, 9, 10, 10, 11];
    let index_vec = _vld1q_u8(&indexes);
    let shifts: [i16; 8] = [0, -4, 0, -4, 0, -4, 0, -4];
    let shift_vec = _vld1q_s16(&shifts);
    let mask12 = _vdupq_n_u16(0xfff);

    let mut input0 = [0u8; 16];
    input0[0..12].copy_from_slice(&v[0..12]);
    let input_vec0 = _vld1q_u8(&input0);

    let mut input1 = [0u8; 16];
    input1[0..12].copy_from_slice(&v[12..24]);
    let input_vec1 = _vld1q_u8(&input1);

    let moved0 = _vreinterpretq_u16_u8(_vqtbl1q_u8(input_vec0, index_vec));
    let shifted0 = _vshlq_u16(moved0, shift_vec);
    let low = _vreinterpretq_s16_u16(_vandq_u16(shifted0, mask12));

    let moved1 = _vreinterpretq_u16_u8(_vqtbl1q_u8(input_vec1, index_vec));
    let shifted1 = _vshlq_u16(moved1, shift_vec);
    let high = _vreinterpretq_s16_u16(_vandq_u16(shifted1, mask12));

    SIMD128Vector {
        low: low,
        high: high,
    }
}
