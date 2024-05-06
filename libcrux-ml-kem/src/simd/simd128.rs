use crate::{
    arithmetic::INVERSE_OF_MODULUS_MOD_MONTGOMERY_R, constants::FIELD_MODULUS, simd::simd_trait::*,
};
use core::arch::aarch64::*;

#[derive(Clone, Copy)]
pub(crate) struct SIMD128Vector {
    vec: int16x8_t
}

#[allow(non_snake_case)]
#[inline(always)]
fn ZERO() -> SIMD128Vector {
    SIMD128Vector {
        vec: unsafe { vdupq_n_s16(0) },
    }
}

#[inline(always)]
fn to_i16_array(v: SIMD128Vector) -> [i16; 8] {
    let mut out = [0i16; 8];
    unsafe { vst1q_s16(out.as_mut_ptr() as *mut i16, v.vec) }
    out
}

#[inline(always)]
fn from_i16_array(array: [i16; 8]) -> SIMD128Vector {
    SIMD128Vector {
        vec: unsafe { vld1q_s16(array.as_ptr() as *const i16) },
    }
}

#[inline(always)]
fn _add_constant(mut v: SIMD128Vector, c: i16) -> SIMD128Vector {
    let c = unsafe { vdupq_n_s16(c) };
    v.vec = unsafe { vaddq_s16(v.vec, c) };
    v
}

#[inline(always)]
fn add(mut lhs: SIMD128Vector, rhs: &SIMD128Vector) -> SIMD128Vector {
    lhs.vec = unsafe { vaddq_s16(lhs.vec, rhs.vec) };
    lhs
}

#[inline(always)]
fn sub(mut lhs: SIMD128Vector, rhs: &SIMD128Vector) -> SIMD128Vector {
    lhs.vec = unsafe { vsubq_s16(lhs.vec, rhs.vec) };
    lhs
}

#[inline(always)]
fn multiply_by_constant(mut v: SIMD128Vector, c: i16) -> SIMD128Vector {
    v.vec = unsafe { vmulq_n_s16(v.vec, c) };
    v
}

#[inline(always)]
fn bitwise_and_with_constant(mut v: SIMD128Vector, c: i16) -> SIMD128Vector {
    let c = unsafe { vdupq_n_s16(c) };
    v.vec = unsafe { vandq_s16(v.vec, c) };
    v
}

#[inline(always)]
fn shift_right<const SHIFT_BY: i32>(mut v: SIMD128Vector) -> SIMD128Vector {
    // Should find special cases of this
    // e.g when doing a right shift just to propagate signed bits, use vclezq_s32 instead
    v.vec = unsafe { vshrq_n_s16::<SHIFT_BY>(v.vec) };
    v
}

#[inline(always)]
fn _shift_left<const SHIFT_BY: i32>(mut lhs: SIMD128Vector) -> SIMD128Vector {
    lhs.vec = unsafe { vshlq_n_s16::<SHIFT_BY>(lhs.vec) };
    lhs
}

#[inline(always)]
fn cond_subtract_3329(mut v: SIMD128Vector) -> SIMD128Vector {
    let c = unsafe { vdupq_n_s16(3329) };
    let m = unsafe { vcgeq_s16(v.vec, c) };
    let c = unsafe { vandq_s16(c, vreinterpretq_s16_u16(m)) };
    v.vec = unsafe { vsubq_s16(v.vec, c) };
    v  
}

const BARRETT_MULTIPLIER: i16 = 20159;

#[inline(always)]
fn barrett_reduce(mut v: SIMD128Vector) -> SIMD128Vector {
    //let pv = crate::simd::portable::from_i16_array(to_i16_array(v));
    //from_i16_array(crate::simd::portable::to_i16_array(crate::simd::portable::barrett_reduce(pv)))

    // This is what we are trying to do in portable:
    // let t = (value as i32 * BARRETT_MULTIPLIER) + (BARRETT_R >> 1);
    // let quotient = (t >> BARRETT_SHIFT) as i16;
    // let result = value - (quotient * FIELD_MODULUS);

    let adder = unsafe { vdupq_n_s16(1 << 10) };
    let vec = unsafe { vqdmulhq_n_s16(v.vec, BARRETT_MULTIPLIER as i16) };
    let vec = unsafe { vaddq_s16(vec, adder) } ;
    let quotient = unsafe { vshrq_n_s16::<11>(vec) } ;
    let sub = unsafe { vmulq_n_s16(quotient, FIELD_MODULUS) } ;
    v.vec = unsafe { vsubq_s16(v.vec, sub) };
    v
}

// #[inline(always)]
// fn montgomery_reduce_i32x2_t(v: int32x2_t) -> int32x2_t {
//     // This is what we are trying to do in portable:
//     // let t = get_n_least_significant_bits(MONTGOMERY_SHIFT, value as u32)
//     //     * INVERSE_OF_MODULUS_MOD_MONTGOMERY_R;
//     // let k = get_n_least_significant_bits(MONTGOMERY_SHIFT, t) as i16;
//     // let k_times_modulus = (k as i32) * FIELD_MODULUS;
//     // let c = k_times_modulus >> MONTGOMERY_SHIFT;
//     // let value_high = value >> MONTGOMERY_SHIFT;
//     // value_high - c

//     let m = unsafe { vdup_n_s32(0x0000ffff) };
//     let t0 = unsafe { vand_s32(v, m) };
//     let t0 = unsafe { vmul_n_s32(t0, INVERSE_OF_MODULUS_MOD_MONTGOMERY_R as i32) };
//     let t0 = unsafe { vreinterpret_s16_s32(t0) };
//     let t0 = unsafe { vmull_n_s16(t0, FIELD_MODULUS as i16) };
//     let c0 = unsafe { vshrq_n_s32::<16>(t0) };
//     let c0 = unsafe { vmovn_s64(vreinterpretq_s64_s32(c0)) };
//     let v0 = unsafe { vshr_n_s32::<16>(v) };
//     let v = unsafe { vsub_s32(v0, c0) };
//     v
// }

// #[inline(always)]
// fn montgomery_reduce_i32x4_t(v: int32x4_t) -> int32x4_t {
//     // This is what we are trying to do in portable:
//     // let t = get_n_least_significant_bits(MONTGOMERY_SHIFT, value as u32)
//     //     * INVERSE_OF_MODULUS_MOD_MONTGOMERY_R;
//     // let k = get_n_least_significant_bits(MONTGOMERY_SHIFT, t) as i16;
//     // let k_times_modulus = (k as i32) * FIELD_MODULUS;
//     // let c = k_times_modulus >> MONTGOMERY_SHIFT;
//     // let value_high = value >> MONTGOMERY_SHIFT;
//     //value_high - c

//     let t = unsafe {
//         vreinterpretq_s16_s32(vmulq_n_s32(v, INVERSE_OF_MODULUS_MOD_MONTGOMERY_R as i32))
//     };
//     let c = unsafe { vreinterpretq_s32_s16(vqdmulhq_n_s16(t, FIELD_MODULUS as i16)) };
//     let c = unsafe { vshrq_n_s32::<17>(vshlq_n_s32::<16>(c)) };
//     let v = unsafe { vshrq_n_s32::<16>(v) };
//     let v = unsafe { vsubq_s32(v, c) };
//     v
// }

#[inline(always)]
fn montgomery_reduce_int16x8_t(low: int16x8_t, high: int16x8_t) -> int16x8_t {
    // This is what we are trying to do in portable:
    // let k = low as i32 * INVERSE_OF_MODULUS_MOD_MONTGOMERY_R;
    // let k_times_modulus = (k as i16 as i32) * (FIELD_MODULUS as i32);
    // let c = (k_times_modulus >> MONTGOMERY_SHIFT) as i16;
    // high - c

    let k = unsafe { vreinterpretq_s16_u16(vmulq_n_u16(vreinterpretq_u16_s16(low), INVERSE_OF_MODULUS_MOD_MONTGOMERY_R as u16)) };
    let c = unsafe { vshrq_n_s16::<1>(vqdmulhq_n_s16(k, FIELD_MODULUS as i16)) };
    unsafe { vsubq_s16(high, c) }
}

#[inline(always)]
fn montgomery_multiply_by_constant_int16x8_t(v: int16x8_t, c: i16) -> int16x8_t {
    // This is what we are trying to do in portable:
    // let value = v as i32 * c
    // let k = (value as i16) as i32 * INVERSE_OF_MODULUS_MOD_MONTGOMERY_R;
    // let k_times_modulus = (k as i16 as i32) * (FIELD_MODULUS as i32);
    // let c = (k_times_modulus >> MONTGOMERY_SHIFT) as i16;
    // let value_high = (value >> MONTGOMERY_SHIFT) as i16;
    // value_high - c

    let v_low = unsafe { vmulq_n_s16(v, c) };
    let v_high = unsafe { vshrq_n_s16::<1>(vqdmulhq_n_s16(v, c)) };
    montgomery_reduce_int16x8_t(v_low, v_high)
}

#[inline(always)]
fn montgomery_multiply_int16x8_t(v: int16x8_t, c: int16x8_t) -> int16x8_t {
    // This is what we are trying to do in portable:
    // let value = v as i32 * c
    // let k = (value as i16) as i32 * INVERSE_OF_MODULUS_MOD_MONTGOMERY_R;
    // let k_times_modulus = (k as i16 as i32) * (FIELD_MODULUS as i32);
    // let c = (k_times_modulus >> MONTGOMERY_SHIFT) as i16;
    // let value_high = (value >> MONTGOMERY_SHIFT) as i16;
    // value_high - c

    let v_low = unsafe { vmulq_s16(v, c) };
    let v_high = unsafe { vshrq_n_s16::<1>(vqdmulhq_s16(v, c)) };
    montgomery_reduce_int16x8_t(v_low, v_high)
}

#[inline(always)]
fn montgomery_multiply_by_constant(mut v: SIMD128Vector, c: i16) -> SIMD128Vector {
    v.vec = montgomery_multiply_by_constant_int16x8_t(v.vec, c);
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

    let half = unsafe { vdupq_n_s16(1664) };
    let quarter = unsafe { vdupq_n_s16(832) };
    let shifted = unsafe { vsubq_s16(half, v.vec) };
    let mask = unsafe { vshrq_n_s16::<15>(shifted) };
    let shifted_to_positive = unsafe { veorq_s16(mask, shifted) };
    let shifted_positive_in_range = unsafe { vsubq_s16(shifted_to_positive, quarter) };
    v.vec = unsafe {
        vreinterpretq_s16_u16(vshrq_n_u16::<15>(vreinterpretq_u16_s16(
            shifted_positive_in_range,
        )))
    };
    v
}

#[inline(always)]
fn mask_n_least_significant_bits(coefficient_bits: i32) -> i16 {
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

    let half = unsafe { vdupq_n_u32(1664) };
    let mask = unsafe { vdupq_n_s16(mask_n_least_significant_bits(COEFFICIENT_BITS)) };

    let mask16 = unsafe { vdupq_n_u32(0xffff) };
    let v_low = unsafe { vandq_u32(vreinterpretq_u32_s16(v.vec),mask16) }; //a0, a2, a4, a6
    let v_high = unsafe { vshrq_n_u32::<16>(vreinterpretq_u32_s16(v.vec)) }; //a1, a3, a5, a7

    let compressed_low = unsafe { vshlq_n_u32::<COEFFICIENT_BITS>(v_low) };
    let compressed_low = unsafe { vaddq_u32(compressed_low, half)} ;
    let compressed_low = unsafe { vreinterpretq_u32_s32(vqdmulhq_n_s32(vreinterpretq_s32_u32(compressed_low), 10_321_340)) };
    let compressed_low = unsafe { vshrq_n_u32::<4>(compressed_low) };

    let compressed_high = unsafe { vshlq_n_u32::<COEFFICIENT_BITS>(v_high) };
    let compressed_high = unsafe { vaddq_u32(compressed_high, half)} ;
    let compressed_high = unsafe { vreinterpretq_u32_s32(vqdmulhq_n_s32(vreinterpretq_s32_u32(compressed_high), 10_321_340)) };
    let compressed_high = unsafe { vshrq_n_u32::<4>(compressed_high) };

    let compressed = unsafe{ vtrn1q_s16(vreinterpretq_s16_u32(compressed_low), vreinterpretq_s16_u32(compressed_high)) };
    v.vec = unsafe { vandq_s16(compressed, mask) };
    v
}

fn decompress<const COEFFICIENT_BITS: i32>(mut v: SIMD128Vector) -> SIMD128Vector {
   
    let coeff = unsafe { vdupq_n_u32(1 << (COEFFICIENT_BITS - 1)) };

    let mask16 = unsafe { vdupq_n_u32(0xffff) };
    let v_low = unsafe { vandq_u32(vreinterpretq_u32_s16(v.vec),mask16) };
    let v_high = unsafe { vshrq_n_u32::<16>(vreinterpretq_u32_s16(v.vec)) };

    let compressed_low = unsafe { vmulq_n_u32(v_low, FIELD_MODULUS as u32) };
    let compressed_low = unsafe { vaddq_u32(compressed_low, coeff)} ;
    let compressed_low = unsafe { vshrq_n_u32::<COEFFICIENT_BITS>(compressed_low) };

    let compressed_high = unsafe { vmulq_n_u32(v_high, FIELD_MODULUS as u32) };
    let compressed_high = unsafe { vaddq_u32(compressed_high, coeff)} ;
    let compressed_high = unsafe { vshrq_n_u32::<COEFFICIENT_BITS>(compressed_high) };

    v.vec = unsafe { vtrn1q_s16(vreinterpretq_s16_u32(compressed_low),vreinterpretq_s16_u32(compressed_high)) };
    v
}


#[inline(always)]
fn ntt_layer_1_step(mut v: SIMD128Vector, zeta1: i16, zeta2: i16) -> SIMD128Vector {
    // This is what we are trying to do, pointwise for every pair of elements:
    // let t = simd::Vector::montgomery_multiply_fe_by_fer(b, zeta_r);
    // b = simd::Vector::sub(a, &t);
    // a = simd::Vector::add(a, &t);

    let zetas = [zeta1, zeta1, -zeta1, -zeta1, zeta2, zeta2, -zeta2, -zeta2];
    let zeta = unsafe { vld1q_s16(zetas.as_ptr() as *const i16) };
    let dup_a = unsafe { vreinterpretq_s16_s32(vtrn1q_s32(vreinterpretq_s32_s16(v.vec), vreinterpretq_s32_s16(v.vec))) };
    let dup_b = unsafe { vreinterpretq_s16_s32(vtrn2q_s32(vreinterpretq_s32_s16(v.vec), vreinterpretq_s32_s16(v.vec))) };
    let t = montgomery_multiply_int16x8_t(dup_b, zeta);
    v.vec = unsafe{ vaddq_s16(dup_a, t) };
    v
}

#[inline(always)]
fn ntt_layer_2_step(mut v: SIMD128Vector, zeta: i16) -> SIMD128Vector {
    // This is what we are trying to do for every four elements:
    // let t = simd::Vector::montgomery_multiply_fe_by_fer(b, zeta_r);
    // b = simd::Vector::sub(a, &t);
    // a = simd::Vector::add(a, &t);

    let zetas = [zeta, zeta, zeta, zeta, -zeta, -zeta, -zeta, -zeta];
    let zeta = unsafe { vld1q_s16(zetas.as_ptr() as *const i16) };
    let dup_a = unsafe { vreinterpretq_s16_s64(vtrn1q_s64(vreinterpretq_s64_s16(v.vec), vreinterpretq_s64_s16(v.vec))) };
    let dup_b = unsafe { vreinterpretq_s16_s64(vtrn2q_s64(vreinterpretq_s64_s16(v.vec), vreinterpretq_s64_s16(v.vec))) };
    let t = montgomery_multiply_int16x8_t(dup_b, zeta);
    v.vec = unsafe{ vaddq_s16(dup_a, t) };
    v
}

#[inline(always)]
fn inv_ntt_layer_1_step(mut v: SIMD128Vector, zeta1: i16, zeta2: i16) -> SIMD128Vector {
    // This is what we are trying to do for every two elements:
    //let a_minus_b = simd::Vector::sub(b, &a);
    //a = simd::Vector::add(a, &b);
    //b = simd::Vector::montgomery_multiply_fe_by_fer(a_minus_b, zeta_r);
    //(a, b)

    let dup_b = unsafe { vreinterpretq_s16_s32(vtrn2q_s32(vreinterpretq_s32_s16(v.vec), vreinterpretq_s32_s16(v.vec))) };
    let a = unsafe { vaddq_s16(v.vec, dup_b) };
    let b_minus_a = unsafe { vsubq_s16(dup_b, v.vec) };

    let zetas = [zeta1, zeta1, 0, 0, zeta2, zeta2, 0, 0];
    let zeta = unsafe { vld1q_s16(zetas.as_ptr() as *const i16) };
    let b = montgomery_multiply_int16x8_t(b_minus_a, zeta);
    v.vec = unsafe { vreinterpretq_s16_s32(vtrn1q_s32(vreinterpretq_s32_s16(a), vreinterpretq_s32_s16(b))) };
    v
}

#[inline(always)]
fn inv_ntt_layer_2_step(mut v: SIMD128Vector, zeta: i16) -> SIMD128Vector {
    // This is what we are trying to do for every four elements:
    //let a_minus_b = simd::Vector::sub(b, &a);
    //a = simd::Vector::add(a, &b);
    //b = simd::Vector::montgomery_multiply_fe_by_fer(a_minus_b, zeta_r);
    //(a, b)

    let dup_b = unsafe { vreinterpretq_s16_s64(vtrn2q_s64(vreinterpretq_s64_s16(v.vec), vreinterpretq_s64_s16(v.vec))) };
    let a = unsafe { vaddq_s16(v.vec, dup_b) };
    let b_minus_a = unsafe { vsubq_s16(dup_b, v.vec) };

    let zetas = [zeta, zeta, zeta, zeta, 0, 0, 0, 0];
    let zeta = unsafe { vld1q_s16(zetas.as_ptr() as *const i16) };
    let b = montgomery_multiply_int16x8_t(b_minus_a, zeta);
    v.vec = unsafe { vreinterpretq_s16_s64(vtrn1q_s64(vreinterpretq_s64_s16(a), vreinterpretq_s64_s16(b))) };
    v
}

#[inline(always)]
fn ntt_multiply(lhs: &SIMD128Vector, rhs: &SIMD128Vector, zeta0: i16, zeta1: i16) -> SIMD128Vector {
    // This is what we are trying to do for pairs of two elements:
    // montgomery_reduce(a0 * b0 + montgomery_reduce(a1 * b1) * zeta),
    // montgomery_reduce(a0 * b1 + a1 * b0)
    //let lhsp = crate::simd::portable::from_i16_array(to_i16_array(lhs.clone()));
    //let rhsp = crate::simd::portable::from_i16_array(to_i16_array(rhs.clone()));
    //let mulp = crate::simd::portable::ntt_multiply(&lhsp,&rhsp,zeta0,zeta1);
    //from_i16_array(crate::simd::portable::to_i16_array(mulp))

    let a0 = unsafe { vshrq_n_s32::<16>(vreinterpretq_s32_u32(vshlq_n_u32::<16>(vreinterpretq_u32_s16(lhs.vec)))) };
    let a1 = unsafe { vshrq_n_s32::<16>(vreinterpretq_s32_s16(lhs.vec)) };
    let b0 = unsafe { vshrq_n_s32::<16>(vreinterpretq_s32_u32(vshlq_n_u32::<16>(vreinterpretq_u32_s16(rhs.vec)))) };
    let b1 = unsafe { vshrq_n_s32::<16>(vreinterpretq_s32_s16(rhs.vec)) };

    let zetas: [i32; 4] = [zeta0 as i32, -zeta0 as i32, zeta1 as i32, -zeta1 as i32];
    let zeta = unsafe { vld1q_s32(zetas.as_ptr() as *const i32) };

    let a0b0 = unsafe { vmulq_s32(a0, b0) };
    
    let a1b1 = unsafe { montgomery_multiply_int16x8_t(vreinterpretq_s16_s32(a1), vreinterpretq_s16_s32(b1)) };
    let a1b1 = unsafe { vshrq_n_s32::<16>(vreinterpretq_s32_u32(vshlq_n_u32::<16>(vreinterpretq_u32_s16(a1b1)))) };
    let fst = unsafe { vreinterpretq_s16_s32(vmlaq_s32(a0b0, a1b1, zeta)) };
    
    let a0b1 = unsafe { vmulq_s32(a0, b1) };
    let snd = unsafe { vreinterpretq_s16_s32(vmlaq_s32(a0b1, a1, b0)) };

    let v_low = unsafe { vtrn1q_s16(fst, snd) };
    let v_high = unsafe { vtrn2q_s16(fst, snd) };
    SIMD128Vector {
        vec: montgomery_reduce_int16x8_t(v_low, v_high)
    }
}

#[inline(always)]
fn serialize_1(v: SIMD128Vector) -> u8 {
    let shifter: [i16; 8] = [0, 1, 2, 3, 4, 5, 6, 7];
    let shift = unsafe { vld1q_s16(shifter.as_ptr() as *const i16) };
    let vec = unsafe { vshlq_s16(v.vec, shift) };
    let vec = unsafe { vaddvq_s16(vec) };
    vec as u8
}

#[inline(always)]
fn deserialize_1(a: u8) -> SIMD128Vector {
    let dup = unsafe { vdupq_n_s16(a as i16) };
    let shifter: [i16; 8] = [0, -1, -2, -3, -4, -5, -6, -7];
    let shift = unsafe { vld1q_s16(shifter.as_ptr() as *const i16) };
    let vec = unsafe { vshlq_s16(dup, shift) };
    SIMD128Vector {
        vec: unsafe { vandq_s16(vec, vdupq_n_s16(1)) },
    }
}

#[inline(always)]
fn serialize_4(v: SIMD128Vector) -> [u8; 4] {
    let shifter: [i16; 8] = [0, 4, 8, 12, 0, 4, 8, 12];
    let shift = unsafe { vld1q_s16(shifter.as_ptr() as *const i16) };
    let vect = unsafe { vshlq_u16(vreinterpretq_u16_s16(v.vec), shift) };
    let sum0 = unsafe { vaddv_u16(vget_low_u16(vect)) };
    let sum1 = unsafe { vaddv_u16(vget_high_u16(vect)) };
    (((sum1 as u32) << 16) + (sum0 as u32)).to_le_bytes()
}

#[inline(always)]
fn deserialize_4(v: &[u8]) -> SIMD128Vector {
    let input = u32::from_le_bytes(v.try_into().unwrap());
    let mut vec = [0i16; 8];
    vec[0] = (input & 0x0f) as i16;
    vec[1] = ((input >> 4) & 0x0f) as i16;
    vec[2] = ((input >> 8) & 0x0f) as i16;
    vec[3] = ((input >> 12) & 0x0f) as i16;
    vec[4] = ((input >> 16) & 0x0f) as i16;
    vec[5] = ((input >> 20) & 0x0f) as i16;
    vec[6] = ((input >> 24) & 0x0f) as i16;
    vec[7] = ((input >> 28) & 0x0f) as i16;
    SIMD128Vector {
        vec: unsafe { vld1q_s16(vec.as_ptr() as *const i16) },
    }
}

#[inline(always)]
fn serialize_5(v: SIMD128Vector) -> [u8; 5] {
    let mut res = [0u8; 5];
    let out = to_i16_array(v);
    res[0] = (out[0] | out[1] << 5) as u8;
    res[1] = (out[1] >> 3 | out[2] << 2 | out[3] << 7) as u8;
    res[2] = (out[3] >> 1 | out[4] << 4) as u8;
    res[3] = (out[4] >> 4 | out[5] << 1 | out[6] << 6) as u8;
    res[4] = (out[6] >> 2 | out[7] << 3) as u8;
    res
}

#[inline(always)]
fn deserialize_5(v: &[u8]) -> SIMD128Vector {
    let mut input = [0u8; 8];
    input[0..5].copy_from_slice(&v[0..5]);
    let input = u64::from_le_bytes(input);

    let mut vec = [0i16; 8];

    vec[0] = (input & 0x1F) as i16;
    vec[1] = ((input >> 5) & 0x1F) as i16;
    vec[2] = ((input >> 10) & 0x1F) as i16;
    vec[3] = ((input >> 15) & 0x1F) as i16;
    vec[4] = ((input >> 20) & 0x1F) as i16;
    vec[5] = ((input >> 25) & 0x1F) as i16;
    vec[6] = ((input >> 30) & 0x1F) as i16;
    vec[7] = ((input >> 35) & 0x1F) as i16;

    SIMD128Vector {
        vec: unsafe { vld1q_s16(vec.as_ptr() as *const i16) },
    }
}

#[inline(always)]
fn serialize_10(v: SIMD128Vector) -> [u8; 10] {
    let lowt = unsafe { vreinterpretq_s32_s16(vtrn1q_s16(v.vec, v.vec)) }; // a0, a0, a2, a2, a4, a4, a6, a6
    let hight = unsafe { vreinterpretq_s32_s16(vtrn2q_s16(v.vec, v.vec)) }; // a1, a1, a3, a3, a5, a5, a7, a7
    let mixt = unsafe { vsliq_n_s32::<10>(lowt, hight) }; // a1a0, a3a2, a5a4, a7a6

    let lowt = unsafe { vreinterpretq_s64_s32(vtrn1q_s32(mixt, mixt)) }; // a1a0, a1a0, a5a4, a5a4
    let hight = unsafe { vreinterpretq_s64_s32(vtrn2q_s32(mixt, mixt)) }; // a3a2, a3a2, a7a6, a7a6
    let mixt = unsafe { vsliq_n_s64::<20>(lowt, hight) }; // a3a2a1a0, a7a6a5a4

    let mut result16 = [0u8; 16];
    unsafe { vst1q_u8(result16.as_mut_ptr() as *mut u8, vreinterpretq_u8_s64(mixt)) };
    let mut result10 = [0u8; 10];
    result10[0..5].copy_from_slice(&result16[0..5]);
    result10[5..10].copy_from_slice(&result16[8..13]);
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
    let mut vec = [0i16; 8];
    vec[0] = (input0 & 0x3ff) as i16;
    vec[1] = ((input0 & 0xffc00) >> 10) as i16;
    vec[2] = ((input0 & 0x3ff00000) >> 20) as i16;
    vec[3] = ((input0 & 0xffc0000000) >> 30) as i16;
    vec[4] = (input1 & 0x3ff) as i16;
    vec[5] = ((input1 & 0xffc00) >> 10) as i16;
    vec[6] = ((input1 & 0x3ff00000) >> 20) as i16;
    vec[7] = ((input1 & 0xffc0000000) >> 30) as i16;
    SIMD128Vector {
        vec: unsafe { vld1q_s16(vec.as_ptr() as *const i16) },
    }
}

#[inline(always)]
fn serialize_11(v: SIMD128Vector) -> [u8; 11] {
    let input = to_i16_array(v);
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

    let mut vec = [0i16; 8];

    vec[0] = (input0 & 0x7FF) as i16;
    vec[1] = ((input0 >> 11) & 0x7FF) as i16;
    vec[2] = ((input0 >> 22) & 0x7FF) as i16;
    vec[3] = ((input0 >> 33) & 0x7FF) as i16;
    vec[4] = ((input1 >> 4) & 0x7FF) as i16;
    vec[5] = ((input1 >> 15) & 0x7FF) as i16;
    vec[6] = ((input1 >> 26) & 0x7FF) as i16;
    vec[7] = ((input1 >> 37) & 0x7FF) as i16;

    SIMD128Vector {
        vec: unsafe { vld1q_s16(vec.as_ptr() as *const i16) },
    }
}

#[inline(always)]
fn serialize_12(v: SIMD128Vector) -> [u8; 12] {
//    println!("serialize 12 (simd128): {:?}", to_i16_array(v));

    let lowt = unsafe { vreinterpretq_s32_s16(vtrn1q_s16(v.vec, v.vec)) }; // a0, a0, a2, a2, a4, a4, a6, a6
    let hight = unsafe { vreinterpretq_s32_s16(vtrn2q_s16(v.vec, v.vec)) }; // a1, a1, a3, a3, a5, a5, a7, a7
    let mixt = unsafe { vsliq_n_s32::<12>(lowt, hight) }; // a1a0, a3a2, a5a4, a7a6

    let lowt = unsafe { vreinterpretq_s64_s32(vtrn1q_s32(mixt, mixt)) }; // a1a0, a1a0, a5a4, a5a4
    let hight = unsafe { vreinterpretq_s64_s32(vtrn2q_s32(mixt, mixt)) }; // a3a2, a3a2, a7a6, a7a6
    let mixt = unsafe { vsliq_n_s64::<24>(lowt, hight) }; // a3a2a1a0, a7a6a5a4

    let mut result16 = [0u8; 16];
    unsafe { vst1q_u8(result16.as_mut_ptr() as *mut u8, vreinterpretq_u8_s64(mixt)) };
    let mut result = [0u8; 12];
    result[0..6].copy_from_slice(&result16[0..6]);
    result[6..12].copy_from_slice(&result16[8..14]);
    result
}

#[inline(always)]
fn deserialize_12(v: &[u8]) -> SIMD128Vector {
    let indexes : [u8; 16] = [0, 1, 1, 2, 3, 4, 4, 5, 6, 7, 7, 8, 9, 10, 10, 11];
    let shifts : [i16; 8] = [0, -4, 0, -4, 0, -4, 0, -4];
    let mut input = [0u8; 16];
    input[0..12].copy_from_slice(v);

    let input_vec = unsafe { vld1q_u8(input.as_ptr() as *const u8) };
    let index_vec = unsafe { vld1q_u8(indexes.as_ptr() as *const u8) };
    let moved = unsafe { vreinterpretq_u16_u8(vqtbl1q_u8(input_vec, index_vec)) };
    let shift_vec = unsafe { vld1q_s16(shifts.as_ptr() as *const i16) };
    let shifted = unsafe { vshlq_u16(moved, shift_vec) };
    let mask12 = unsafe { vdupq_n_u16(0xfff) };
    let vec = unsafe { vreinterpretq_s16_u16(vandq_u16(shifted, mask12)) };
    SIMD128Vector {
        vec: vec
    }
}

#[inline(always)]
fn _rej_sample_simd(a: &[u8]) -> (usize, [i16; 8]) {
    let neon_bits : [u16; 8] = [0x1, 0x2, 0x4, 0x8, 0x10, 0x20, 0x40, 0x80];
    let bits = unsafe { vld1q_u16(neon_bits.as_ptr() as *const u16) };
    let input = deserialize_12(a);
    let fm = unsafe { vdupq_n_s16(FIELD_MODULUS) };
    let mask = unsafe { vcltq_s16(input.vec,fm) };

    let mut used = unsafe { vaddvq_u16(vandq_u16(mask, bits)) };
    let pick = used.count_ones();

    // The following indexing is implemented by a large index table in PQClean
    let mut index : [u8;16] = [0u8; 16];
    let mut idx = 0;
    for i in 0..8 {
        if used > 0 {
            let next = used.trailing_zeros();
            idx = idx + next;
            index[i*2] = (idx*2) as u8;
            index[i*2+1] = (idx*2 + 1) as u8;
            idx = idx + 1;
            used = used >> (next+1);
        }
    }
    let index_vec = unsafe { vld1q_u8(index.as_ptr() as *const u8) };
    // End of index table lookup calculation

    let shifted = unsafe { vqtbl1q_u8(vreinterpretq_u8_s16(input.vec),index_vec) };
    let mut out: [i16;8] = [0i16;8];
    unsafe {vst1q_s16(out.as_mut_ptr() as *mut i16, vreinterpretq_s16_u8(shifted)) };
    (pick as usize,out)
}


#[inline(always)]
fn rej_sample(a: &[u8]) -> (usize, [i16; 8]) {
    let mut result = [0i16; 8];
    let mut sampled = 0;
    for bytes in a.chunks(3) {
        let b1 = bytes[0] as i16;
        let b2 = bytes[1] as i16;
        let b3 = bytes[2] as i16;

        let d1 = ((b2 & 0xF) << 8) | b1;
        let d2 = (b3 << 4) | (b2 >> 4);

        if d1 < FIELD_MODULUS && sampled < 8 {
            result[sampled] = d1;
            sampled += 1
        }
        if d2 < FIELD_MODULUS && sampled < 8 {
            result[sampled] = d2;
            sampled += 1
        }
    }
    (sampled,result)
}

impl Operations for SIMD128Vector {
    #[inline(always)]
    fn ZERO() -> Self {
        ZERO()
    }

    fn to_i16_array(v: Self) -> [i16; 8] {
        to_i16_array(v)
    }

    fn from_i16_array(array: [i16; 8]) -> Self {
        from_i16_array(array)
    }

    // fn add_constant(v: Self, c: i16) -> Self {
    //     add_constant(v, c)
    // }

    fn add(lhs: Self, rhs: &Self) -> Self {
        add(lhs, rhs)
    }

    fn sub(lhs: Self, rhs: &Self) -> Self {
        sub(lhs, rhs)
    }

    fn multiply_by_constant(v: Self, c: i16) -> Self {
        multiply_by_constant(v, c)
    }

    fn bitwise_and_with_constant(v: Self, c: i16) -> Self {
        bitwise_and_with_constant(v, c)
    }

    fn shift_right<const SHIFT_BY: i32>(v: Self) -> Self {
        shift_right::<SHIFT_BY>(v)
    }

    // fn shift_left<const SHIFT_BY: i32>(v: Self) -> Self {
    //     shift_left::<SHIFT_BY>(v)
    // }

    fn cond_subtract_3329(v: Self) -> Self {
        cond_subtract_3329(v)
    }

    fn barrett_reduce(v: Self) -> Self {
        barrett_reduce(v)
    }

    fn montgomery_multiply_by_constant(v: Self, c: i16) -> Self {
        montgomery_multiply_by_constant(v, c)
    }

    fn compress_1(v: Self) -> Self {
        compress_1(v)
    }

    fn compress<const COEFFICIENT_BITS: i32>(v: Self) -> Self {
        compress::<COEFFICIENT_BITS>(v)
    }

    fn decompress<const COEFFICIENT_BITS: i32>(v: Self) -> Self {
        decompress::<COEFFICIENT_BITS>(v)
    }

    fn ntt_layer_1_step(a: Self, zeta1: i16, zeta2: i16) -> Self {
        ntt_layer_1_step(a, zeta1, zeta2)
    }

    fn ntt_layer_2_step(a: Self, zeta: i16) -> Self {
        ntt_layer_2_step(a, zeta)
    }

    fn inv_ntt_layer_1_step(a: Self, zeta1: i16, zeta2: i16) -> Self {
        inv_ntt_layer_1_step(a, zeta1, zeta2)
    }

    fn inv_ntt_layer_2_step(a: Self, zeta: i16) -> Self {
        inv_ntt_layer_2_step(a, zeta)
    }

    fn ntt_multiply(lhs: &Self, rhs: &Self, zeta0: i16, zeta1: i16) -> Self {
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

    fn rej_sample(a: &[u8]) -> (usize, [i16; 8]) {
        rej_sample(a)
    }
}
