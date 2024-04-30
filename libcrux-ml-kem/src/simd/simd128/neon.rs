#![allow(non_camel_case_types)]
use core::arch::aarch64;

pub(super) type int16x4_t = aarch64::int16x4_t;
pub(super) type int32x2_t = aarch64::int32x2_t;
pub(super) type int32x4_t = aarch64::int32x4_t;
pub(super) type int64x2_t = aarch64::int64x2_t;
pub(super) type uint32x4_t = aarch64::uint32x4_t;
pub(super) type uint8x16_t = aarch64::uint8x16_t;

#[inline(always)]
pub(super) fn vdupq_n_s32(v: i32) -> int32x4_t {
    unsafe { aarch64::vdupq_n_s32(v) }
}

#[inline(always)]
pub(super) fn vdup_n_s32(v: i32) -> int32x2_t {
    unsafe { aarch64::vdup_n_s32(v) }
}

#[inline(always)]
pub(super) fn vdupq_n_s64(v: i64) -> int64x2_t {
    unsafe { aarch64::vdupq_n_s64(v) }
}

#[inline(always)]
pub(super) fn vst1q_s32(out: &mut [i32], v: int32x4_t) {
    debug_assert!(out.len() == 4);
    unsafe {
        aarch64::vst1q_s32(out.as_mut_ptr(), v);
    }
}

#[inline(always)]
pub(super) fn vst1q_s64(out: &mut [i64], v: int64x2_t) {
    debug_assert!(out.len() == 2);
    unsafe {
        aarch64::vst1q_s64(out.as_mut_ptr(), v);
    }
}

#[inline(always)]
pub(super) fn vld1q_s32(v: &[i32]) -> int32x4_t {
    debug_assert!(v.len() == 4);
    unsafe { aarch64::vld1q_s32(v.as_ptr()) }
}

#[inline(always)]
pub(super) fn vld1q_u8(v: &[u8]) -> uint8x16_t {
    debug_assert!(v.len() == 16);
    unsafe { aarch64::vld1q_u8(v.as_ptr()) }
}

#[inline(always)]
pub(super) fn vqtbl1q_u8(t: uint8x16_t, idx: uint8x16_t) -> uint8x16_t {
    unsafe { aarch64::vqtbl1q_u8(t, idx) }
}

#[inline(always)]
pub(super) fn vst1q_u8(out: &mut [u8], v: uint8x16_t) {
    unsafe { aarch64::vst1q_u8(out.as_mut_ptr(), v) }
}

#[inline(always)]
pub(super) fn veorq_s32(a: int32x4_t, b: int32x4_t) -> int32x4_t {
    unsafe { aarch64::veorq_s32(a, b) }
}

#[inline(always)]
pub(super) fn vaddq_s32(a: int32x4_t, b: int32x4_t) -> int32x4_t {
    unsafe { aarch64::vaddq_s32(a, b) }
}

#[inline(always)]
pub(super) fn vaddvq_s32(a: int32x4_t) -> i32 {
    unsafe { aarch64::vaddvq_s32(a) }
}

#[inline(always)]
pub(super) fn vadd_s32(a: int32x2_t, b: int32x2_t) -> int32x2_t {
    unsafe { aarch64::vadd_s32(a, b) }
}

#[inline(always)]
pub(super) fn vaddq_s64(a: int64x2_t, b: int64x2_t) -> int64x2_t {
    unsafe { aarch64::vaddq_s64(a, b) }
}

#[inline(always)]
pub(super) fn vsubq_s32(a: int32x4_t, b: int32x4_t) -> int32x4_t {
    unsafe { aarch64::vsubq_s32(a, b) }
}

#[inline(always)]
pub(super) fn vsub_s32(a: int32x2_t, b: int32x2_t) -> int32x2_t {
    unsafe { aarch64::vsub_s32(a, b) }
}

#[inline(always)]
pub(super) fn vmulq_n_s32(a: int32x4_t, b: i32) -> int32x4_t {
    unsafe { aarch64::vmulq_n_s32(a, b) }
}

#[inline(always)]
pub(super) fn vmulq_s32(a: int32x4_t, b: int32x4_t) -> int32x4_t {
    unsafe { aarch64::vmulq_s32(a, b) }
}

#[inline(always)]
pub(super) fn vmul_n_s32(a: int32x2_t, b: i32) -> int32x2_t {
    unsafe { aarch64::vmul_n_s32(a, b) }
}

#[inline(always)]
pub(super) fn vmull_n_s32(a: int32x2_t, b: i32) -> int64x2_t {
    unsafe { aarch64::vmull_n_s32(a, b) }
}

#[inline(always)]
pub(super) fn vmull_n_s16(a: int16x4_t, b: i16) -> int32x4_t {
    unsafe { aarch64::vmull_n_s16(a, b) }
}

#[inline(always)]
pub(super) fn vmull_high_n_s32(a: int32x4_t, b: i32) -> int64x2_t {
    unsafe { aarch64::vmull_high_n_s32(a, b) }
}

#[inline(always)]
pub(super) fn vandq_s32(a: int32x4_t, b: int32x4_t) -> int32x4_t {
    unsafe { aarch64::vandq_s32(a, b) }
}

#[inline(always)]
pub(super) fn vand_s32(a: int32x2_t, b: int32x2_t) -> int32x2_t {
    unsafe { aarch64::vand_s32(a, b) }
}

#[inline(always)]
pub(super) fn vshrq_n_s32<const N: i32>(a: int32x4_t) -> int32x4_t {
    unsafe { aarch64::vshrq_n_s32::<N>(a) }
}

#[inline(always)]
pub(super) fn vshrq_n_u32<const N: i32>(a: uint32x4_t) -> uint32x4_t {
    unsafe { aarch64::vshrq_n_u32::<N>(a) }
}

#[inline(always)]
pub(super) fn vshr_n_s32<const N: i32>(a: int32x2_t) -> int32x2_t {
    unsafe { aarch64::vshr_n_s32::<N>(a) }
}

#[inline(always)]
pub(super) fn vshrq_n_s64<const N: i32>(a: int64x2_t) -> int64x2_t {
    unsafe { aarch64::vshrq_n_s64::<N>(a) }
}

#[inline(always)]
pub(super) fn vshlq_n_s32<const N: i32>(a: int32x4_t) -> int32x4_t {
    unsafe { aarch64::vshlq_n_s32::<N>(a) }
}

#[inline(always)]
pub(super) fn vshlq_s32(a: int32x4_t, b: int32x4_t) -> int32x4_t {
    unsafe { aarch64::vshlq_s32(a, b) }
}

#[inline(always)]
pub(super) fn vcgeq_s32_reinterpreted(a: int32x4_t, b: int32x4_t) -> int32x4_t {
    unsafe { aarch64::vreinterpretq_s32_u32(aarch64::vcgeq_s32(a, b)) }
}

#[inline(always)]
pub(super) fn vget_low_s32(a: int32x4_t) -> int32x2_t {
    unsafe { aarch64::vget_low_s32(a) }
}

#[inline(always)]
pub(super) fn vget_high_s32(a: int32x4_t) -> int32x2_t {
    unsafe { aarch64::vget_high_s32(a) }
}

#[inline(always)]
pub(super) fn vmovn_s64(a: int64x2_t) -> int32x2_t {
    unsafe { aarch64::vmovn_s64(a) }
}

#[inline(always)]
pub(super) fn vmovl_s32(a: int32x2_t) -> int64x2_t {
    unsafe { aarch64::vmovl_s32(a) }
}

#[inline(always)]
pub(super) fn vreinterpret_s16_s32(a: int32x2_t) -> int16x4_t {
    unsafe { aarch64::vreinterpret_s16_s32(a) }
}

#[inline(always)]
pub(super) fn vreinterpretq_u8_s32(a: int32x4_t) -> uint8x16_t {
    unsafe { aarch64::vreinterpretq_u8_s32(a) }
}

#[inline(always)]
pub(super) fn vreinterpretq_u8_s64(a: int64x2_t) -> uint8x16_t {
    unsafe { aarch64::vreinterpretq_u8_s64(a) }
}

#[inline(always)]
pub(super) fn vreinterpretq_s64_s32(a: int32x4_t) -> int64x2_t {
    unsafe { aarch64::vreinterpretq_s64_s32(a) }
}

#[inline(always)]
pub(super) fn vreinterpretq_u32_s32(a: int32x4_t) -> uint32x4_t {
    unsafe { aarch64::vreinterpretq_u32_s32(a) }
}

#[inline(always)]
pub(super) fn vreinterpretq_s32_u32(a: uint32x4_t) -> int32x4_t {
    unsafe { aarch64::vreinterpretq_s32_u32(a) }
}

#[inline(always)]
pub(super) fn vmovn_s32(a: int32x4_t) -> int16x4_t {
    unsafe { aarch64::vmovn_s32(a) }
}

#[inline(always)]
pub(super) fn vmovl_s16(a: int16x4_t) -> int32x4_t {
    unsafe { aarch64::vmovl_s16(a) }
}

#[inline(always)]
pub(super) fn vcombine_s32(a: int32x2_t, b: int32x2_t) -> int32x4_t {
    unsafe { aarch64::vcombine_s32(a, b) }
}

#[inline(always)]
pub(super) fn vtrn1q_s32(a: int32x4_t, b: int32x4_t) -> int32x4_t {
    unsafe { aarch64::vtrn1q_s32(a, b) }
}

#[inline(always)]
pub(super) fn vtrn2q_s32(a: int32x4_t, b: int32x4_t) -> int32x4_t {
    unsafe { aarch64::vtrn2q_s32(a, b) }
}

#[inline(always)]
pub(super) fn vsliq_n_s32<const N: i32>(a: int32x4_t, b: int32x4_t) -> int32x4_t {
    unsafe { aarch64::vsliq_n_s32::<N>(a, b) }
}

#[inline(always)]
pub(super) fn vsliq_n_s64<const N: i32>(a: int64x2_t, b: int64x2_t) -> int64x2_t {
    unsafe { aarch64::vsliq_n_s64::<N>(a, b) }
}
