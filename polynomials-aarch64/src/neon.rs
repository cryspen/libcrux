#![allow(non_camel_case_types)]
pub(crate) use core::arch::aarch64::*;

#[inline(always)]
pub(crate) fn _vdupq_n_s16(i: i16) -> int16x8_t {
    unsafe { vdupq_n_s16(i) }
}

#[inline(always)]
pub(crate) fn _vst1q_s16(out: &mut [i16], v: int16x8_t) {
    unsafe { vst1q_s16(out.as_mut_ptr() as *mut i16, v) }
}

#[inline(always)]
pub(crate) fn _vld1q_s16(array: &[i16]) -> int16x8_t {
    unsafe { vld1q_s16(array.as_ptr() as *const i16) }
}

#[inline(always)]
pub(crate) fn _vaddq_s16(lhs: int16x8_t, rhs: int16x8_t) -> int16x8_t {
    unsafe { vaddq_s16(lhs, rhs) }
}

#[inline(always)]
pub(crate) fn _vsubq_s16(lhs: int16x8_t, rhs: int16x8_t) -> int16x8_t {
    unsafe { vsubq_s16(lhs, rhs) }
}

#[inline(always)]
pub(crate) fn _vmulq_n_s16(v: int16x8_t, c: i16) -> int16x8_t {
    unsafe { vmulq_n_s16(v, c) }
}

#[inline(always)]
pub(crate) fn _vmulq_n_u16(v: uint16x8_t, c: u16) -> uint16x8_t {
    unsafe { vmulq_n_u16(v, c) }
}

#[inline(always)]
pub(crate) fn _vshrq_n_s16<const SHIFT_BY: i32>(v: int16x8_t) -> int16x8_t {
    unsafe { vshrq_n_s16::<SHIFT_BY>(v) }
}

#[inline(always)]
pub(crate) fn _vshrq_n_u16<const SHIFT_BY: i32>(v: uint16x8_t) -> uint16x8_t {
    unsafe { vshrq_n_u16::<SHIFT_BY>(v) }
}

#[inline(always)]
pub(crate) fn _vshlq_n_s16<const SHIFT_BY: i32>(v: int16x8_t) -> int16x8_t {
    unsafe { vshlq_n_s16::<SHIFT_BY>(v) }
}

#[inline(always)]
pub(crate) fn _vshlq_n_u32<const SHIFT_BY: i32>(v: uint32x4_t) -> uint32x4_t {
    unsafe { vshlq_n_u32::<SHIFT_BY>(v) }
}
#[inline(always)]
pub(crate) fn _vqdmulhq_n_s16(k: int16x8_t, b: i16) -> int16x8_t {
    unsafe { vqdmulhq_n_s16(k, b) }
}
#[inline(always)]
pub(crate) fn _vqdmulhq_s16(v: int16x8_t, c: int16x8_t) -> int16x8_t {
    unsafe { vqdmulhq_s16(v, c) }
}
#[inline(always)]
pub(crate) fn _vcgeq_s16(v: int16x8_t, c: int16x8_t) -> uint16x8_t {
    unsafe { vcgeq_s16(v, c) }
}
#[inline(always)]
pub(crate) fn _vandq_s16(a: int16x8_t, b: int16x8_t) -> int16x8_t {
    unsafe { vandq_s16(a, b) }
}
#[inline(always)]
pub(crate) fn _vreinterpretq_s16_u16(m0: uint16x8_t) -> int16x8_t {
    unsafe { vreinterpretq_s16_u16(m0) }
}
#[inline(always)]
pub(crate) fn _vreinterpretq_u16_s16(m0: int16x8_t) -> uint16x8_t {
    unsafe { vreinterpretq_u16_s16(m0) }
}
#[inline(always)]
pub(crate) fn _vmulq_s16(v: int16x8_t, c: int16x8_t) -> int16x8_t {
    unsafe { vmulq_s16(v, c) }
}
#[inline(always)]
pub(crate) fn _veorq_s16(mask: int16x8_t, shifted: int16x8_t) -> int16x8_t {
    unsafe { veorq_s16(mask, shifted) }
}
#[inline(always)]
pub(crate) fn _vdupq_n_u32(value: u32) -> uint32x4_t {
    unsafe { vdupq_n_u32(value) }
}
#[inline(always)]
pub(crate) fn _vaddq_u32(compressed: uint32x4_t, half: uint32x4_t) -> uint32x4_t {
    unsafe { vaddq_u32(compressed, half) }
}
#[inline(always)]
pub(crate) fn _vreinterpretq_s32_u32(compressed: uint32x4_t) -> int32x4_t {
    unsafe { vreinterpretq_s32_u32(compressed) }
}
#[inline(always)]
pub(crate) fn _vqdmulhq_n_s32(a: int32x4_t, b: i32) -> int32x4_t {
    unsafe { vqdmulhq_n_s32(a, b) }
}

#[inline(always)]
pub(super) fn _vreinterpretq_u32_s32(a: int32x4_t) -> uint32x4_t {
    unsafe { vreinterpretq_u32_s32(a) }
}

#[inline(always)]
pub(super) fn _vshrq_n_u32<const N: i32>(a: uint32x4_t) -> uint32x4_t {
    unsafe { vshrq_n_u32::<N>(a) }
}
#[inline(always)]
pub(crate) fn _vandq_u32(a: uint32x4_t, b: uint32x4_t) -> uint32x4_t {
    unsafe { vandq_u32(a, b) }
}
#[inline(always)]
pub(crate) fn _vreinterpretq_u32_s16(a: int16x8_t) -> uint32x4_t {
    unsafe { vreinterpretq_u32_s16(a) }
}
#[inline(always)]
pub(crate) fn _vreinterpretq_s16_u32(a: uint32x4_t) -> int16x8_t {
    unsafe { vreinterpretq_s16_u32(a) }
}
#[inline(always)]
pub(crate) fn _vtrn1q_s16(a: int16x8_t, b: int16x8_t) -> int16x8_t {
    unsafe { vtrn1q_s16(a, b) }
}
#[inline(always)]
pub(crate) fn _vtrn2q_s16(a: int16x8_t, b: int16x8_t) -> int16x8_t {
    unsafe { vtrn2q_s16(a, b) }
}
#[inline(always)]
pub(crate) fn _vmulq_n_u32(a: uint32x4_t, b: u32) -> uint32x4_t {
    unsafe { vmulq_n_u32(a, b) }
}

#[inline(always)]
pub(super) fn _vtrn1q_s32(a: int32x4_t, b: int32x4_t) -> int32x4_t {
    unsafe { vtrn1q_s32(a, b) }
}
#[inline(always)]
pub(crate) fn _vreinterpretq_s16_s32(a: int32x4_t) -> int16x8_t {
    unsafe { vreinterpretq_s16_s32(a) }
}
#[inline(always)]
pub(crate) fn _vreinterpretq_s32_s16(a: int16x8_t) -> int32x4_t {
    unsafe { vreinterpretq_s32_s16(a) }
}

#[inline(always)]
pub(super) fn _vtrn2q_s32(a: int32x4_t, b: int32x4_t) -> int32x4_t {
    unsafe { vtrn2q_s32(a, b) }
}
#[inline(always)]
pub(crate) fn _vtrn1q_s64(a: int64x2_t, b: int64x2_t) -> int64x2_t {
    unsafe { vtrn1q_s64(a, b) }
}
#[inline(always)]
pub(crate) fn _vreinterpretq_s16_s64(a: int64x2_t) -> int16x8_t {
    unsafe { vreinterpretq_s16_s64(a) }
}
#[inline(always)]
pub(crate) fn _vreinterpretq_s64_s16(a: int16x8_t) -> int64x2_t {
    unsafe { vreinterpretq_s64_s16(a) }
}
#[inline(always)]
pub(crate) fn _vtrn2q_s64(a: int64x2_t, b: int64x2_t) -> int64x2_t {
    unsafe { vtrn2q_s64(a, b) }
}
#[inline(always)]
pub(crate) fn _vmull_s16(a: int16x4_t, b: int16x4_t) -> int32x4_t {
    unsafe { vmull_s16(a, b) }
}
#[inline(always)]
pub(crate) fn _vget_low_s16(a: int16x8_t) -> int16x4_t {
    unsafe { vget_low_s16(a) }
}
#[inline(always)]
pub(crate) fn _vmull_high_s16(a: int16x8_t, b: int16x8_t) -> int32x4_t {
    unsafe { vmull_high_s16(a, b) }
}
#[inline(always)]
pub(crate) fn _vmlal_s16(a: int32x4_t, b: int16x4_t, c: int16x4_t) -> int32x4_t {
    unsafe { vmlal_s16(a, b, c) }
}
#[inline(always)]
pub(crate) fn _vmlal_high_s16(a: int32x4_t, b: int16x8_t, c: int16x8_t) -> int32x4_t {
    unsafe { vmlal_high_s16(a, b, c) }
}
#[inline(always)]
pub(crate) fn _vld1q_u8(ptr: &[u8]) -> uint8x16_t {
    unsafe { vld1q_u8(ptr.as_ptr()) }
}
#[inline(always)]
pub(crate) fn _vreinterpretq_u8_s16(a: int16x8_t) -> uint8x16_t {
    unsafe { vreinterpretq_u8_s16(a) }
}
#[inline(always)]
pub(crate) fn _vqtbl1q_u8(t: uint8x16_t, idx: uint8x16_t) -> uint8x16_t {
    unsafe { vqtbl1q_u8(t, idx) }
}
#[inline(always)]
pub(crate) fn _vreinterpretq_s16_u8(a: uint8x16_t) -> int16x8_t {
    unsafe { vreinterpretq_s16_u8(a) }
}
#[inline(always)]
pub(crate) fn _vshlq_s16(a: int16x8_t, b: int16x8_t) -> int16x8_t {
    unsafe { vshlq_s16(a, b) }
}
#[inline(always)]
pub(crate) fn _vshlq_u16(a: uint16x8_t, b: int16x8_t) -> uint16x8_t {
    unsafe { vshlq_u16(a, b) }
}
#[inline(always)]
pub(crate) fn _vaddv_u16(a: uint16x4_t) -> u16 {
    unsafe { vaddv_u16(a) }
}
#[inline(always)]
pub(crate) fn _vget_low_u16(a: uint16x8_t) -> uint16x4_t {
    unsafe { vget_low_u16(a) }
}
#[inline(always)]
pub(crate) fn _vget_high_u16(a: uint16x8_t) -> uint16x4_t {
    unsafe { vget_high_u16(a) }
}
#[inline(always)]
pub(crate) fn _vaddvq_s16(a: int16x8_t) -> i16 {
    unsafe { vaddvq_s16(a) }
}

#[inline(always)]
pub(super) fn _vsliq_n_s32<const N: i32>(a: int32x4_t, b: int32x4_t) -> int32x4_t {
    unsafe { vsliq_n_s32::<N>(a, b) }
}

#[inline(always)]
pub(super) fn _vreinterpretq_s64_s32(a: int32x4_t) -> int64x2_t {
    unsafe { vreinterpretq_s64_s32(a) }
}

#[inline(always)]
pub(super) fn _vsliq_n_s64<const N: i32>(a: int64x2_t, b: int64x2_t) -> int64x2_t {
    unsafe { vsliq_n_s64::<N>(a, b) }
}

#[inline(always)]
pub(super) fn _vreinterpretq_u8_s64(a: int64x2_t) -> uint8x16_t {
    unsafe { vreinterpretq_u8_s64(a) }
}

#[inline(always)]
pub(super) fn _vst1q_u8(out: &mut [u8], v: uint8x16_t) {
    unsafe { vst1q_u8(out.as_mut_ptr(), v) }
}
#[inline(always)]
pub(crate) fn _vdupq_n_u16(value: u16) -> uint16x8_t {
    unsafe { vdupq_n_u16(value) }
}
#[inline(always)]
pub(crate) fn _vandq_u16(a: uint16x8_t, b: uint16x8_t) -> uint16x8_t {
    unsafe { vandq_u16(a, b) }
}
#[inline(always)]
pub(crate) fn _vreinterpretq_u16_u8(a: uint8x16_t) -> uint16x8_t {
    unsafe { vreinterpretq_u16_u8(a) }
}
#[inline(always)]
pub(crate) fn _vld1q_u16(ptr: &[u16]) -> uint16x8_t {
    unsafe { vld1q_u16(ptr.as_ptr()) }
}
#[inline(always)]
pub(crate) fn _vcleq_s16(a: int16x8_t, b: int16x8_t) -> uint16x8_t {
    unsafe { vcleq_s16(a, b) }
}
#[inline(always)]
pub(crate) fn _vaddvq_u16(a: uint16x8_t) -> u16 {
    unsafe { vaddvq_u16(a) }
}
