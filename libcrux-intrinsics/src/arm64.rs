#![allow(non_camel_case_types, unsafe_code)]
use core::arch::aarch64::*;

pub type _uint16x4_t = uint16x4_t;
pub type _int16x4_t = int16x4_t;
pub type _int16x8_t = int16x8_t;
pub type _uint8x16_t = uint8x16_t;
pub type _uint16x8_t = uint16x8_t;
pub type _uint32x4_t = uint32x4_t;
pub type _int32x4_t = int32x4_t;
pub type _uint64x2_t = uint64x2_t;
pub type _int64x2_t = int64x2_t;

#[inline(always)]
pub fn _vdupq_n_s16(i: i16) -> _int16x8_t {
    unsafe { vdupq_n_s16(i) }
}

#[inline(always)]
pub fn _vdupq_n_u64(i: u64) -> _uint64x2_t {
    unsafe { vdupq_n_u64(i) }
}

#[inline(always)]
pub fn _vst1q_s16(out: &mut [i16], v: _int16x8_t) {
    unsafe { vst1q_s16(out.as_mut_ptr(), v) }
}

#[inline(always)]
pub fn _vld1q_s16(array: &[i16]) -> _int16x8_t {
    unsafe { vld1q_s16(array.as_ptr()) }
}

#[inline(always)]
pub fn _vld1q_bytes_u64(array: &[u8]) -> _uint64x2_t {
    unsafe { vld1q_u64(array.as_ptr() as *const u64) }
}

#[inline(always)]
pub fn _vld1q_u64(array: &[u64]) -> _uint64x2_t {
    unsafe { vld1q_u64(array.as_ptr()) }
}

#[inline(always)]
pub fn _vst1q_u64(out: &mut [u64], v: _uint64x2_t) {
    unsafe { vst1q_u64(out.as_mut_ptr(), v) }
}

#[inline(always)]
pub fn _vst1q_bytes_u64(out: &mut [u8], v: _uint64x2_t) {
    unsafe { vst1q_u64(out.as_mut_ptr() as *mut u64, v) }
}

#[inline(always)]
pub fn _vaddq_s16(lhs: _int16x8_t, rhs: _int16x8_t) -> _int16x8_t {
    unsafe { vaddq_s16(lhs, rhs) }
}

#[inline(always)]
pub fn _vsubq_s16(lhs: _int16x8_t, rhs: _int16x8_t) -> _int16x8_t {
    unsafe { vsubq_s16(lhs, rhs) }
}

#[inline(always)]
pub fn _vmulq_n_s16(v: _int16x8_t, c: i16) -> _int16x8_t {
    unsafe { vmulq_n_s16(v, c) }
}

#[inline(always)]
pub fn _vmulq_n_u16(v: _uint16x8_t, c: u16) -> _uint16x8_t {
    unsafe { vmulq_n_u16(v, c) }
}

#[inline(always)]
pub fn _vshrq_n_s16<const SHIFT_BY: i32>(v: _int16x8_t) -> _int16x8_t {
    unsafe { vshrq_n_s16::<SHIFT_BY>(v) }
}

#[inline(always)]
pub fn _vshrq_n_u16<const SHIFT_BY: i32>(v: _uint16x8_t) -> _uint16x8_t {
    unsafe { vshrq_n_u16::<SHIFT_BY>(v) }
}

#[inline(always)]
pub fn _vshrq_n_u64<const SHIFT_BY: i32>(v: _uint64x2_t) -> _uint64x2_t {
    unsafe { vshrq_n_u64::<SHIFT_BY>(v) }
}

#[inline(always)]
pub fn _vshlq_n_u64<const SHIFT_BY: i32>(v: _uint64x2_t) -> _uint64x2_t {
    unsafe { vshlq_n_u64::<SHIFT_BY>(v) }
}

#[inline(always)]
pub fn _vshlq_n_s16<const SHIFT_BY: i32>(v: _int16x8_t) -> _int16x8_t {
    unsafe { vshlq_n_s16::<SHIFT_BY>(v) }
}

#[inline(always)]
pub fn _vshlq_n_u32<const SHIFT_BY: i32>(v: _uint32x4_t) -> _uint32x4_t {
    unsafe { vshlq_n_u32::<SHIFT_BY>(v) }
}
#[inline(always)]
pub fn _vqdmulhq_n_s16(k: _int16x8_t, b: i16) -> _int16x8_t {
    unsafe { vqdmulhq_n_s16(k, b) }
}
#[inline(always)]
pub fn _vqdmulhq_s16(v: _int16x8_t, c: _int16x8_t) -> _int16x8_t {
    unsafe { vqdmulhq_s16(v, c) }
}
#[inline(always)]
pub fn _vcgeq_s16(v: _int16x8_t, c: _int16x8_t) -> _uint16x8_t {
    unsafe { vcgeq_s16(v, c) }
}
#[inline(always)]
pub fn _vandq_s16(a: _int16x8_t, b: _int16x8_t) -> _int16x8_t {
    unsafe { vandq_s16(a, b) }
}

#[inline(always)]
pub fn _vbicq_u64(a: _uint64x2_t, b: _uint64x2_t) -> _uint64x2_t {
    unsafe { vbicq_u64(a, b) }
}

#[inline(always)]
pub fn _vreinterpretq_s16_u16(m0: _uint16x8_t) -> _int16x8_t {
    unsafe { vreinterpretq_s16_u16(m0) }
}
#[inline(always)]
pub fn _vreinterpretq_u16_s16(m0: _int16x8_t) -> _uint16x8_t {
    unsafe { vreinterpretq_u16_s16(m0) }
}
#[inline(always)]
pub fn _vmulq_s16(v: _int16x8_t, c: _int16x8_t) -> _int16x8_t {
    unsafe { vmulq_s16(v, c) }
}

#[inline(always)]
pub fn _veorq_s16(mask: _int16x8_t, shifted: _int16x8_t) -> _int16x8_t {
    unsafe { veorq_s16(mask, shifted) }
}

#[inline(always)]
pub fn _veorq_u64(mask: _uint64x2_t, shifted: _uint64x2_t) -> _uint64x2_t {
    unsafe { veorq_u64(mask, shifted) }
}

#[inline(always)]
pub fn _vdupq_n_u32(value: u32) -> _uint32x4_t {
    unsafe { vdupq_n_u32(value) }
}
#[inline(always)]
pub fn _vaddq_u32(compressed: _uint32x4_t, half: _uint32x4_t) -> _uint32x4_t {
    unsafe { vaddq_u32(compressed, half) }
}
#[inline(always)]
pub fn _vreinterpretq_s32_u32(compressed: _uint32x4_t) -> _int32x4_t {
    unsafe { vreinterpretq_s32_u32(compressed) }
}
#[inline(always)]
pub fn _vqdmulhq_n_s32(a: _int32x4_t, b: i32) -> _int32x4_t {
    unsafe { vqdmulhq_n_s32(a, b) }
}

#[inline(always)]
pub fn _vreinterpretq_u32_s32(a: _int32x4_t) -> _uint32x4_t {
    unsafe { vreinterpretq_u32_s32(a) }
}

#[inline(always)]
pub fn _vshrq_n_u32<const N: i32>(a: _uint32x4_t) -> _uint32x4_t {
    unsafe { vshrq_n_u32::<N>(a) }
}
#[inline(always)]
pub fn _vandq_u32(a: _uint32x4_t, b: _uint32x4_t) -> _uint32x4_t {
    unsafe { vandq_u32(a, b) }
}
#[inline(always)]
pub fn _vreinterpretq_u32_s16(a: _int16x8_t) -> _uint32x4_t {
    unsafe { vreinterpretq_u32_s16(a) }
}
#[inline(always)]
pub fn _vreinterpretq_s16_u32(a: _uint32x4_t) -> _int16x8_t {
    unsafe { vreinterpretq_s16_u32(a) }
}
#[inline(always)]
pub fn _vtrn1q_s16(a: _int16x8_t, b: _int16x8_t) -> _int16x8_t {
    unsafe { vtrn1q_s16(a, b) }
}
#[inline(always)]
pub fn _vtrn2q_s16(a: _int16x8_t, b: _int16x8_t) -> _int16x8_t {
    unsafe { vtrn2q_s16(a, b) }
}
#[inline(always)]
pub fn _vmulq_n_u32(a: _uint32x4_t, b: u32) -> _uint32x4_t {
    unsafe { vmulq_n_u32(a, b) }
}

#[inline(always)]
pub fn _vtrn1q_s32(a: _int32x4_t, b: _int32x4_t) -> _int32x4_t {
    unsafe { vtrn1q_s32(a, b) }
}
#[inline(always)]
pub fn _vreinterpretq_s16_s32(a: _int32x4_t) -> _int16x8_t {
    unsafe { vreinterpretq_s16_s32(a) }
}
#[inline(always)]
pub fn _vreinterpretq_s32_s16(a: _int16x8_t) -> _int32x4_t {
    unsafe { vreinterpretq_s32_s16(a) }
}

#[inline(always)]
pub fn _vtrn2q_s32(a: _int32x4_t, b: _int32x4_t) -> _int32x4_t {
    unsafe { vtrn2q_s32(a, b) }
}
#[inline(always)]
pub fn _vtrn1q_s64(a: _int64x2_t, b: _int64x2_t) -> _int64x2_t {
    unsafe { vtrn1q_s64(a, b) }
}

#[inline(always)]
pub fn _vtrn1q_u64(a: _uint64x2_t, b: _uint64x2_t) -> _uint64x2_t {
    unsafe { vtrn1q_u64(a, b) }
}

#[inline(always)]
pub fn _vreinterpretq_s16_s64(a: _int64x2_t) -> _int16x8_t {
    unsafe { vreinterpretq_s16_s64(a) }
}
#[inline(always)]
pub fn _vreinterpretq_s64_s16(a: _int16x8_t) -> _int64x2_t {
    unsafe { vreinterpretq_s64_s16(a) }
}
#[inline(always)]
pub fn _vtrn2q_s64(a: _int64x2_t, b: _int64x2_t) -> _int64x2_t {
    unsafe { vtrn2q_s64(a, b) }
}

#[inline(always)]
pub fn _vtrn2q_u64(a: _uint64x2_t, b: _uint64x2_t) -> _uint64x2_t {
    unsafe { vtrn2q_u64(a, b) }
}

#[inline(always)]
pub fn _vmull_s16(a: _int16x4_t, b: _int16x4_t) -> _int32x4_t {
    unsafe { vmull_s16(a, b) }
}
#[inline(always)]
pub fn _vget_low_s16(a: _int16x8_t) -> _int16x4_t {
    unsafe { vget_low_s16(a) }
}
#[inline(always)]
pub fn _vmull_high_s16(a: _int16x8_t, b: _int16x8_t) -> _int32x4_t {
    unsafe { vmull_high_s16(a, b) }
}
#[inline(always)]
pub fn _vmlal_s16(a: _int32x4_t, b: _int16x4_t, c: _int16x4_t) -> _int32x4_t {
    unsafe { vmlal_s16(a, b, c) }
}
#[inline(always)]
pub fn _vmlal_high_s16(a: _int32x4_t, b: _int16x8_t, c: _int16x8_t) -> _int32x4_t {
    unsafe { vmlal_high_s16(a, b, c) }
}
#[inline(always)]
pub fn _vld1q_u8(ptr: &[u8]) -> _uint8x16_t {
    unsafe { vld1q_u8(ptr.as_ptr()) }
}
#[inline(always)]
pub fn _vreinterpretq_u8_s16(a: _int16x8_t) -> _uint8x16_t {
    unsafe { vreinterpretq_u8_s16(a) }
}
#[inline(always)]
pub fn _vqtbl1q_u8(t: _uint8x16_t, idx: _uint8x16_t) -> _uint8x16_t {
    unsafe { vqtbl1q_u8(t, idx) }
}
#[inline(always)]
pub fn _vreinterpretq_s16_u8(a: _uint8x16_t) -> _int16x8_t {
    unsafe { vreinterpretq_s16_u8(a) }
}
#[inline(always)]
pub fn _vshlq_s16(a: _int16x8_t, b: _int16x8_t) -> _int16x8_t {
    unsafe { vshlq_s16(a, b) }
}
#[inline(always)]
pub fn _vshlq_u16(a: _uint16x8_t, b: _int16x8_t) -> _uint16x8_t {
    unsafe { vshlq_u16(a, b) }
}
#[inline(always)]
pub fn _vaddv_u16(a: _uint16x4_t) -> u16 {
    unsafe { vaddv_u16(a) }
}
#[inline(always)]
pub fn _vget_low_u16(a: _uint16x8_t) -> _uint16x4_t {
    unsafe { vget_low_u16(a) }
}
#[inline(always)]
pub fn _vget_high_u16(a: _uint16x8_t) -> _uint16x4_t {
    unsafe { vget_high_u16(a) }
}
#[inline(always)]
pub fn _vaddvq_s16(a: _int16x8_t) -> i16 {
    unsafe { vaddvq_s16(a) }
}

#[inline(always)]
pub fn _vsliq_n_s32<const N: i32>(a: _int32x4_t, b: _int32x4_t) -> _int32x4_t {
    unsafe { vsliq_n_s32::<N>(a, b) }
}

#[inline(always)]
pub fn _vreinterpretq_s64_s32(a: _int32x4_t) -> _int64x2_t {
    unsafe { vreinterpretq_s64_s32(a) }
}

#[inline(always)]
pub fn _vsliq_n_s64<const N: i32>(a: _int64x2_t, b: _int64x2_t) -> _int64x2_t {
    unsafe { vsliq_n_s64::<N>(a, b) }
}

#[inline(always)]
pub fn _vreinterpretq_u8_s64(a: _int64x2_t) -> _uint8x16_t {
    unsafe { vreinterpretq_u8_s64(a) }
}

#[inline(always)]
pub fn _vst1q_u8(out: &mut [u8], v: _uint8x16_t) {
    unsafe { vst1q_u8(out.as_mut_ptr(), v) }
}
#[inline(always)]
pub fn _vdupq_n_u16(value: u16) -> _uint16x8_t {
    unsafe { vdupq_n_u16(value) }
}
#[inline(always)]
pub fn _vandq_u16(a: _uint16x8_t, b: _uint16x8_t) -> _uint16x8_t {
    unsafe { vandq_u16(a, b) }
}
#[inline(always)]
pub fn _vreinterpretq_u16_u8(a: _uint8x16_t) -> _uint16x8_t {
    unsafe { vreinterpretq_u16_u8(a) }
}
#[inline(always)]
pub fn _vld1q_u16(ptr: &[u16]) -> _uint16x8_t {
    unsafe { vld1q_u16(ptr.as_ptr()) }
}
#[inline(always)]
pub fn _vcleq_s16(a: _int16x8_t, b: _int16x8_t) -> _uint16x8_t {
    unsafe { vcleq_s16(a, b) }
}
#[inline(always)]
pub fn _vaddvq_u16(a: _uint16x8_t) -> u16 {
    unsafe { vaddvq_u16(a) }
}
