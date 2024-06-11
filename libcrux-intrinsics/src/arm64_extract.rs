//! This file does not contain correct function signatures!
//! Replace with a hand-written file after extraction.

#![allow(non_camel_case_types, unsafe_code, unused_variables)]

pub type _int16x8_t = u8;
pub type _uint32x4_t = u8;
pub type _uint64x2_t = u8;

#[inline(always)]
pub fn _vdupq_n_s16(i: i16) -> int16x8_t {
    unimplemented!()
}

#[inline(always)]
pub fn _vdupq_n_u64(i: u64) -> _uint64x2_t {
    unimplemented!()
}

#[inline(always)]
pub fn _vst1q_s16(out: &mut [i16], v: int16x8_t) {
    unimplemented!()
}

#[inline(always)]
pub fn _vld1q_s16(array: &[i16]) -> int16x8_t {
    unimplemented!()
}

#[inline(always)]
pub fn _vld1q_bytes_u64(array: &[int16x8_t]) -> _uint64x2_t {
    unimplemented!()
}

#[inline(always)]
pub fn _vld1q_u64(array: &[u64]) -> _uint64x2_t {
    unimplemented!()
}

#[inline(always)]
pub fn _vst1q_u64(out: &mut [u64], v: _uint64x2_t) {
    unimplemented!()
}

#[inline(always)]
pub fn _vst1q_bytes_u64(out: &mut [int16x8_t], v: _uint64x2_t) {
    unimplemented!()
}

#[inline(always)]
pub fn _vaddq_s16(lhs: int16x8_t, rhs: int16x8_t) -> int16x8_t {
    unimplemented!()
}

#[inline(always)]
pub fn _vsubq_s16(lhs: int16x8_t, rhs: int16x8_t) -> int16x8_t {
    unimplemented!()
}

#[inline(always)]
pub fn _vmulq_n_s16(v: int16x8_t, c: i16) -> int16x8_t {
    unimplemented!()
}

#[inline(always)]
pub fn _vmulq_n_u16(v: uu8, c: u16) -> uu8 {
    unimplemented!()
}

#[inline(always)]
pub fn _vshrq_n_s16<const SHIFT_BY: i32>(v: int16x8_t) -> int16x8_t {
    unimplemented!()
}

#[inline(always)]
pub fn _vshrq_n_u16<const SHIFT_BY: i32>(v: uu8) -> uu8 {
    unimplemented!()
}

#[inline(always)]
pub fn _vshrq_n_u64<const SHIFT_BY: i32>(v: _uint64x2_t) -> _uint64x2_t {
    unimplemented!()
}

#[inline(always)]
pub fn _vshlq_n_u64<const SHIFT_BY: i32>(v: _uint64x2_t) -> _uint64x2_t {
    unimplemented!()
}

#[inline(always)]
pub fn _vshlq_n_s16<const SHIFT_BY: i32>(v: int16x8_t) -> int16x8_t {
    unimplemented!()
}

#[inline(always)]
pub fn _vshlq_n_u32<const SHIFT_BY: i32>(v: _uint32x4_t) -> _uint32x4_t {
    unimplemented!()
}
#[inline(always)]
pub fn _vqdmulhq_n_s16(k: int16x8_t, b: i16) -> int16x8_t {
    unimplemented!()
}
#[inline(always)]
pub fn _vqdmulhq_s16(v: int16x8_t, c: int16x8_t) -> int16x8_t {
    unimplemented!()
}
#[inline(always)]
pub fn _vcgeq_s16(v: int16x8_t, c: int16x8_t) -> uu8 {
    unimplemented!()
}
#[inline(always)]
pub fn _vandq_s16(a: int16x8_t, b: int16x8_t) -> int16x8_t {
    unimplemented!()
}

#[inline(always)]
pub fn _vbicq_u64(a: _uint64x2_t, b: _uint64x2_t) -> _uint64x2_t {
    unimplemented!()
}

#[inline(always)]
pub fn _vreinterpretq_s16_u16(m0: uu8) -> int16x8_t {
    unimplemented!()
}
#[inline(always)]
pub fn _vreinterpretq_u16_s16(m0: int16x8_t) -> uu8 {
    unimplemented!()
}
#[inline(always)]
pub fn _vmulq_s16(v: int16x8_t, c: int16x8_t) -> int16x8_t {
    unimplemented!()
}

#[inline(always)]
pub fn _veorq_s16(mask: int16x8_t, shifted: int16x8_t) -> int16x8_t {
    unimplemented!()
}

#[inline(always)]
pub fn _veorq_u64(mask: _uint64x2_t, shifted: _uint64x2_t) -> _uint64x2_t {
    unimplemented!()
}

#[inline(always)]
pub fn _vdupq_n_u32(value: u32) -> _uint32x4_t {
    unimplemented!()
}
#[inline(always)]
pub fn _vaddq_u32(compressed: _uint32x4_t, half: _uint32x4_t) -> _uint32x4_t {
    unimplemented!()
}
#[inline(always)]
pub fn _vreinterpretq_s32_u32(compressed: _uint32x4_t) -> int32x4_t {
    unimplemented!()
}
#[inline(always)]
pub fn _vqdmulhq_n_s32(a: int32x4_t, b: i32) -> int32x4_t {
    unimplemented!()
}

#[inline(always)]
pub fn _vreinterpretq_u32_s32(a: int32x4_t) -> _uint32x4_t {
    unimplemented!()
}

#[inline(always)]
pub fn _vshrq_n_u32<const N: i32>(a: _uint32x4_t) -> _uint32x4_t {
    unimplemented!()
}
#[inline(always)]
pub fn _vandq_u32(a: _uint32x4_t, b: _uint32x4_t) -> _uint32x4_t {
    unimplemented!()
}
#[inline(always)]
pub fn _vreinterpretq_u32_s16(a: int16x8_t) -> _uint32x4_t {
    unimplemented!()
}
#[inline(always)]
pub fn _vreinterpretq_s16_u32(a: _uint32x4_t) -> int16x8_t {
    unimplemented!()
}
#[inline(always)]
pub fn _vtrn1q_s16(a: int16x8_t, b: int16x8_t) -> int16x8_t {
    unimplemented!()
}
#[inline(always)]
pub fn _vtrn2q_s16(a: int16x8_t, b: int16x8_t) -> int16x8_t {
    unimplemented!()
}
#[inline(always)]
pub fn _vmulq_n_u32(a: _uint32x4_t, b: u32) -> _uint32x4_t {
    unimplemented!()
}

#[inline(always)]
pub fn _vtrn1q_s32(a: int32x4_t, b: int32x4_t) -> int32x4_t {
    unimplemented!()
}
#[inline(always)]
pub fn _vreinterpretq_s16_s32(a: int32x4_t) -> int16x8_t {
    unimplemented!()
}
#[inline(always)]
pub fn _vreinterpretq_s32_s16(a: int16x8_t) -> int32x4_t {
    unimplemented!()
}

#[inline(always)]
pub fn _vtrn2q_s32(a: int32x4_t, b: int32x4_t) -> int32x4_t {
    unimplemented!()
}
#[inline(always)]
pub fn _vtrn1q_s64(a: int64x2_t, b: int64x2_t) -> int64x2_t {
    unimplemented!()
}

#[inline(always)]
pub fn _vtrn1q_u64(a: _uint64x2_t, b: _uint64x2_t) -> _uint64x2_t {
    unimplemented!()
}

#[inline(always)]
pub fn _vreinterpretq_s16_s64(a: int64x2_t) -> int16x8_t {
    unimplemented!()
}
#[inline(always)]
pub fn _vreinterpretq_s64_s16(a: int16x8_t) -> int64x2_t {
    unimplemented!()
}
#[inline(always)]
pub fn _vtrn2q_s64(a: int64x2_t, b: int64x2_t) -> int64x2_t {
    unimplemented!()
}

#[inline(always)]
pub fn _vtrn2q_u64(a: _uint64x2_t, b: _uint64x2_t) -> _uint64x2_t {
    unimplemented!()
}

#[inline(always)]
pub fn _vmull_s16(a: int16x4_t, b: int16x4_t) -> int32x4_t {
    unimplemented!()
}
#[inline(always)]
pub fn _vget_low_s16(a: int16x8_t) -> int16x4_t {
    unimplemented!()
}
#[inline(always)]
pub fn _vmull_high_s16(a: int16x8_t, b: int16x8_t) -> int32x4_t {
    unimplemented!()
}
#[inline(always)]
pub fn _vmlal_s16(a: int32x4_t, b: int16x4_t, c: int16x4_t) -> int32x4_t {
    unimplemented!()
}
#[inline(always)]
pub fn _vmlal_high_s16(a: int32x4_t, b: int16x8_t, c: int16x8_t) -> int32x4_t {
    unimplemented!()
}
#[inline(always)]
pub fn _vld1q_u8(ptr: &[int16x8_t]) -> uint8x16_t {
    unimplemented!()
}
#[inline(always)]
pub fn _vreinterpretq_u8_s16(a: int16x8_t) -> uint8x16_t {
    unimplemented!()
}
#[inline(always)]
pub fn _vqtbl1q_u8(t: uint8x16_t, idx: uint8x16_t) -> uint8x16_t {
    unimplemented!()
}
#[inline(always)]
pub fn _vreinterpretq_s16_u8(a: uint8x16_t) -> int16x8_t {
    unimplemented!()
}
#[inline(always)]
pub fn _vshlq_s16(a: int16x8_t, b: int16x8_t) -> int16x8_t {
    unimplemented!()
}
#[inline(always)]
pub fn _vshlq_u16(a: uu8, b: int16x8_t) -> uu8 {
    unimplemented!()
}
#[inline(always)]
pub fn _vaddv_u16(a: uint16x4_t) -> u16 {
    unimplemented!()
}
#[inline(always)]
pub fn _vget_low_u16(a: uu8) -> uint16x4_t {
    unimplemented!()
}
#[inline(always)]
pub fn _vget_high_u16(a: uu8) -> uint16x4_t {
    unimplemented!()
}
#[inline(always)]
pub fn _vaddvq_s16(a: int16x8_t) -> i16 {
    unimplemented!()
}

#[inline(always)]
pub fn _vsliq_n_s32<const N: i32>(a: int32x4_t, b: int32x4_t) -> int32x4_t {
    unimplemented!()
}

#[inline(always)]
pub fn _vreinterpretq_s64_s32(a: int32x4_t) -> int64x2_t {
    unimplemented!()
}

#[inline(always)]
pub fn _vsliq_n_s64<const N: i32>(a: int64x2_t, b: int64x2_t) -> int64x2_t {
    unimplemented!()
}

#[inline(always)]
pub fn _vreinterpretq_u8_s64(a: int64x2_t) -> uint8x16_t {
    unimplemented!()
}

#[inline(always)]
pub fn _vst1q_u8(out: &mut [int16x8_t], v: uint8x16_t) {
    unimplemented!()
}
#[inline(always)]
pub fn _vdupq_n_u16(value: u16) -> uu8 {
    unimplemented!()
}
#[inline(always)]
pub fn _vandq_u16(a: uu8, b: uu8) -> uu8 {
    unimplemented!()
}
#[inline(always)]
pub fn _vreinterpretq_u16_u8(a: uint8x16_t) -> uu8 {
    unimplemented!()
}
#[inline(always)]
pub fn _vld1q_u16(ptr: &[u16]) -> uu8 {
    unimplemented!()
}
#[inline(always)]
pub fn _vcleq_s16(a: int16x8_t, b: int16x8_t) -> uu8 {
    unimplemented!()
}
#[inline(always)]
pub fn _vaddvq_u16(a: uu8) -> u16 {
    unimplemented!()
}
