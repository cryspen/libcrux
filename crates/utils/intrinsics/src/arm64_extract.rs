//! Extraction-only stubs for ARM64 NEON intrinsic types and functions.
//!
//! Each NEON vector type is defined as a single-field struct with
//! `#[hax_lib::lean::replace(...)]` so the Lean backend directly emits the
//! correct `BitVec` width, and `#[hax_lib::fstar::replace(...)]` for F*.

#![allow(non_camel_case_types, unsafe_code, unused_variables)]

#[derive(Clone, Copy)]
#[hax_lib::lean::replace("abbrev _uint16x4_t := BitVec 64")]
#[hax_lib::fstar::replace(interface, "unfold type $:{_uint16x4_t} = bit_vec 64")]
pub struct _uint16x4_t(u8);

#[derive(Clone, Copy)]
#[hax_lib::lean::replace("abbrev _int16x4_t := BitVec 64")]
#[hax_lib::fstar::replace(interface, "unfold type $:{_int16x4_t} = bit_vec 64")]
pub struct _int16x4_t(u8);

#[derive(Clone, Copy)]
#[hax_lib::lean::replace("abbrev _int16x8_t := BitVec 128")]
#[hax_lib::fstar::replace(interface, "unfold type $:{_int16x8_t} = bit_vec 128")]
pub struct _int16x8_t(u8);

#[derive(Clone, Copy)]
#[hax_lib::lean::replace("abbrev _uint8x16_t := BitVec 128")]
#[hax_lib::fstar::replace(interface, "unfold type $:{_uint8x16_t} = bit_vec 128")]
pub struct _uint8x16_t(u8);

#[derive(Clone, Copy)]
#[hax_lib::lean::replace("abbrev _uint16x8_t := BitVec 128")]
#[hax_lib::fstar::replace(interface, "unfold type $:{_uint16x8_t} = bit_vec 128")]
pub struct _uint16x8_t(u8);

#[derive(Clone, Copy)]
#[hax_lib::lean::replace("abbrev _uint32x4_t := BitVec 128")]
#[hax_lib::fstar::replace(interface, "unfold type $:{_uint32x4_t} = bit_vec 128")]
pub struct _uint32x4_t(u8);

#[derive(Clone, Copy)]
#[hax_lib::lean::replace("abbrev _int32x4_t := BitVec 128")]
#[hax_lib::fstar::replace(interface, "unfold type $:{_int32x4_t} = bit_vec 128")]
pub struct _int32x4_t(u8);

#[derive(Clone, Copy)]
#[hax_lib::lean::replace("abbrev _uint64x2_t := BitVec 128")]
#[hax_lib::fstar::replace(interface, "unfold type $:{_uint64x2_t} = bit_vec 128")]
pub struct _uint64x2_t(u8);

#[derive(Clone, Copy)]
#[hax_lib::lean::replace("abbrev _int64x2_t := BitVec 128")]
#[hax_lib::fstar::replace(interface, "unfold type $:{_int64x2_t} = bit_vec 128")]
pub struct _int64x2_t(u8);

#[inline(always)]
#[hax_lib::lean::replace_body("sorry")]
pub fn _vdupq_n_s16(i: i16) -> _int16x8_t {
    unimplemented!()
}

#[inline(always)]
#[hax_lib::lean::replace_body("sorry")]
pub fn _vdupq_n_u64(i: u64) -> _uint64x2_t {
    unimplemented!()
}

#[inline(always)]
#[hax_lib::lean::replace_body("()")]
pub fn _vst1q_s16(out: &mut [i16], v: _int16x8_t) {
    unimplemented!()
}

#[inline(always)]
#[hax_lib::lean::replace_body("()")]
pub fn _vst1q_bytes(out: &mut [u8], v: _int16x8_t) {
    unimplemented!()
}

#[inline(always)]
#[hax_lib::lean::replace_body("sorry")]
pub fn _vld1q_bytes(bytes: &[u8]) -> _int16x8_t {
    unimplemented!()
}

#[inline(always)]
#[hax_lib::lean::replace_body("sorry")]
pub fn _vld1q_s16(array: &[i16]) -> _int16x8_t {
    unimplemented!()
}

#[inline(always)]
#[hax_lib::lean::replace_body("sorry")]
pub fn _vld1q_bytes_u64(array: &[u8]) -> _uint64x2_t {
    unimplemented!()
}

#[inline(always)]
#[hax_lib::lean::replace_body("sorry")]
pub fn _vld1q_u64(array: &[u64]) -> _uint64x2_t {
    unimplemented!()
}

#[inline(always)]
#[hax_lib::ensures(|()| future(out).len() == out.len())]
#[hax_lib::lean::replace_body("()")]
pub fn _vst1q_u64(out: &mut [u64], v: _uint64x2_t) {
    unimplemented!()
}

#[inline(always)]
#[hax_lib::ensures(|()| future(out).len() == out.len())]
#[hax_lib::lean::replace_body("()")]
pub fn _vst1q_bytes_u64(out: &mut [u8], v: _uint64x2_t) {
    unimplemented!()
}

#[inline(always)]
#[hax_lib::lean::replace_body("sorry")]
pub fn _vaddq_s16(lhs: _int16x8_t, rhs: _int16x8_t) -> _int16x8_t {
    unimplemented!()
}

#[inline(always)]
#[hax_lib::lean::replace_body("sorry")]
pub fn _vsubq_s16(lhs: _int16x8_t, rhs: _int16x8_t) -> _int16x8_t {
    unimplemented!()
}

#[inline(always)]
#[hax_lib::lean::replace_body("sorry")]
pub fn _vmulq_n_s16(v: _int16x8_t, c: i16) -> _int16x8_t {
    unimplemented!()
}

#[inline(always)]
#[hax_lib::lean::replace_body("sorry")]
pub fn _vmulq_n_u16(v: _uint16x8_t, c: u16) -> _uint16x8_t {
    unimplemented!()
}

#[inline(always)]
#[hax_lib::lean::replace_body("sorry")]
pub fn _vshrq_n_s16<const SHIFT_BY: i32>(v: _int16x8_t) -> _int16x8_t {
    unimplemented!()
}

#[inline(always)]
#[hax_lib::lean::replace_body("sorry")]
pub fn _vshrq_n_u16<const SHIFT_BY: i32>(v: _uint16x8_t) -> _uint16x8_t {
    unimplemented!()
}

#[inline(always)]
#[hax_lib::lean::replace_body("sorry")]
pub fn _vshrq_n_u64<const SHIFT_BY: i32>(v: _uint64x2_t) -> _uint64x2_t {
    unimplemented!()
}

#[inline(always)]
#[hax_lib::lean::replace_body("sorry")]
pub fn _vxarq_u64<const LEFT: i32, const RIGHT: i32>(
    a: _uint64x2_t,
    b: _uint64x2_t,
) -> _uint64x2_t {
    unimplemented!()
}

#[inline(always)]
#[hax_lib::lean::replace_body("sorry")]
pub fn _vshlq_n_u64<const SHIFT_BY: i32>(v: _uint64x2_t) -> _uint64x2_t {
    unimplemented!()
}

#[inline(always)]
#[hax_lib::lean::replace_body("sorry")]
pub fn _vshlq_n_s16<const SHIFT_BY: i32>(v: _int16x8_t) -> _int16x8_t {
    unimplemented!()
}

#[inline(always)]
#[hax_lib::lean::replace_body("sorry")]
pub fn _vshlq_n_u32<const SHIFT_BY: i32>(v: _uint32x4_t) -> _uint32x4_t {
    unimplemented!()
}
#[inline(always)]
#[hax_lib::lean::replace_body("sorry")]
pub fn _vqdmulhq_n_s16(k: _int16x8_t, b: i16) -> _int16x8_t {
    unimplemented!()
}
#[inline(always)]
#[hax_lib::lean::replace_body("sorry")]
pub fn _vqdmulhq_s16(v: _int16x8_t, c: _int16x8_t) -> _int16x8_t {
    unimplemented!()
}
#[inline(always)]
#[hax_lib::lean::replace_body("sorry")]
pub fn _vcgeq_s16(v: _int16x8_t, c: _int16x8_t) -> _uint16x8_t {
    unimplemented!()
}
#[inline(always)]
#[hax_lib::lean::replace_body("sorry")]
pub fn _vandq_s16(a: _int16x8_t, b: _int16x8_t) -> _int16x8_t {
    unimplemented!()
}

#[inline(always)]
#[hax_lib::lean::replace_body("sorry")]
pub fn _vbicq_u64(a: _uint64x2_t, b: _uint64x2_t) -> _uint64x2_t {
    unimplemented!()
}

#[inline(always)]
#[hax_lib::lean::replace_body("sorry")]
pub fn _vbcaxq_u64(a: _uint64x2_t, b: _uint64x2_t, c: _uint64x2_t) -> _uint64x2_t {
    unimplemented!()
}

#[inline(always)]
#[hax_lib::lean::replace_body("sorry")]
pub fn _vreinterpretq_s16_u16(m0: _uint16x8_t) -> _int16x8_t {
    unimplemented!()
}
#[inline(always)]
#[hax_lib::lean::replace_body("sorry")]
pub fn _vreinterpretq_u16_s16(m0: _int16x8_t) -> _uint16x8_t {
    unimplemented!()
}
#[inline(always)]
#[hax_lib::lean::replace_body("sorry")]
pub fn _vmulq_s16(v: _int16x8_t, c: _int16x8_t) -> _int16x8_t {
    unimplemented!()
}

#[inline(always)]
#[hax_lib::lean::replace_body("sorry")]
pub fn _veorq_s16(mask: _int16x8_t, shifted: _int16x8_t) -> _int16x8_t {
    unimplemented!()
}

#[inline(always)]
#[hax_lib::lean::replace_body("sorry")]
pub fn _veorq_u64(mask: _uint64x2_t, shifted: _uint64x2_t) -> _uint64x2_t {
    unimplemented!()
}

#[inline(always)]
#[hax_lib::lean::replace_body("sorry")]
pub fn _vrax1q_u64(a: _uint64x2_t, b: _uint64x2_t) -> _uint64x2_t {
    unimplemented!()
}

#[inline(always)]
#[hax_lib::lean::replace_body("sorry")]
pub fn _veor3q_u64(a: _uint64x2_t, b: _uint64x2_t, c: _uint64x2_t) -> _uint64x2_t {
    unimplemented!()
}

#[inline(always)]
#[hax_lib::lean::replace_body("sorry")]
pub fn _vdupq_n_u32(value: u32) -> _uint32x4_t {
    unimplemented!()
}
#[inline(always)]
#[hax_lib::lean::replace_body("sorry")]
pub fn _vaddq_u32(compressed: _uint32x4_t, half: _uint32x4_t) -> _uint32x4_t {
    unimplemented!()
}
#[inline(always)]
#[hax_lib::lean::replace_body("sorry")]
pub fn _vreinterpretq_s32_u32(compressed: _uint32x4_t) -> _int32x4_t {
    unimplemented!()
}
#[inline(always)]
#[hax_lib::lean::replace_body("sorry")]
pub fn _vqdmulhq_n_s32(a: _int32x4_t, b: i32) -> _int32x4_t {
    unimplemented!()
}

#[inline(always)]
#[hax_lib::lean::replace_body("sorry")]
pub fn _vreinterpretq_u32_s32(a: _int32x4_t) -> _uint32x4_t {
    unimplemented!()
}

#[inline(always)]
#[hax_lib::lean::replace_body("sorry")]
pub fn _vshrq_n_u32<const N: i32>(a: _uint32x4_t) -> _uint32x4_t {
    unimplemented!()
}

#[inline(always)]
#[hax_lib::lean::replace_body("sorry")]
pub fn _vandq_u32(a: _uint32x4_t, b: _uint32x4_t) -> _uint32x4_t {
    unimplemented!()
}
#[inline(always)]
#[hax_lib::lean::replace_body("sorry")]
pub fn _vreinterpretq_u32_s16(a: _int16x8_t) -> _uint32x4_t {
    unimplemented!()
}
#[inline(always)]
#[hax_lib::lean::replace_body("sorry")]
pub fn _vreinterpretq_s16_u32(a: _uint32x4_t) -> _int16x8_t {
    unimplemented!()
}
#[inline(always)]
#[hax_lib::lean::replace_body("sorry")]
pub fn _vtrn1q_s16(a: _int16x8_t, b: _int16x8_t) -> _int16x8_t {
    unimplemented!()
}
#[inline(always)]
#[hax_lib::lean::replace_body("sorry")]
pub fn _vtrn2q_s16(a: _int16x8_t, b: _int16x8_t) -> _int16x8_t {
    unimplemented!()
}
#[inline(always)]
#[hax_lib::lean::replace_body("sorry")]
pub fn _vmulq_n_u32(a: _uint32x4_t, b: u32) -> _uint32x4_t {
    unimplemented!()
}

#[inline(always)]
#[hax_lib::lean::replace_body("sorry")]
pub fn _vtrn1q_s32(a: _int32x4_t, b: _int32x4_t) -> _int32x4_t {
    unimplemented!()
}
#[inline(always)]
#[hax_lib::lean::replace_body("sorry")]
pub fn _vreinterpretq_s16_s32(a: _int32x4_t) -> _int16x8_t {
    unimplemented!()
}
#[inline(always)]
#[hax_lib::lean::replace_body("sorry")]
pub fn _vreinterpretq_s32_s16(a: _int16x8_t) -> _int32x4_t {
    unimplemented!()
}

#[inline(always)]
#[hax_lib::lean::replace_body("sorry")]
pub fn _vtrn2q_s32(a: _int32x4_t, b: _int32x4_t) -> _int32x4_t {
    unimplemented!()
}
#[inline(always)]
#[hax_lib::lean::replace_body("sorry")]
pub fn _vtrn1q_s64(a: _int64x2_t, b: _int64x2_t) -> _int64x2_t {
    unimplemented!()
}

#[inline(always)]
#[hax_lib::lean::replace_body("sorry")]
pub fn _vtrn1q_u64(a: _uint64x2_t, b: _uint64x2_t) -> _uint64x2_t {
    unimplemented!()
}

#[inline(always)]
#[hax_lib::lean::replace_body("sorry")]
pub fn _vreinterpretq_s16_s64(a: _int64x2_t) -> _int16x8_t {
    unimplemented!()
}
#[inline(always)]
#[hax_lib::lean::replace_body("sorry")]
pub fn _vreinterpretq_s64_s16(a: _int16x8_t) -> _int64x2_t {
    unimplemented!()
}
#[inline(always)]
#[hax_lib::lean::replace_body("sorry")]
pub fn _vtrn2q_s64(a: _int64x2_t, b: _int64x2_t) -> _int64x2_t {
    unimplemented!()
}

#[inline(always)]
#[hax_lib::lean::replace_body("sorry")]
pub fn _vtrn2q_u64(a: _uint64x2_t, b: _uint64x2_t) -> _uint64x2_t {
    unimplemented!()
}

#[inline(always)]
#[hax_lib::lean::replace_body("sorry")]
pub fn _vmull_s16(a: _int16x4_t, b: _int16x4_t) -> _int32x4_t {
    unimplemented!()
}
#[inline(always)]
#[hax_lib::lean::replace_body("sorry")]
pub fn _vget_low_s16(a: _int16x8_t) -> _int16x4_t {
    unimplemented!()
}
#[inline(always)]
#[hax_lib::lean::replace_body("sorry")]
pub fn _vmull_high_s16(a: _int16x8_t, b: _int16x8_t) -> _int32x4_t {
    unimplemented!()
}
#[inline(always)]
#[hax_lib::lean::replace_body("sorry")]
pub fn _vmlal_s16(a: _int32x4_t, b: _int16x4_t, c: _int16x4_t) -> _int32x4_t {
    unimplemented!()
}
#[inline(always)]
#[hax_lib::lean::replace_body("sorry")]
pub fn _vmlal_high_s16(a: _int32x4_t, b: _int16x8_t, c: _int16x8_t) -> _int32x4_t {
    unimplemented!()
}
#[inline(always)]
#[hax_lib::lean::replace_body("sorry")]
pub fn _vld1q_u8(ptr: &[u8]) -> _uint8x16_t {
    unimplemented!()
}
#[inline(always)]
#[hax_lib::lean::replace_body("sorry")]
pub fn _vreinterpretq_u8_s16(a: _int16x8_t) -> _uint8x16_t {
    unimplemented!()
}
#[inline(always)]
#[hax_lib::lean::replace_body("sorry")]
pub fn _vqtbl1q_u8(t: _uint8x16_t, idx: _uint8x16_t) -> _uint8x16_t {
    unimplemented!()
}
#[inline(always)]
#[hax_lib::lean::replace_body("sorry")]
pub fn _vreinterpretq_s16_u8(a: _uint8x16_t) -> _int16x8_t {
    unimplemented!()
}
#[inline(always)]
#[hax_lib::lean::replace_body("sorry")]
pub fn _vshlq_s16(a: _int16x8_t, b: _int16x8_t) -> _int16x8_t {
    unimplemented!()
}
#[inline(always)]
#[hax_lib::lean::replace_body("sorry")]
pub fn _vshlq_u16(a: _uint16x8_t, b: _int16x8_t) -> _uint16x8_t {
    unimplemented!()
}
#[inline(always)]
#[hax_lib::lean::replace_body("sorry")]
pub fn _vaddv_u16(a: _uint16x4_t) -> u16 {
    unimplemented!()
}
#[inline(always)]
#[hax_lib::lean::replace_body("sorry")]
pub fn _vget_low_u16(a: _uint16x8_t) -> _uint16x4_t {
    unimplemented!()
}
#[inline(always)]
#[hax_lib::lean::replace_body("sorry")]
pub fn _vget_high_u16(a: _uint16x8_t) -> _uint16x4_t {
    unimplemented!()
}
#[inline(always)]
#[hax_lib::lean::replace_body("sorry")]
pub fn _vaddvq_s16(a: _int16x8_t) -> i16 {
    unimplemented!()
}

#[inline(always)]
#[hax_lib::lean::replace_body("sorry")]
pub fn _vsliq_n_s32<const N: i32>(a: _int32x4_t, b: _int32x4_t) -> _int32x4_t {
    unimplemented!()
}

#[inline(always)]
#[hax_lib::lean::replace_body("sorry")]
pub fn _vreinterpretq_s64_s32(a: _int32x4_t) -> _int64x2_t {
    unimplemented!()
}

#[inline(always)]
#[hax_lib::lean::replace_body("sorry")]
pub fn _vsliq_n_s64<const N: i32>(a: _int64x2_t, b: _int64x2_t) -> _int64x2_t {
    unimplemented!()
}

#[inline(always)]
#[hax_lib::lean::replace_body("sorry")]
pub fn _vreinterpretq_u8_s64(a: _int64x2_t) -> _uint8x16_t {
    unimplemented!()
}

#[inline(always)]
#[hax_lib::lean::replace_body("()")]
pub fn _vst1q_u8(out: &mut [u8], v: _uint8x16_t) {
    unimplemented!()
}
#[inline(always)]
#[hax_lib::lean::replace_body("sorry")]
pub fn _vdupq_n_u16(value: u16) -> _uint16x8_t {
    unimplemented!()
}
#[inline(always)]
#[hax_lib::lean::replace_body("sorry")]
pub fn _vandq_u16(a: _uint16x8_t, b: _uint16x8_t) -> _uint16x8_t {
    unimplemented!()
}
#[inline(always)]
#[hax_lib::lean::replace_body("sorry")]
pub fn _vreinterpretq_u16_u8(a: _uint8x16_t) -> _uint16x8_t {
    unimplemented!()
}
#[inline(always)]
#[hax_lib::lean::replace_body("sorry")]
pub fn _vld1q_u16(ptr: &[u16]) -> _uint16x8_t {
    unimplemented!()
}
#[inline(always)]
#[hax_lib::lean::replace_body("sorry")]
pub fn _vcleq_s16(a: _int16x8_t, b: _int16x8_t) -> _uint16x8_t {
    unimplemented!()
}
#[inline(always)]
#[hax_lib::lean::replace_body("sorry")]
pub fn _vaddvq_u16(a: _uint16x8_t) -> u16 {
    unimplemented!()
}
#[inline(always)]
#[hax_lib::lean::replace_body("sorry")]
pub fn _vmull_p64(a: u64, b: u64) -> u128 {
    unimplemented!()
}

#[inline]
#[hax_lib::lean::replace_body("sorry")]
pub fn _veorq_u8(a: _uint8x16_t, b: _uint8x16_t) -> _uint8x16_t {
    unimplemented!()
}

#[inline]
#[hax_lib::lean::replace_body("sorry")]
pub fn _vaesmcq_u8(data: _uint8x16_t) -> _uint8x16_t {
    unimplemented!()
}

#[inline]
#[hax_lib::lean::replace_body("sorry")]
pub fn _vaeseq_u8(data: _uint8x16_t, key: _uint8x16_t) -> _uint8x16_t {
    unimplemented!()
}

#[inline]
#[hax_lib::lean::replace_body("sorry")]
pub fn _vdupq_n_u8(value: u8) -> _uint8x16_t {
    unimplemented!()
}

#[inline]
#[hax_lib::lean::replace_body("sorry")]
pub fn _vdupq_laneq_u32<const N: i32>(a: _uint32x4_t) -> _uint32x4_t {
    unimplemented!()
}

#[inline]
#[hax_lib::lean::replace_body("sorry")]
pub fn _veorq_u32(a: _uint32x4_t, b: _uint32x4_t) -> _uint32x4_t {
    unimplemented!()
}

#[inline]
#[hax_lib::lean::replace_body("sorry")]
pub fn _vextq_u32<const N: i32>(a: _uint32x4_t, b: _uint32x4_t) -> _uint32x4_t {
    unimplemented!()
}

#[inline(always)]
#[hax_lib::lean::replace_body("sorry")]
pub fn _vld1q_u32(ptr: &[u32]) -> _uint32x4_t {
    unimplemented!()
}

#[inline(always)]
#[hax_lib::lean::replace_body("sorry")]
pub fn _vreinterpretq_u32_u8(a: _uint8x16_t) -> _uint32x4_t {
    unimplemented!()
}

#[inline(always)]
#[hax_lib::lean::replace_body("sorry")]
pub fn _vreinterpretq_u8_u32(a: _uint32x4_t) -> _uint8x16_t {
    unimplemented!()
}
