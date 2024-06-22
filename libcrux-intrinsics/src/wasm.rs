#![allow(non_camel_case_types, unsafe_code)]
use core::arch::wasm32::*; 

pub type _uint8x16_t = v128;
pub type _int16x8_t = v128;
pub type _uint16x8_t = v128;
pub type _uint32x4_t = v128;
pub type _int32x4_t = v128;
pub type _int64x2_t = v128;
pub type _uint64x2_t = v128;

// Initialize with Splat
// 
#[inline(always)]
pub fn _vdupq_n_s16(i: i16) -> _int16x8_t {
    i16x8_splat(i)
}

#[inline(always)]
pub fn _vdupq_n_u32(value: u32) -> _uint32x4_t {
    u32x4_splat(value) 
}

#[inline(always)]
pub fn _vdupq_n_u64(i: u64) -> _uint64x2_t {
    u64x2_splat(i) 
}

#[inline(always)]
pub fn _vdupq_n_u16(value: u16) -> _uint16x8_t {
    u16x8_splat(value) 
}

// Cast
// 
#[inline(always)]
pub fn _vreinterpretq_s16_u16(m0: _int16x8_t) -> _int16x8_t {
    m0 
}

#[inline(always)]
pub fn _vreinterpretq_u16_s16(m0: _int16x8_t) -> _uint16x8_t {
    m0 
}

#[inline(always)]
pub fn _vreinterpretq_s32_u32(m0: _uint32x4_t) -> _int32x4_t {
    m0
}


#[inline(always)]
pub fn _vreinterpretq_u32_s32(a: _int32x4_t) -> _uint32x4_t {
    a 
}

#[inline(always)]
pub fn _vreinterpretq_u32_s16(a: _int16x8_t) -> _uint32x4_t {
    a 
}
#[inline(always)]
pub fn _vreinterpretq_s16_u32(a: _uint32x4_t) -> _int16x8_t {
    a 
}

#[inline(always)]
pub fn _vreinterpretq_s16_s32(a: _int32x4_t) -> _int16x8_t {
    a 
}

#[inline(always)]
pub fn _vreinterpretq_s32_s16(a: _int16x8_t) -> _int32x4_t {
    a 
}

#[inline(always)]
pub fn _vreinterpretq_s16_s64(a: _int64x2_t) -> _int16x8_t {
    a 
}
#[inline(always)]
pub fn _vreinterpretq_s64_s16(a: _int16x8_t) -> _int64x2_t {
    a 
}

#[inline(always)]
pub fn _vreinterpretq_u8_s16(a: _int16x8_t) -> _uint8x16_t {
    a 
}

#[inline(always)]
pub fn _vreinterpretq_s16_u8(a: _uint8x16_t) -> _int16x8_t {
    a 
}


#[inline(always)]
pub fn _vreinterpretq_s64_s32(a: _int32x4_t) -> _int64x2_t {
    a 
}

#[inline(always)]
pub fn _vreinterpretq_u8_s64(a: _int64x2_t) -> _uint8x16_t {
    a 
}

#[inline(always)]
pub fn _vreinterpretq_u16_u8(a: _uint8x16_t) -> _uint16x8_t {
    a
}

// Load from array
// 
#[inline(always)]
pub fn _vld1q_s16(array: &[i16]) -> _int16x8_t {
    unsafe { v128_load(array.as_ptr() as *const v128) }
}

#[inline(always)]
pub fn _vld1q_bytes_u64(array: &[u8]) -> _uint64x2_t {
    unsafe { v128_load(array.as_ptr() as *const v128) }
}

#[inline(always)]
pub fn _vld1q_u64(array: &[u64]) -> _uint64x2_t {
    unsafe { v128_load(array.as_ptr() as *const v128) }
}

#[inline(always)]
pub fn _vld1q_u8(array: &[u8]) -> _uint8x16_t {
    unsafe { v128_load(array.as_ptr() as *const v128) }
}

#[inline(always)]
pub fn _vld1q_u16(array: &[u16]) -> _uint16x8_t {
    unsafe { v128_load(array.as_ptr() as *const v128) }
}

// Store to array
#[inline(always)]
pub fn _vst1q_s16(out: &mut [i16], v: _int16x8_t) {
    unsafe { v128_store(out.as_mut_ptr() as *mut v128, v) }
}

#[inline(always)]
pub fn _vst1q_u64(out: &mut [u64], v: _uint64x2_t) {
    unsafe { v128_store(out.as_mut_ptr() as *mut v128, v) }
}

#[inline(always)]
pub fn _vst1q_bytes_u64(out: &mut [u8], v: _uint64x2_t) {
    unsafe { v128_store(out.as_mut_ptr() as *mut v128, v) }
}

#[inline(always)]
pub fn _vst1q_u8(out: &mut [u8], v: _uint8x16_t) {
    unsafe { v128_store(out.as_mut_ptr() as *mut v128, v) }
}


// Add and sub
// 
#[inline(always)]
pub fn _vaddq_s16(lhs: _int16x8_t, rhs: _int16x8_t) -> _int16x8_t {
    i16x8_add(lhs, rhs) 
}

#[inline(always)]
pub fn _vsubq_s16(lhs: _int16x8_t, rhs: _int16x8_t) -> _int16x8_t {
    i16x8_sub(lhs, rhs) 
}

#[inline(always)]
pub fn _vaddq_u32(compressed: _uint32x4_t, half: _uint32x4_t) -> _uint32x4_t {
    u32x4_add(compressed, half) 
}

/* 
#[inline(always)]
pub fn _vaddv_u16(a: uint16x4_t) -> u16 {
    vaddv_u16(a) }
}

#[inline(always)]
pub fn _vaddvq_s16(a: _int16x8_t) -> i16 {
    vaddvq_s16(a) }
}

#[inline(always)]
pub fn _vaddvq_u16(a: ) -> u16 {
    vaddvq_u16(a) }
}
*/

// Mul
// 
#[inline(always)]
pub fn _vmulq_n_s16(v: _int16x8_t, c: i16) -> _int16x8_t {
    i16x8_mul(v, i16x8_splat(c)) 
}

#[inline(always)]
pub fn _vmulq_n_u16(v: _uint16x8_t, c: u16) -> _uint16x8_t {
    u16x8_mul(v, u16x8_splat(c)) 
}

#[inline(always)]
pub fn _vmulq_s16(v: _int16x8_t, c: _int16x8_t) -> _int16x8_t {
    i16x8_mul(v, c) 
}

#[inline(always)]
pub fn _vmulq_n_u32(v: _uint32x4_t, c: u32) -> _uint32x4_t {
    u32x4_mul(v, u32x4_splat(c)) 
}

// #[inline(always)]
// pub fn _vmull_s16(a: int16x4_t, b: int16x4_t) -> int32x4_t {
//     i32x4_extmul_low_i16x8(a, b)
// }

// #[inline(always)]
// pub fn _vmull_high_s16(a: _int16x8_t, b: _int16x8_t) -> int32x4_t {
//     vmull_high_s16(a, b) }
// }
// #[inline(always)]
// pub fn _vmlal_s16(a: int32x4_t, b: int16x4_t, c: int16x4_t) -> int32x4_t {
//     vmlal_s16(a, b, c) }
// }
// #[inline(always)]
// pub fn _vmlal_high_s16(a: int32x4_t, b: _int16x8_t, c: _int16x8_t) -> int32x4_t {
//     vmlal_high_s16(a, b, c) }
// }
// #[inline(always)]
// pub fn _vqdmulhq_n_s16(k: _int16x8_t, b: i16) -> _int16x8_t {
//     vqdmulhq_n_s16(k, b) }
// }
// #[inline(always)]
// pub fn _vqdmulhq_s16(v: _int16x8_t, c: _int16x8_t) -> _int16x8_t {
//     vqdmulhq_s16(v, c) }
// }


// Shift
#[inline(always)]
pub fn _vshrq_n_s16<const SHIFT_BY: u32>(v: _int16x8_t) -> _int16x8_t {
    i16x8_shr(v,SHIFT_BY)
}

#[inline(always)]
pub fn _vshrq_n_u16<const SHIFT_BY: u32>(v: _uint16x8_t) -> _uint16x8_t {
    u16x8_shr(v,SHIFT_BY)
}

#[inline(always)]
pub fn _vshrq_n_u64<const SHIFT_BY: u32>(v: _uint64x2_t) -> _uint64x2_t {
    u64x2_shr(v,SHIFT_BY)
}

#[inline(always)]
pub fn _vshrq_n_u32<const SHIFT_BY: u32>(v: _uint32x4_t) -> _uint32x4_t {
    u32x4_shr(v,SHIFT_BY)
}

#[inline(always)]
pub fn _vshlq_n_u64<const SHIFT_BY: u32>(v: _uint64x2_t) -> _uint64x2_t {
    u64x2_shl(v,SHIFT_BY)
}

#[inline(always)]
pub fn _vshlq_n_s16<const SHIFT_BY: u32>(v: _int16x8_t) -> _int16x8_t {
    i16x8_shl(v,SHIFT_BY)
}

#[inline(always)]
pub fn _vshlq_n_u32<const SHIFT_BY: u32>(v: _uint32x4_t) -> _uint32x4_t {
    u32x4_shl(v,SHIFT_BY)
}

// #[inline(always)]
// pub fn _vshlq_s16(a: _int16x8_t, b: _int16x8_t) -> _int16x8_t {
//     i16x8_shl(v,b)
// }

// #[inline(always)]
// pub fn _vshlq_u16(a: , b: _int16x8_t) ->  {
//     vshlq_u16(a, b) }
// }

// #[inline(always)]
// pub fn _vsliq_n_s32<const N: i32>(a: int32x4_t, b: int32x4_t) -> int32x4_t {
//     vsliq_n_s32::<N>(a, b) 
// }

// #[inline(always)]
// pub fn _vsliq_n_s64<const N: i32>(a: int64x2_t, b: int64x2_t) -> int64x2_t {
//     vsliq_n_s64::<N>(a, b) }
// }

// Compare

#[inline(always)]
pub fn _vcgeq_s16(v: _int16x8_t, c: _int16x8_t) -> _uint16x8_t {
    i16x8_ge(v, c)
}

#[inline(always)]
pub fn _vcleq_s16(a: _int16x8_t, b: _int16x8_t) -> _uint16x8_t {
    i16x8_le(a, b)
}

// Bitwise Operations
// 
#[inline(always)]
pub fn _vandq_s16(a: _int16x8_t, b: _int16x8_t) -> _int16x8_t {
   v128_and(a, b)
}


#[inline(always)]
pub fn _vandq_u32(a: _uint32x4_t, b: _uint32x4_t) -> _uint32x4_t {
    v128_and(a, b)
}

#[inline(always)]
pub fn _vandq_u16(a: _uint16x8_t, b: _uint16x8_t) ->  _uint16x8_t{
    v128_and(a, b)
}

#[inline(always)]
pub fn _vbicq_u64(a: _uint64x2_t, b: _uint64x2_t) -> _uint64x2_t {
    v128_andnot(a, b)
}

#[inline(always)]
pub fn _veorq_u64(a: _uint64x2_t, b: _uint64x2_t) -> _uint64x2_t {
    v128_xor(a, b)
}

#[inline(always)]
pub fn _veorq_s16(a: _int16x8_t, b: _int16x8_t) -> _int16x8_t {
    v128_xor(a, b)
}


// Shuffle
// 
#[inline(always)]
pub fn _vtrn1q_s16(a: _int16x8_t, b: _int16x8_t) -> _int16x8_t {
    i16x8_shuffle::<0,8,2,10,4,12,6,14>(a, b)
}

#[inline(always)]
pub fn _vtrn2q_s16(a: _int16x8_t, b: _int16x8_t) -> _int16x8_t {
    i16x8_shuffle::<1,9,3,11,5,13,7,15>(a, b)
}

#[inline(always)]
pub fn _vtrn1q_s32(a: _int32x4_t, b: _int32x4_t) -> _int32x4_t {
    i32x4_shuffle::<0,4,2,6>(a, b)
}

#[inline(always)]
pub fn _vtrn2q_s32(a: _int32x4_t, b: _int32x4_t) -> _int32x4_t {
    i32x4_shuffle::<1,5,3,7>(a, b)
}

#[inline(always)]
pub fn _vtrn1q_s64(a: _int64x2_t, b: _int64x2_t) -> _int64x2_t {
    i64x2_shuffle::<0,2>(a, b)
}

#[inline(always)]
pub fn _vtrn1q_u64(a: _uint64x2_t, b: _uint64x2_t) -> _uint64x2_t {
    u64x2_shuffle::<0,2>(a, b)
}

#[inline(always)]
pub fn _vtrn2q_s64(a: _int64x2_t, b: _int64x2_t) -> _int64x2_t {
    i64x2_shuffle::<1,3>(a, b)
}

#[inline(always)]
pub fn _vtrn2q_u64(a: _uint64x2_t, b: _uint64x2_t) -> _uint64x2_t {
    u64x2_shuffle::<1,3>(a, b)
}

#[inline(always)]
pub fn _vqtbl1q_u8(t: _uint8x16_t, idx: _uint8x16_t) -> _uint8x16_t {
    u8x16_swizzle(t, idx) 
}

// Extract 
// 
// #[inline(always)]
// pub fn _vget_low_s16(a: _int16x8_t) -> int16x4_t {
//     vget_low_s16(a) }
// }

// #[inline(always)]
// pub fn _vget_low_u16(a: ) -> uint16x4_t {
//     vget_low_u16(a) }
// }
// #[inline(always)]
// pub fn _vget_high_u16(a: ) -> uint16x4_t {
//     vget_high_u16(a) }
// }






