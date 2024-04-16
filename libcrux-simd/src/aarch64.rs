use core::arch::aarch64::*;

/// A 128-bit integer type for SIMD instructions.
pub type Vec128 = uint32x4_t;

/// We can't compute on a const `N`. So this is a little ugly.
/// Ensure that the `N` you provide is handled here.
///
/// 16 is handled differently because it's more efficient this way.
#[inline(always)]
pub fn rotate_left128_u32(a: Vec128, n: u32) -> Vec128 {
    assert!(n >= 1 && n <= 32);
    match n {
        7 => unsafe { vsriq_n_u32(vshlq_n_u32(a, 7), a, 32 - 7) },
        8 => unsafe { vsriq_n_u32(vshlq_n_u32(a, 8), a, 32 - 8) },
        12 => unsafe { vsriq_n_u32(vshlq_n_u32(a, 12), a, 32 - 12) },
        16 => unsafe { vreinterpretq_u32_u16(vrev32q_u16(vreinterpretq_u16_u32(a))) },
        _ => unimplemented!(),
    }
}

#[inline(always)]
pub fn rotate_left128_u32_16(a: Vec128) -> Vec128 {
    unsafe { vreinterpretq_u32_u16(vrev32q_u16(vreinterpretq_u16_u32(a))) }
}

#[inline(always)]
pub fn rotate_left128_u32_12(a: Vec128) -> Vec128 {
    unsafe { vsriq_n_u32(vshlq_n_u32(a, 12), a, 32 - 12) }
}

#[inline(always)]
pub fn rotate_left128_u32_8(a: Vec128) -> Vec128 {
    unsafe { vsriq_n_u32(vshlq_n_u32(a, 8), a, 32 - 8) }
}

#[inline(always)]
pub fn rotate_left128_u32_7(a: Vec128) -> Vec128 {
    unsafe { vsriq_n_u32(vshlq_n_u32(a, 7), a, 32 - 7) }
}

#[inline(always)]
pub fn add32(a: Vec128, b: Vec128) -> Vec128 {
    unsafe { vaddq_u32(a, b) }
}

#[inline(always)]
pub fn xor32(a: Vec128, b: Vec128) -> Vec128 {
    unsafe { veorq_u32(a, b) }
}

#[inline(always)]
pub fn load32(x: u32) -> Vec128 {
    unsafe { vdupq_n_u32(x) }
}

#[inline(always)]
// 16 u8, interpreted as 4 u32
pub fn load8_32_le(value: &[u8]) -> Vec128 {
    unsafe { vld1q_u32(value.as_ptr() as *const u32) }
}

/// Load a `u8` slice into 4 `u32`.
///
/// The slice must be `value.len() <= 4 * 4`.
/// When the slice is shorter, it is padded with `0`s.
#[inline(always)]
pub fn u32_from_le_bytes(value: &[u8]) -> Vec128 {
    let mut padded = [0u8; 16];
    padded[0..value.len()].copy_from_slice(value);
    load8_32_le(&padded)
}

#[inline(always)]
// 4 u32, interpreted as 4 u32
pub fn load32_le(values: [u32; 4]) -> Vec128 {
    unsafe { vld1q_u32(values.as_ptr() as *const u32) }
}

#[inline(always)]
// store vec128 into u8 slice
pub fn store8_32_le(value: Vec128, out: &mut [u8; 16]) {
    unsafe { vst1q_u32(out.as_mut_ptr() as *mut u32, value) }
}

/// Store 4 `u32` into little endian bytes.
///
/// When the output has less than 16 bytes left to write in, only the available
/// number of bytes are written.
#[inline(always)]
pub fn u32_to_le_bytes(out: &mut [u8], value: Vec128) {
    let mut padded = [0u8; 16];
    store8_32_le_ip(&mut padded, value);
    out.copy_from_slice(&padded[0..out.len()]);
}

#[inline(always)]
pub fn store8_32_le_ip(out: &mut [u8], value: Vec128) {
    unsafe { vst1q_u32(out.as_mut_ptr() as *mut u32, value) }
}

#[inline(always)]
pub fn interleave_low64(x1: Vec128, x2: Vec128) -> Vec128 {
    unsafe {
        vreinterpretq_u32_u64(vzip1q_u64(
            vreinterpretq_u64_u32(x1),
            vreinterpretq_u64_u32(x2),
        ))
    }
}

#[inline(always)]
pub fn interleave_high64(x1: Vec128, x2: Vec128) -> Vec128 {
    unsafe {
        vreinterpretq_u32_u64(vzip2q_u64(
            vreinterpretq_u64_u32(x1),
            vreinterpretq_u64_u32(x2),
        ))
    }
}

#[inline(always)]
pub fn interleave_low32(x1: Vec128, x2: Vec128) -> Vec128 {
    unsafe { vzip1q_u32(x1, x2) }
}

#[inline(always)]
pub fn interleave_high32(x1: Vec128, x2: Vec128) -> Vec128 {
    unsafe { vzip2q_u32(x1, x2) }
}
