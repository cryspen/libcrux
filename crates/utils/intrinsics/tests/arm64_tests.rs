//! Comprehensive tests for ARM64 NEON intrinsic wrappers.
//!
//! These tests verify that each wrapper function in src/arm64.rs behaves
//! identically to its upstream equivalent from core::arch::aarch64.

#![cfg(target_arch = "aarch64")]

use libcrux_intrinsics::arm64::*;

#[cfg(target_arch = "aarch64")]
use core::arch::aarch64::*;

/// Helper to compare two int16x8_t values
fn int16x8_eq(a: int16x8_t, b: int16x8_t) -> bool {
    unsafe {
        let a_bytes: [u8; 16] = core::mem::transmute(a);
        let b_bytes: [u8; 16] = core::mem::transmute(b);
        a_bytes == b_bytes
    }
}

/// Helper to compare two uint16x8_t values
fn uint16x8_eq(a: uint16x8_t, b: uint16x8_t) -> bool {
    unsafe {
        let a_bytes: [u8; 16] = core::mem::transmute(a);
        let b_bytes: [u8; 16] = core::mem::transmute(b);
        a_bytes == b_bytes
    }
}

/// Helper to compare two int32x4_t values
fn int32x4_eq(a: int32x4_t, b: int32x4_t) -> bool {
    unsafe {
        let a_bytes: [u8; 16] = core::mem::transmute(a);
        let b_bytes: [u8; 16] = core::mem::transmute(b);
        a_bytes == b_bytes
    }
}

/// Helper to compare two uint32x4_t values
fn uint32x4_eq(a: uint32x4_t, b: uint32x4_t) -> bool {
    unsafe {
        let a_bytes: [u8; 16] = core::mem::transmute(a);
        let b_bytes: [u8; 16] = core::mem::transmute(b);
        a_bytes == b_bytes
    }
}

/// Helper to compare two int64x2_t values
fn int64x2_eq(a: int64x2_t, b: int64x2_t) -> bool {
    unsafe {
        let a_bytes: [u8; 16] = core::mem::transmute(a);
        let b_bytes: [u8; 16] = core::mem::transmute(b);
        a_bytes == b_bytes
    }
}

/// Helper to compare two uint64x2_t values
fn uint64x2_eq(a: uint64x2_t, b: uint64x2_t) -> bool {
    unsafe {
        let a_bytes: [u8; 16] = core::mem::transmute(a);
        let b_bytes: [u8; 16] = core::mem::transmute(b);
        a_bytes == b_bytes
    }
}

/// Helper to compare two uint8x16_t values
fn uint8x16_eq(a: uint8x16_t, b: uint8x16_t) -> bool {
    unsafe {
        let a_bytes: [u8; 16] = core::mem::transmute(a);
        let b_bytes: [u8; 16] = core::mem::transmute(b);
        a_bytes == b_bytes
    }
}

/// Helper to compare two int16x4_t values
fn int16x4_eq(a: int16x4_t, b: int16x4_t) -> bool {
    unsafe {
        let a_bytes: [u8; 8] = core::mem::transmute(a);
        let b_bytes: [u8; 8] = core::mem::transmute(b);
        a_bytes == b_bytes
    }
}

/// Helper to compare two uint16x4_t values
fn uint16x4_eq(a: uint16x4_t, b: uint16x4_t) -> bool {
    unsafe {
        let a_bytes: [u8; 8] = core::mem::transmute(a);
        let b_bytes: [u8; 8] = core::mem::transmute(b);
        a_bytes == b_bytes
    }
}

// =============================================================================
// Duplicate/Broadcast Tests
// =============================================================================

#[test]
fn test_vdupq_n_s16() {
    let result = _vdupq_n_s16(42);
    let expected = unsafe { vdupq_n_s16(42) };
    assert!(int16x8_eq(result, expected));
}

#[test]
fn test_vdupq_n_u64() {
    let result = _vdupq_n_u64(0x123456789ABCDEF0);
    let expected = unsafe { vdupq_n_u64(0x123456789ABCDEF0) };
    assert!(uint64x2_eq(result, expected));
}

#[test]
fn test_vdupq_n_u32() {
    let result = _vdupq_n_u32(0x12345678);
    let expected = unsafe { vdupq_n_u32(0x12345678) };
    assert!(uint32x4_eq(result, expected));
}

#[test]
fn test_vdupq_n_u16() {
    let result = _vdupq_n_u16(0x1234);
    let expected = unsafe { vdupq_n_u16(0x1234) };
    assert!(uint16x8_eq(result, expected));
}

#[test]
fn test_vdupq_n_u8() {
    let result = _vdupq_n_u8(0x42);
    let expected = unsafe { vdupq_n_u8(0x42) };
    assert!(uint8x16_eq(result, expected));
}

// =============================================================================
// Load Tests
// =============================================================================

#[test]
fn test_vld1q_s16() {
    let input: [i16; 8] = [0, 1, 2, 3, 4, 5, 6, 7];
    let result = _vld1q_s16(&input);
    let expected = unsafe { vld1q_s16(input.as_ptr()) };
    assert!(int16x8_eq(result, expected));
}

#[test]
fn test_vld1q_u64() {
    let input: [u64; 2] = [0x123456789ABCDEF0, 0xFEDCBA9876543210];
    let result = _vld1q_u64(&input);
    let expected = unsafe { vld1q_u64(input.as_ptr()) };
    assert!(uint64x2_eq(result, expected));
}

#[test]
fn test_vld1q_bytes() {
    let input: [u8; 16] = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15];
    let result = _vld1q_bytes(&input);
    let expected = unsafe { vreinterpretq_s16_u8(vld1q_u8(input.as_ptr())) };
    assert!(int16x8_eq(result, expected));
}

#[test]
fn test_vld1q_bytes_u64() {
    let input: [u8; 16] = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15];
    let result = _vld1q_bytes_u64(&input);
    let expected = unsafe { vld1q_u64(input.as_ptr() as *const u64) };
    assert!(uint64x2_eq(result, expected));
}

#[test]
fn test_vld1q_u8() {
    let input: [u8; 16] = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15];
    let result = _vld1q_u8(&input);
    let expected = unsafe { vld1q_u8(input.as_ptr()) };
    assert!(uint8x16_eq(result, expected));
}

#[test]
fn test_vld1q_u32() {
    let input: [u32; 4] = [0x12345678, 0x9ABCDEF0, 0x11111111, 0x22222222];
    let result = _vld1q_u32(&input);
    let expected = unsafe { vld1q_u32(input.as_ptr()) };
    assert!(uint32x4_eq(result, expected));
}

#[test]
fn test_vld1q_u16() {
    let input: [u16; 8] = [0, 1, 2, 3, 4, 5, 6, 7];
    let result = _vld1q_u16(&input);
    let expected = unsafe { vld1q_u16(input.as_ptr()) };
    assert!(uint16x8_eq(result, expected));
}

// =============================================================================
// Store Tests
// =============================================================================

#[test]
fn test_vst1q_s16() {
    let vec = _vdupq_n_s16(42);
    let mut output1: [i16; 8] = [0; 8];
    let mut output2: [i16; 8] = [0; 8];

    _vst1q_s16(&mut output1, vec);
    unsafe {
        vst1q_s16(output2.as_mut_ptr(), vec);
    }
    assert_eq!(output1, output2);
}

#[test]
fn test_vst1q_bytes() {
    let vec = _vdupq_n_s16(0x1234);
    let mut output1: [u8; 16] = [0; 16];
    let mut output2: [u8; 16] = [0; 16];

    _vst1q_bytes(&mut output1, vec);
    unsafe {
        vst1q_u8(output2.as_mut_ptr(), vreinterpretq_u8_s16(vec));
    }
    assert_eq!(output1, output2);
}

#[test]
fn test_vst1q_u64() {
    let vec = _vdupq_n_u64(0x123456789ABCDEF0);
    let mut output1: [u64; 2] = [0; 2];
    let mut output2: [u64; 2] = [0; 2];

    _vst1q_u64(&mut output1, vec);
    unsafe {
        vst1q_u64(output2.as_mut_ptr(), vec);
    }
    assert_eq!(output1, output2);
}

#[test]
fn test_vst1q_bytes_u64() {
    let vec = _vdupq_n_u64(0x123456789ABCDEF0);
    let mut output1: [u8; 16] = [0; 16];
    let mut output2: [u8; 16] = [0; 16];

    _vst1q_bytes_u64(&mut output1, vec);
    unsafe {
        vst1q_u64(output2.as_mut_ptr() as *mut u64, vec);
    }
    assert_eq!(output1, output2);
}

#[test]
fn test_vst1q_u8() {
    let vec = _vdupq_n_u8(0x42);
    let mut output1: [u8; 16] = [0; 16];
    let mut output2: [u8; 16] = [0; 16];

    _vst1q_u8(&mut output1, vec);
    unsafe {
        vst1q_u8(output2.as_mut_ptr(), vec);
    }
    assert_eq!(output1, output2);
}

// =============================================================================
// Arithmetic Tests
// =============================================================================

#[test]
fn test_vaddq_s16() {
    let a = _vdupq_n_s16(10);
    let b = _vdupq_n_s16(20);
    let result = _vaddq_s16(a, b);
    let expected = unsafe { vaddq_s16(a, b) };
    assert!(int16x8_eq(result, expected));
}

#[test]
fn test_vsubq_s16() {
    let a = _vdupq_n_s16(30);
    let b = _vdupq_n_s16(10);
    let result = _vsubq_s16(a, b);
    let expected = unsafe { vsubq_s16(a, b) };
    assert!(int16x8_eq(result, expected));
}

#[test]
fn test_vmulq_n_s16() {
    let v = _vdupq_n_s16(10);
    let result = _vmulq_n_s16(v, 5);
    let expected = unsafe { vmulq_n_s16(v, 5) };
    assert!(int16x8_eq(result, expected));
}

#[test]
fn test_vmulq_n_u16() {
    let v = _vdupq_n_u16(10);
    let result = _vmulq_n_u16(v, 5);
    let expected = unsafe { vmulq_n_u16(v, 5) };
    assert!(uint16x8_eq(result, expected));
}

#[test]
fn test_vmulq_s16() {
    let a = _vdupq_n_s16(10);
    let b = _vdupq_n_s16(5);
    let result = _vmulq_s16(a, b);
    let expected = unsafe { vmulq_s16(a, b) };
    assert!(int16x8_eq(result, expected));
}

#[test]
fn test_vaddq_u32() {
    let a = _vdupq_n_u32(10);
    let b = _vdupq_n_u32(20);
    let result = _vaddq_u32(a, b);
    let expected = unsafe { vaddq_u32(a, b) };
    assert!(uint32x4_eq(result, expected));
}

#[test]
fn test_vmulq_n_u32() {
    let a = _vdupq_n_u32(10);
    let result = _vmulq_n_u32(a, 5);
    let expected = unsafe { vmulq_n_u32(a, 5) };
    assert!(uint32x4_eq(result, expected));
}

// =============================================================================
// Saturating Doubling Multiply High Tests
// =============================================================================

#[test]
fn test_vqdmulhq_n_s16() {
    let k = _vdupq_n_s16(1000);
    let result = _vqdmulhq_n_s16(k, 500);
    let expected = unsafe { vqdmulhq_n_s16(k, 500) };
    assert!(int16x8_eq(result, expected));
}

#[test]
fn test_vqdmulhq_s16() {
    let a = _vdupq_n_s16(1000);
    let b = _vdupq_n_s16(500);
    let result = _vqdmulhq_s16(a, b);
    let expected = unsafe { vqdmulhq_s16(a, b) };
    assert!(int16x8_eq(result, expected));
}

#[test]
fn test_vqdmulhq_n_s32() {
    let a = _vdupq_n_u32(1000);
    let a_s32 = _vreinterpretq_s32_u32(a);
    let result = _vqdmulhq_n_s32(a_s32, 500);
    let expected = unsafe { vqdmulhq_n_s32(a_s32, 500) };
    assert!(int32x4_eq(result, expected));
}

// =============================================================================
// Shift Tests
// =============================================================================

#[test]
fn test_vshrq_n_s16() {
    let v = _vdupq_n_s16(1024);
    let result = _vshrq_n_s16::<4>(v);
    let expected = unsafe { vshrq_n_s16::<4>(v) };
    assert!(int16x8_eq(result, expected));
}

#[test]
fn test_vshrq_n_u16() {
    let v = _vdupq_n_u16(1024);
    let result = _vshrq_n_u16::<4>(v);
    let expected = unsafe { vshrq_n_u16::<4>(v) };
    assert!(uint16x8_eq(result, expected));
}

#[test]
fn test_vshrq_n_u64() {
    let v = _vdupq_n_u64(1024);
    let result = _vshrq_n_u64::<4>(v);
    let expected = unsafe { vshrq_n_u64::<4>(v) };
    assert!(uint64x2_eq(result, expected));
}

#[test]
fn test_vshrq_n_u32() {
    let v = _vdupq_n_u32(1024);
    let result = _vshrq_n_u32::<4>(v);
    let expected = unsafe { vshrq_n_u32::<4>(v) };
    assert!(uint32x4_eq(result, expected));
}

#[test]
fn test_vshlq_n_u64() {
    let v = _vdupq_n_u64(1);
    let result = _vshlq_n_u64::<4>(v);
    let expected = unsafe { vshlq_n_u64::<4>(v) };
    assert!(uint64x2_eq(result, expected));
}

#[test]
fn test_vshlq_n_s16() {
    let v = _vdupq_n_s16(1);
    let result = _vshlq_n_s16::<4>(v);
    let expected = unsafe { vshlq_n_s16::<4>(v) };
    assert!(int16x8_eq(result, expected));
}

#[test]
fn test_vshlq_n_u32() {
    let v = _vdupq_n_u32(1);
    let result = _vshlq_n_u32::<4>(v);
    let expected = unsafe { vshlq_n_u32::<4>(v) };
    assert!(uint32x4_eq(result, expected));
}

#[test]
fn test_vshlq_s16() {
    let a = _vdupq_n_s16(1);
    let b = _vdupq_n_s16(4);
    let result = _vshlq_s16(a, b);
    let expected = unsafe { vshlq_s16(a, b) };
    assert!(int16x8_eq(result, expected));
}

#[test]
fn test_vshlq_u16() {
    let a = _vdupq_n_u16(1);
    let b = _vdupq_n_s16(4);
    let result = _vshlq_u16(a, b);
    let expected = unsafe { vshlq_u16(a, b) };
    assert!(uint16x8_eq(result, expected));
}

// =============================================================================
// Bitwise Operations Tests
// =============================================================================

#[test]
fn test_vandq_s16() {
    let a = _vdupq_n_s16(0x00FFu16 as i16);
    let b = _vdupq_n_s16(0x0F0F);
    let result = _vandq_s16(a, b);
    let expected = unsafe { vandq_s16(a, b) };
    assert!(int16x8_eq(result, expected));
}

#[test]
fn test_vandq_u32() {
    let a = _vdupq_n_u32(0x00FF00FF);
    let b = _vdupq_n_u32(0x0F0F0F0F);
    let result = _vandq_u32(a, b);
    let expected = unsafe { vandq_u32(a, b) };
    assert!(uint32x4_eq(result, expected));
}

#[test]
fn test_vandq_u16() {
    let a = _vdupq_n_u16(0x00FF);
    let b = _vdupq_n_u16(0x0F0F);
    let result = _vandq_u16(a, b);
    let expected = unsafe { vandq_u16(a, b) };
    assert!(uint16x8_eq(result, expected));
}

#[test]
fn test_vbicq_u64() {
    let a = _vdupq_n_u64(0xFFFFFFFFFFFFFFFF);
    let b = _vdupq_n_u64(0x00FF00FF00FF00FF);
    let result = _vbicq_u64(a, b);
    let expected = unsafe { vbicq_u64(a, b) };
    assert!(uint64x2_eq(result, expected));
}

#[test]
fn test_veorq_s16() {
    let a = _vdupq_n_s16(0x00FFu16 as i16);
    let b = _vdupq_n_s16(0x0F0F);
    let result = _veorq_s16(a, b);
    let expected = unsafe { veorq_s16(a, b) };
    assert!(int16x8_eq(result, expected));
}

#[test]
fn test_veorq_u64() {
    let a = _vdupq_n_u64(0x00FF00FF00FF00FF);
    let b = _vdupq_n_u64(0x0F0F0F0F0F0F0F0F);
    let result = _veorq_u64(a, b);
    let expected = unsafe { veorq_u64(a, b) };
    assert!(uint64x2_eq(result, expected));
}

#[test]
fn test_veorq_u32() {
    let a = _vdupq_n_u32(0x00FF00FF);
    let b = _vdupq_n_u32(0x0F0F0F0F);
    let result = _veorq_u32(a, b);
    let expected = unsafe { veorq_u32(a, b) };
    assert!(uint32x4_eq(result, expected));
}

#[test]
fn test_veorq_u8() {
    let a = _vdupq_n_u8(0x0F);
    let b = _vdupq_n_u8(0xF0);
    let result = _veorq_u8(a, b);
    let expected = unsafe { veorq_u8(a, b) };
    assert!(uint8x16_eq(result, expected));
}

// =============================================================================
// Compare Tests
// =============================================================================

#[test]
fn test_vcgeq_s16() {
    let a = _vdupq_n_s16(10);
    let b = _vdupq_n_s16(5);
    let result = _vcgeq_s16(a, b);
    let expected = unsafe { vcgeq_s16(a, b) };
    assert!(uint16x8_eq(result, expected));
}

#[test]
fn test_vcleq_s16() {
    let a = _vdupq_n_s16(5);
    let b = _vdupq_n_s16(10);
    let result = _vcleq_s16(a, b);
    let expected = unsafe { vcleq_s16(a, b) };
    assert!(uint16x8_eq(result, expected));
}

// =============================================================================
// Reinterpret Tests
// =============================================================================

#[test]
fn test_vreinterpretq_s16_u16() {
    let a = _vdupq_n_u16(0x1234);
    let result = _vreinterpretq_s16_u16(a);
    let expected = unsafe { vreinterpretq_s16_u16(a) };
    assert!(int16x8_eq(result, expected));
}

#[test]
fn test_vreinterpretq_u16_s16() {
    let a = _vdupq_n_s16(0x1234);
    let result = _vreinterpretq_u16_s16(a);
    let expected = unsafe { vreinterpretq_u16_s16(a) };
    assert!(uint16x8_eq(result, expected));
}

#[test]
fn test_vreinterpretq_s32_u32() {
    let a = _vdupq_n_u32(0x12345678);
    let result = _vreinterpretq_s32_u32(a);
    let expected = unsafe { vreinterpretq_s32_u32(a) };
    assert!(int32x4_eq(result, expected));
}

#[test]
fn test_vreinterpretq_u32_s32() {
    let a = _vreinterpretq_s32_u32(_vdupq_n_u32(0x12345678));
    let result = _vreinterpretq_u32_s32(a);
    let expected = unsafe { vreinterpretq_u32_s32(a) };
    assert!(uint32x4_eq(result, expected));
}

#[test]
fn test_vreinterpretq_u32_u8() {
    let a = _vdupq_n_u8(0x42);
    let result = _vreinterpretq_u32_u8(a);
    let expected = unsafe { vreinterpretq_u32_u8(a) };
    assert!(uint32x4_eq(result, expected));
}

#[test]
fn test_vreinterpretq_u8_u32() {
    let a = _vdupq_n_u32(0x42424242);
    let result = _vreinterpretq_u8_u32(a);
    let expected = unsafe { vreinterpretq_u8_u32(a) };
    assert!(uint8x16_eq(result, expected));
}

#[test]
fn test_vreinterpretq_u32_s16() {
    let a = _vdupq_n_s16(0x1234);
    let result = _vreinterpretq_u32_s16(a);
    let expected = unsafe { vreinterpretq_u32_s16(a) };
    assert!(uint32x4_eq(result, expected));
}

#[test]
fn test_vreinterpretq_s16_u32() {
    let a = _vdupq_n_u32(0x12345678);
    let result = _vreinterpretq_s16_u32(a);
    let expected = unsafe { vreinterpretq_s16_u32(a) };
    assert!(int16x8_eq(result, expected));
}

#[test]
fn test_vreinterpretq_s16_s32() {
    let a = _vreinterpretq_s32_u32(_vdupq_n_u32(0x12345678));
    let result = _vreinterpretq_s16_s32(a);
    let expected = unsafe { vreinterpretq_s16_s32(a) };
    assert!(int16x8_eq(result, expected));
}

#[test]
fn test_vreinterpretq_s32_s16() {
    let a = _vdupq_n_s16(0x1234);
    let result = _vreinterpretq_s32_s16(a);
    let expected = unsafe { vreinterpretq_s32_s16(a) };
    assert!(int32x4_eq(result, expected));
}

#[test]
fn test_vreinterpretq_s16_s64() {
    let a = _vreinterpretq_s64_s16(_vdupq_n_s16(0x1234));
    let result = _vreinterpretq_s16_s64(a);
    let expected = unsafe { vreinterpretq_s16_s64(a) };
    assert!(int16x8_eq(result, expected));
}

#[test]
fn test_vreinterpretq_s64_s16() {
    let a = _vdupq_n_s16(0x1234);
    let result = _vreinterpretq_s64_s16(a);
    let expected = unsafe { vreinterpretq_s64_s16(a) };
    assert!(int64x2_eq(result, expected));
}

#[test]
fn test_vreinterpretq_u8_s16() {
    let a = _vdupq_n_s16(0x1234);
    let result = _vreinterpretq_u8_s16(a);
    let expected = unsafe { vreinterpretq_u8_s16(a) };
    assert!(uint8x16_eq(result, expected));
}

#[test]
fn test_vreinterpretq_s16_u8() {
    let a = _vdupq_n_u8(0x42);
    let result = _vreinterpretq_s16_u8(a);
    let expected = unsafe { vreinterpretq_s16_u8(a) };
    assert!(int16x8_eq(result, expected));
}

#[test]
fn test_vreinterpretq_u16_u8() {
    let a = _vdupq_n_u8(0x42);
    let result = _vreinterpretq_u16_u8(a);
    let expected = unsafe { vreinterpretq_u16_u8(a) };
    assert!(uint16x8_eq(result, expected));
}

#[test]
fn test_vreinterpretq_s64_s32() {
    let a = _vreinterpretq_s32_u32(_vdupq_n_u32(0x12345678));
    let result = _vreinterpretq_s64_s32(a);
    let expected = unsafe { vreinterpretq_s64_s32(a) };
    assert!(int64x2_eq(result, expected));
}

#[test]
fn test_vreinterpretq_u8_s64() {
    let a = _vreinterpretq_s64_s16(_vdupq_n_s16(0x1234));
    let result = _vreinterpretq_u8_s64(a);
    let expected = unsafe { vreinterpretq_u8_s64(a) };
    assert!(uint8x16_eq(result, expected));
}

// =============================================================================
// Transpose Tests
// =============================================================================

#[test]
fn test_vtrn1q_s16() {
    let a = _vdupq_n_s16(1);
    let b = _vdupq_n_s16(2);
    let result = _vtrn1q_s16(a, b);
    let expected = unsafe { vtrn1q_s16(a, b) };
    assert!(int16x8_eq(result, expected));
}

#[test]
fn test_vtrn2q_s16() {
    let a = _vdupq_n_s16(1);
    let b = _vdupq_n_s16(2);
    let result = _vtrn2q_s16(a, b);
    let expected = unsafe { vtrn2q_s16(a, b) };
    assert!(int16x8_eq(result, expected));
}

#[test]
fn test_vtrn1q_s32() {
    let a = _vreinterpretq_s32_u32(_vdupq_n_u32(1));
    let b = _vreinterpretq_s32_u32(_vdupq_n_u32(2));
    let result = _vtrn1q_s32(a, b);
    let expected = unsafe { vtrn1q_s32(a, b) };
    assert!(int32x4_eq(result, expected));
}

#[test]
fn test_vtrn2q_s32() {
    let a = _vreinterpretq_s32_u32(_vdupq_n_u32(1));
    let b = _vreinterpretq_s32_u32(_vdupq_n_u32(2));
    let result = _vtrn2q_s32(a, b);
    let expected = unsafe { vtrn2q_s32(a, b) };
    assert!(int32x4_eq(result, expected));
}

#[test]
fn test_vtrn1q_s64() {
    let a = _vreinterpretq_s64_s16(_vdupq_n_s16(1));
    let b = _vreinterpretq_s64_s16(_vdupq_n_s16(2));
    let result = _vtrn1q_s64(a, b);
    let expected = unsafe { vtrn1q_s64(a, b) };
    assert!(int64x2_eq(result, expected));
}

#[test]
fn test_vtrn2q_s64() {
    let a = _vreinterpretq_s64_s16(_vdupq_n_s16(1));
    let b = _vreinterpretq_s64_s16(_vdupq_n_s16(2));
    let result = _vtrn2q_s64(a, b);
    let expected = unsafe { vtrn2q_s64(a, b) };
    assert!(int64x2_eq(result, expected));
}

#[test]
fn test_vtrn1q_u64() {
    let a = _vdupq_n_u64(1);
    let b = _vdupq_n_u64(2);
    let result = _vtrn1q_u64(a, b);
    let expected = unsafe { vtrn1q_u64(a, b) };
    assert!(uint64x2_eq(result, expected));
}

#[test]
fn test_vtrn2q_u64() {
    let a = _vdupq_n_u64(1);
    let b = _vdupq_n_u64(2);
    let result = _vtrn2q_u64(a, b);
    let expected = unsafe { vtrn2q_u64(a, b) };
    assert!(uint64x2_eq(result, expected));
}

// =============================================================================
// Multiply Long/Accumulate Tests
// =============================================================================

#[test]
fn test_vmull_s16() {
    let a = _vget_low_s16(_vdupq_n_s16(10));
    let b = _vget_low_s16(_vdupq_n_s16(20));
    let result = _vmull_s16(a, b);
    let expected = unsafe { vmull_s16(a, b) };
    assert!(int32x4_eq(result, expected));
}

#[test]
fn test_vget_low_s16() {
    let a = _vdupq_n_s16(42);
    let result = _vget_low_s16(a);
    let expected = unsafe { vget_low_s16(a) };
    assert!(int16x4_eq(result, expected));
}

#[test]
fn test_vmull_high_s16() {
    let a = _vdupq_n_s16(10);
    let b = _vdupq_n_s16(20);
    let result = _vmull_high_s16(a, b);
    let expected = unsafe { vmull_high_s16(a, b) };
    assert!(int32x4_eq(result, expected));
}

#[test]
fn test_vmlal_s16() {
    let acc = _vreinterpretq_s32_u32(_vdupq_n_u32(100));
    let a = _vget_low_s16(_vdupq_n_s16(10));
    let b = _vget_low_s16(_vdupq_n_s16(20));
    let result = _vmlal_s16(acc, a, b);
    let expected = unsafe { vmlal_s16(acc, a, b) };
    assert!(int32x4_eq(result, expected));
}

#[test]
fn test_vmlal_high_s16() {
    let acc = _vreinterpretq_s32_u32(_vdupq_n_u32(100));
    let a = _vdupq_n_s16(10);
    let b = _vdupq_n_s16(20);
    let result = _vmlal_high_s16(acc, a, b);
    let expected = unsafe { vmlal_high_s16(acc, a, b) };
    assert!(int32x4_eq(result, expected));
}

// =============================================================================
// Table Lookup Tests
// =============================================================================

#[test]
fn test_vqtbl1q_u8() {
    let table: [u8; 16] = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15];
    let t = _vld1q_u8(&table);
    let idx: [u8; 16] = [15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0];
    let i = _vld1q_u8(&idx);
    let result = _vqtbl1q_u8(t, i);
    let expected = unsafe { vqtbl1q_u8(t, i) };
    assert!(uint8x16_eq(result, expected));
}

// =============================================================================
// Horizontal Reduction Tests
// =============================================================================

#[test]
fn test_vaddv_u16() {
    let a = _vget_low_u16(_vdupq_n_u16(10));
    let result = _vaddv_u16(a);
    let expected = unsafe { vaddv_u16(a) };
    assert_eq!(result, expected);
}

#[test]
fn test_vget_low_u16() {
    let a = _vdupq_n_u16(42);
    let result = _vget_low_u16(a);
    let expected = unsafe { vget_low_u16(a) };
    assert!(uint16x4_eq(result, expected));
}

#[test]
fn test_vget_high_u16() {
    let a = _vdupq_n_u16(42);
    let result = _vget_high_u16(a);
    let expected = unsafe { vget_high_u16(a) };
    assert!(uint16x4_eq(result, expected));
}

#[test]
fn test_vaddvq_s16() {
    let a = _vdupq_n_s16(10);
    let result = _vaddvq_s16(a);
    let expected = unsafe { vaddvq_s16(a) };
    assert_eq!(result, expected);
}

#[test]
fn test_vaddvq_u16() {
    let a = _vdupq_n_u16(10);
    let result = _vaddvq_u16(a);
    let expected = unsafe { vaddvq_u16(a) };
    assert_eq!(result, expected);
}

// =============================================================================
// Shift and Insert Tests
// =============================================================================

#[test]
fn test_vsliq_n_s32() {
    let a = _vreinterpretq_s32_u32(_vdupq_n_u32(0x0000FFFF));
    let b = _vreinterpretq_s32_u32(_vdupq_n_u32(0x12345678));
    let result = _vsliq_n_s32::<16>(a, b);
    let expected = unsafe { vsliq_n_s32::<16>(a, b) };
    assert!(int32x4_eq(result, expected));
}

#[test]
fn test_vsliq_n_s64() {
    let a = _vreinterpretq_s64_s16(_vdupq_n_s16(0x00FF));
    let b = _vreinterpretq_s64_s16(_vdupq_n_s16(0x1234));
    let result = _vsliq_n_s64::<32>(a, b);
    let expected = unsafe { vsliq_n_s64::<32>(a, b) };
    assert!(int64x2_eq(result, expected));
}

// =============================================================================
// Extract Tests (testing the potentially buggy function)
// =============================================================================

#[test]
fn test_vextq_u32() {
    let a = _vdupq_n_u32(1);
    let b = _vdupq_n_u32(2);

    // Test with N = 0
    let result_0 = _vextq_u32::<0>(a, b);
    let expected_0 = unsafe { vextq_u32::<0>(a, b) };
    assert!(uint32x4_eq(result_0, expected_0));

    // Test with N = 1
    let result_1 = _vextq_u32::<1>(a, b);
    let expected_1 = unsafe { vextq_u32::<1>(a, b) };
    assert!(uint32x4_eq(result_1, expected_1));

    // Test with N = 2
    let result_2 = _vextq_u32::<2>(a, b);
    let expected_2 = unsafe { vextq_u32::<2>(a, b) };
    assert!(uint32x4_eq(result_2, expected_2));

    // Test with N = 3
    let result_3 = _vextq_u32::<3>(a, b);
    let expected_3 = unsafe { vextq_u32::<3>(a, b) };
    assert!(uint32x4_eq(result_3, expected_3));
}

// =============================================================================
// Duplicate Lane Tests (testing the potentially buggy function)
// =============================================================================

#[test]
fn test_vdupq_laneq_u32() {
    let input: [u32; 4] = [1, 2, 3, 4];
    let a = _vld1q_u32(&input);

    let result_0 = _vdupq_laneq_u32::<0>(a);
    let expected_0 = unsafe { vdupq_laneq_u32::<0>(a) };
    assert!(uint32x4_eq(result_0, expected_0));

    let result_1 = _vdupq_laneq_u32::<1>(a);
    let expected_1 = unsafe { vdupq_laneq_u32::<1>(a) };
    assert!(uint32x4_eq(result_1, expected_1));

    let result_2 = _vdupq_laneq_u32::<2>(a);
    let expected_2 = unsafe { vdupq_laneq_u32::<2>(a) };
    assert!(uint32x4_eq(result_2, expected_2));

    let result_3 = _vdupq_laneq_u32::<3>(a);
    let expected_3 = unsafe { vdupq_laneq_u32::<3>(a) };
    assert!(uint32x4_eq(result_3, expected_3));
}

// =============================================================================
// Polynomial Multiply Tests
// =============================================================================

#[test]
fn test_vmull_p64() {
    let a: u64 = 0x123456789ABCDEF0;
    let b: u64 = 0xFEDCBA9876543210;
    let result = _vmull_p64(a, b);
    let expected = unsafe { vmull_p64(a, b) };
    assert_eq!(result, expected);
}

// =============================================================================
// SHA3 Extension Tests (with fallback verification)
// =============================================================================

#[test]
fn test_vrax1q_u64() {
    let a = _vdupq_n_u64(0x123456789ABCDEF0);
    let b = _vdupq_n_u64(0xFEDCBA9876543210);
    let result = _vrax1q_u64(a, b);

    // Verify against manual computation: a XOR (b rotated left by 1)
    // Rotate left by 1 = (b << 1) | (b >> 63)
    let b_rotl1 = _veorq_u64(_vshlq_n_u64::<1>(b), _vshrq_n_u64::<63>(b));
    let expected_manual = _veorq_u64(a, b_rotl1);
    assert!(uint64x2_eq(result, expected_manual));
}

#[test]
fn test_veor3q_u64() {
    let a = _vdupq_n_u64(0x123456789ABCDEF0);
    let b = _vdupq_n_u64(0xFEDCBA9876543210);
    let c = _vdupq_n_u64(0x1111111111111111);
    let result = _veor3q_u64(a, b, c);

    // Verify against manual computation: a XOR b XOR c
    let expected_manual = _veorq_u64(a, _veorq_u64(b, c));
    assert!(uint64x2_eq(result, expected_manual));
}

#[test]
fn test_vxarq_u64() {
    let a = _vdupq_n_u64(0x123456789ABCDEF0);
    let b = _vdupq_n_u64(0xFEDCBA9876543210);

    // Test rotation by various amounts
    let result = _vxarq_u64::<60, 4>(a, b);

    // Verify: (a XOR b) rotated right by 4
    let a_xor_b = _veorq_u64(a, b);
    // Rotate right by 4 = (x >> 4) | (x << 60)
    let expected_manual = _veorq_u64(_vshlq_n_u64::<60>(a_xor_b), _vshrq_n_u64::<4>(a_xor_b));
    assert!(uint64x2_eq(result, expected_manual));
}

#[test]
fn test_vbcaxq_u64() {
    let a = _vdupq_n_u64(0x123456789ABCDEF0);
    let b = _vdupq_n_u64(0xFEDCBA9876543210);
    let c = _vdupq_n_u64(0x1111111111111111);
    let result = _vbcaxq_u64(a, b, c);

    // Verify against manual computation: a XOR (b AND NOT c)
    let expected_manual = _veorq_u64(a, _vbicq_u64(b, c));
    assert!(uint64x2_eq(result, expected_manual));
}

// =============================================================================
// AES Tests
// =============================================================================

#[cfg(target_feature = "aes")]
#[test]
fn test_vaesmcq_u8() {
    let data: [u8; 16] = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15];
    let input = _vld1q_u8(&data);
    let result = _vaesmcq_u8(input);
    let expected = unsafe { vaesmcq_u8(input) };
    assert!(uint8x16_eq(result, expected));
}

#[cfg(target_feature = "aes")]
#[test]
fn test_vaeseq_u8() {
    let data: [u8; 16] = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15];
    let key: [u8; 16] = [15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0];
    let input = _vld1q_u8(&data);
    let k = _vld1q_u8(&key);
    let result = _vaeseq_u8(input, k);
    let expected = unsafe { vaeseq_u8(input, k) };
    assert!(uint8x16_eq(result, expected));
}
