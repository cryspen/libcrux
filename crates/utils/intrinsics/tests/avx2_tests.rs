//! Comprehensive tests for AVX2 intrinsic wrappers.
//!
//! These tests verify that each wrapper function in src/avx2.rs behaves
//! identically to its upstream equivalent from core::arch::x86_64.

#![cfg(all(target_arch = "x86_64", target_feature = "avx2"))]

use libcrux_intrinsics::avx2::*;

#[cfg(target_arch = "x86_64")]
use core::arch::x86_64::*;

/// Helper to compare two Vec256 values
fn vec256_eq(a: Vec256, b: Vec256) -> bool {
    unsafe {
        let a_bytes: [u8; 32] = core::mem::transmute(a);
        let b_bytes: [u8; 32] = core::mem::transmute(b);
        a_bytes == b_bytes
    }
}

/// Helper to compare two Vec128 values
fn vec128_eq(a: Vec128, b: Vec128) -> bool {
    unsafe {
        let a_bytes: [u8; 16] = core::mem::transmute(a);
        let b_bytes: [u8; 16] = core::mem::transmute(b);
        a_bytes == b_bytes
    }
}

/// Helper to create a test Vec256 with known values
fn test_vec256() -> Vec256 {
    mm256_set_epi32(7, 6, 5, 4, 3, 2, 1, 0)
}

/// Helper to create a second test Vec256 with different values
fn test_vec256_b() -> Vec256 {
    mm256_set_epi32(15, 14, 13, 12, 11, 10, 9, 8)
}

/// Helper to create a test Vec128 with known values
fn test_vec128() -> Vec128 {
    mm_set_epi32(3, 2, 1, 0)
}

/// Helper to create a second test Vec128 with different values
fn test_vec128_b() -> Vec128 {
    mm_set_epi32(7, 6, 5, 4)
}

// =============================================================================
// Load/Store Tests
// =============================================================================

#[test]
fn test_mm256_loadu_si256_u8() {
    let input: [u8; 32] = [
        0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24,
        25, 26, 27, 28, 29, 30, 31,
    ];
    let result = mm256_loadu_si256_u8(&input);
    let expected = unsafe { _mm256_loadu_si256(input.as_ptr() as *const __m256i) };
    assert!(vec256_eq(result, expected));
}

#[test]
fn test_mm256_loadu_si256_i16() {
    let input: [i16; 16] = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15];
    let result = mm256_loadu_si256_i16(&input);
    let expected = unsafe { _mm256_loadu_si256(input.as_ptr() as *const __m256i) };
    assert!(vec256_eq(result, expected));
}

#[test]
fn test_mm256_loadu_si256_i32() {
    let input: [i32; 8] = [0, 1, 2, 3, 4, 5, 6, 7];
    let result = mm256_loadu_si256_i32(&input);
    let expected = unsafe { _mm256_loadu_si256(input.as_ptr() as *const __m256i) };
    assert!(vec256_eq(result, expected));
}

#[test]
fn test_mm256_storeu_si256_u8() {
    let vec = test_vec256();
    let mut output1: [u8; 32] = [0; 32];
    let mut output2: [u8; 32] = [0; 32];

    mm256_storeu_si256_u8(&mut output1, vec);
    unsafe {
        _mm256_storeu_si256(output2.as_mut_ptr() as *mut __m256i, vec);
    }
    assert_eq!(output1, output2);
}

#[test]
fn test_mm256_storeu_si256_i16() {
    let vec = test_vec256();
    let mut output1: [i16; 16] = [0; 16];
    let mut output2: [i16; 16] = [0; 16];

    mm256_storeu_si256_i16(&mut output1, vec);
    unsafe {
        _mm256_storeu_si256(output2.as_mut_ptr() as *mut __m256i, vec);
    }
    assert_eq!(output1, output2);
}

#[test]
fn test_mm256_storeu_si256_i32() {
    let vec = test_vec256();
    let mut output1: [i32; 8] = [0; 8];
    let mut output2: [i32; 8] = [0; 8];

    mm256_storeu_si256_i32(&mut output1, vec);
    unsafe {
        _mm256_storeu_si256(output2.as_mut_ptr() as *mut __m256i, vec);
    }
    assert_eq!(output1, output2);
}

#[test]
fn test_mm_loadu_si128() {
    let input: [u8; 16] = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15];
    let result = mm_loadu_si128(&input);
    let expected = unsafe { _mm_loadu_si128(input.as_ptr() as *const __m128i) };
    assert!(vec128_eq(result, expected));
}

#[test]
fn test_mm_storeu_si128() {
    let vec = test_vec128();
    let mut output1: [i16; 8] = [0; 8];
    let mut output2: [i16; 8] = [0; 8];

    mm_storeu_si128(&mut output1, vec);
    unsafe {
        _mm_storeu_si128(output2.as_mut_ptr() as *mut __m128i, vec);
    }
    assert_eq!(output1, output2);
}

#[test]
fn test_mm_storeu_si128_u8() {
    let vec = test_vec128();
    let mut output1: [u8; 16] = [0; 16];
    let mut output2: [u8; 16] = [0; 16];

    mm_storeu_si128_u8(&mut output1, vec);
    unsafe {
        _mm_storeu_si128(output2.as_mut_ptr() as *mut __m128i, vec);
    }
    assert_eq!(output1, output2);
}

#[test]
fn test_mm_storeu_bytes_si128() {
    let vec = test_vec128();
    let mut output1: [u8; 16] = [0; 16];
    let mut output2: [u8; 16] = [0; 16];

    mm_storeu_bytes_si128(&mut output1, vec);
    unsafe {
        _mm_storeu_si128(output2.as_mut_ptr() as *mut __m128i, vec);
    }
    assert_eq!(output1, output2);
}

// =============================================================================
// Set/Initialize Tests
// =============================================================================

#[test]
fn test_mm256_setzero_si256() {
    let result = mm256_setzero_si256();
    let expected = unsafe { _mm256_setzero_si256() };
    assert!(vec256_eq(result, expected));
}

#[test]
fn test_mm_setzero_si128() {
    let result = mm_setzero_si128();
    let expected = unsafe { _mm_setzero_si128() };
    assert!(vec128_eq(result, expected));
}

#[test]
fn test_mm256_set_m128i() {
    let hi = test_vec128();
    let lo = test_vec128_b();
    let result = mm256_set_m128i(hi, lo);
    let expected = unsafe { _mm256_set_m128i(hi, lo) };
    assert!(vec256_eq(result, expected));
}

#[test]
fn test_mm256_set1_epi16() {
    let result = mm256_set1_epi16(42);
    let expected = unsafe { _mm256_set1_epi16(42) };
    assert!(vec256_eq(result, expected));
}

#[test]
fn test_mm_set1_epi16() {
    let result = mm_set1_epi16(42);
    let expected = unsafe { _mm_set1_epi16(42) };
    assert!(vec128_eq(result, expected));
}

#[test]
fn test_mm256_set1_epi32() {
    let result = mm256_set1_epi32(42);
    let expected = unsafe { _mm256_set1_epi32(42) };
    assert!(vec256_eq(result, expected));
}

#[test]
fn test_mm256_set1_epi64x() {
    let result = mm256_set1_epi64x(42);
    let expected = unsafe { _mm256_set1_epi64x(42) };
    assert!(vec256_eq(result, expected));
}

#[test]
fn test_mm256_set_epi16() {
    let result = mm256_set_epi16(15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0);
    let expected =
        unsafe { _mm256_set_epi16(15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0) };
    assert!(vec256_eq(result, expected));
}

#[test]
fn test_mm256_set_epi32() {
    let result = mm256_set_epi32(7, 6, 5, 4, 3, 2, 1, 0);
    let expected = unsafe { _mm256_set_epi32(7, 6, 5, 4, 3, 2, 1, 0) };
    assert!(vec256_eq(result, expected));
}

#[test]
fn test_mm256_set_epi64x() {
    let result = mm256_set_epi64x(3, 2, 1, 0);
    let expected = unsafe { _mm256_set_epi64x(3, 2, 1, 0) };
    assert!(vec256_eq(result, expected));
}

#[test]
fn test_mm_set_epi32() {
    let result = mm_set_epi32(3, 2, 1, 0);
    let expected = unsafe { _mm_set_epi32(3, 2, 1, 0) };
    assert!(vec128_eq(result, expected));
}

#[test]
fn test_mm_set_epi8() {
    let result = mm_set_epi8(15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0);
    let expected = unsafe { _mm_set_epi8(15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0) };
    assert!(vec128_eq(result, expected));
}

#[test]
fn test_mm256_set_epi8() {
    let result = mm256_set_epi8(
        31, 30, 29, 28, 27, 26, 25, 24, 23, 22, 21, 20, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10, 9,
        8, 7, 6, 5, 4, 3, 2, 1, 0,
    );
    let expected = unsafe {
        _mm256_set_epi8(
            31, 30, 29, 28, 27, 26, 25, 24, 23, 22, 21, 20, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10,
            9, 8, 7, 6, 5, 4, 3, 2, 1, 0,
        )
    };
    assert!(vec256_eq(result, expected));
}

// =============================================================================
// Arithmetic Tests
// =============================================================================

#[test]
fn test_mm256_add_epi16() {
    let a = mm256_set1_epi16(10);
    let b = mm256_set1_epi16(20);
    let result = mm256_add_epi16(a, b);
    let expected = unsafe { _mm256_add_epi16(a, b) };
    assert!(vec256_eq(result, expected));
}

#[test]
fn test_mm_add_epi16() {
    let a = mm_set1_epi16(10);
    let b = mm_set1_epi16(20);
    let result = mm_add_epi16(a, b);
    let expected = unsafe { _mm_add_epi16(a, b) };
    assert!(vec128_eq(result, expected));
}

#[test]
fn test_mm256_add_epi32() {
    let a = mm256_set1_epi32(10);
    let b = mm256_set1_epi32(20);
    let result = mm256_add_epi32(a, b);
    let expected = unsafe { _mm256_add_epi32(a, b) };
    assert!(vec256_eq(result, expected));
}

#[test]
fn test_mm256_add_epi64() {
    let a = mm256_set1_epi64x(10);
    let b = mm256_set1_epi64x(20);
    let result = mm256_add_epi64(a, b);
    let expected = unsafe { _mm256_add_epi64(a, b) };
    assert!(vec256_eq(result, expected));
}

#[test]
fn test_mm256_sub_epi16() {
    let a = mm256_set1_epi16(30);
    let b = mm256_set1_epi16(10);
    let result = mm256_sub_epi16(a, b);
    let expected = unsafe { _mm256_sub_epi16(a, b) };
    assert!(vec256_eq(result, expected));
}

#[test]
fn test_mm256_sub_epi32() {
    let a = mm256_set1_epi32(30);
    let b = mm256_set1_epi32(10);
    let result = mm256_sub_epi32(a, b);
    let expected = unsafe { _mm256_sub_epi32(a, b) };
    assert!(vec256_eq(result, expected));
}

#[test]
fn test_mm_sub_epi16() {
    let a = mm_set1_epi16(30);
    let b = mm_set1_epi16(10);
    let result = mm_sub_epi16(a, b);
    let expected = unsafe { _mm_sub_epi16(a, b) };
    assert!(vec128_eq(result, expected));
}

#[test]
fn test_mm256_mullo_epi16() {
    let a = mm256_set1_epi16(10);
    let b = mm256_set1_epi16(20);
    let result = mm256_mullo_epi16(a, b);
    let expected = unsafe { _mm256_mullo_epi16(a, b) };
    assert!(vec256_eq(result, expected));
}

#[test]
fn test_mm_mullo_epi16() {
    let a = mm_set1_epi16(10);
    let b = mm_set1_epi16(20);
    let result = mm_mullo_epi16(a, b);
    let expected = unsafe { _mm_mullo_epi16(a, b) };
    assert!(vec128_eq(result, expected));
}

#[test]
fn test_mm256_mullo_epi32() {
    let a = mm256_set1_epi32(10);
    let b = mm256_set1_epi32(20);
    let result = mm256_mullo_epi32(a, b);
    let expected = unsafe { _mm256_mullo_epi32(a, b) };
    assert!(vec256_eq(result, expected));
}

#[test]
fn test_mm256_mulhi_epi16() {
    let a = mm256_set1_epi16(10000);
    let b = mm256_set1_epi16(20000);
    let result = mm256_mulhi_epi16(a, b);
    let expected = unsafe { _mm256_mulhi_epi16(a, b) };
    assert!(vec256_eq(result, expected));
}

#[test]
fn test_mm_mulhi_epi16() {
    let a = mm_set1_epi16(10000);
    let b = mm_set1_epi16(20000);
    let result = mm_mulhi_epi16(a, b);
    let expected = unsafe { _mm_mulhi_epi16(a, b) };
    assert!(vec128_eq(result, expected));
}

#[test]
fn test_mm256_mul_epu32() {
    let a = mm256_set1_epi32(10000);
    let b = mm256_set1_epi32(20000);
    let result = mm256_mul_epu32(a, b);
    let expected = unsafe { _mm256_mul_epu32(a, b) };
    assert!(vec256_eq(result, expected));
}

#[test]
fn test_mm256_mul_epi32() {
    let a = mm256_set1_epi32(10000);
    let b = mm256_set1_epi32(-20000);
    let result = mm256_mul_epi32(a, b);
    let expected = unsafe { _mm256_mul_epi32(a, b) };
    assert!(vec256_eq(result, expected));
}

#[test]
fn test_mm256_madd_epi16() {
    let a = mm256_set1_epi16(10);
    let b = mm256_set1_epi16(20);
    let result = mm256_madd_epi16(a, b);
    let expected = unsafe { _mm256_madd_epi16(a, b) };
    assert!(vec256_eq(result, expected));
}

#[test]
fn test_mm256_abs_epi32() {
    let a = mm256_set_epi32(-7, 6, -5, 4, -3, 2, -1, 0);
    let result = mm256_abs_epi32(a);
    let expected = unsafe { _mm256_abs_epi32(a) };
    assert!(vec256_eq(result, expected));
}

// =============================================================================
// Bitwise Operations Tests
// =============================================================================

#[test]
fn test_mm256_and_si256() {
    let a = mm256_set1_epi32(0xFF00FF00u32 as i32);
    let b = mm256_set1_epi32(0x0F0F0F0F);
    let result = mm256_and_si256(a, b);
    let expected = unsafe { _mm256_and_si256(a, b) };
    assert!(vec256_eq(result, expected));
}

#[test]
fn test_mm256_or_si256() {
    let a = mm256_set1_epi32(0xFF00FF00u32 as i32);
    let b = mm256_set1_epi32(0x0F0F0F0F);
    let result = mm256_or_si256(a, b);
    let expected = unsafe { _mm256_or_si256(a, b) };
    assert!(vec256_eq(result, expected));
}

#[test]
fn test_mm256_xor_si256() {
    let a = mm256_set1_epi32(0xFF00FF00u32 as i32);
    let b = mm256_set1_epi32(0x0F0F0F0F);
    let result = mm256_xor_si256(a, b);
    let expected = unsafe { _mm256_xor_si256(a, b) };
    assert!(vec256_eq(result, expected));
}

#[test]
fn test_mm_xor_si128() {
    let a = mm_set1_epi16(0x00FF);
    let b = mm_set1_epi16(0x0F0F);
    let result = mm_xor_si128(a, b);
    let expected = unsafe { _mm_xor_si128(a, b) };
    assert!(vec128_eq(result, expected));
}

#[test]
fn test_mm256_andnot_si256() {
    let a = mm256_set1_epi32(0xFF00FF00u32 as i32);
    let b = mm256_set1_epi32(0xFFFFFFFFu32 as i32);
    let result = mm256_andnot_si256(a, b);
    let expected = unsafe { _mm256_andnot_si256(a, b) };
    assert!(vec256_eq(result, expected));
}

#[test]
fn test_mm256_testz_si256() {
    let a = mm256_set1_epi32(0xFF00FF00u32 as i32);
    let b = mm256_set1_epi32(0x00FF00FF);
    let result = mm256_testz_si256(a, b);
    let expected = unsafe { _mm256_testz_si256(a, b) };
    assert_eq!(result, expected);
}

// =============================================================================
// Shift Tests
// =============================================================================

#[test]
fn test_mm256_srai_epi16() {
    let a = mm256_set1_epi16(-1024);
    let result = mm256_srai_epi16::<4>(a);
    let expected = unsafe { _mm256_srai_epi16::<4>(a) };
    assert!(vec256_eq(result, expected));
}

#[test]
fn test_mm256_srai_epi32() {
    let a = mm256_set1_epi32(-1024);
    let result = mm256_srai_epi32::<4>(a);
    let expected = unsafe { _mm256_srai_epi32::<4>(a) };
    assert!(vec256_eq(result, expected));
}

#[test]
fn test_mm256_srli_epi16() {
    let a = mm256_set1_epi16(1024);
    let result = mm256_srli_epi16::<4>(a);
    let expected = unsafe { _mm256_srli_epi16::<4>(a) };
    assert!(vec256_eq(result, expected));
}

#[test]
fn test_mm256_srli_epi32() {
    let a = mm256_set1_epi32(1024);
    let result = mm256_srli_epi32::<4>(a);
    let expected = unsafe { _mm256_srli_epi32::<4>(a) };
    assert!(vec256_eq(result, expected));
}

#[test]
fn test_mm256_srli_epi64() {
    let a = mm256_set1_epi64x(1024);
    let result = mm256_srli_epi64::<4>(a);
    let expected = unsafe { _mm256_srli_epi64::<4>(a) };
    assert!(vec256_eq(result, expected));
}

#[test]
fn test_mm_srli_epi64() {
    let a = mm_set_epi32(0, 1024, 0, 2048);
    let result = mm_srli_epi64::<4>(a);
    let expected = unsafe { _mm_srli_epi64::<4>(a) };
    assert!(vec128_eq(result, expected));
}

#[test]
fn test_mm256_slli_epi16() {
    let a = mm256_set1_epi16(1024);
    let result = mm256_slli_epi16::<4>(a);
    let expected = unsafe { _mm256_slli_epi16::<4>(a) };
    assert!(vec256_eq(result, expected));
}

#[test]
fn test_mm256_slli_epi32() {
    let a = mm256_set1_epi32(1024);
    let result = mm256_slli_epi32::<4>(a);
    let expected = unsafe { _mm256_slli_epi32::<4>(a) };
    assert!(vec256_eq(result, expected));
}

#[test]
fn test_mm256_slli_epi64() {
    let a = mm256_set1_epi64x(1024);
    let result = mm256_slli_epi64::<4>(a);
    let expected = unsafe { _mm256_slli_epi64::<4>(a) };
    assert!(vec256_eq(result, expected));
}

#[test]
fn test_mm_slli_si128() {
    let a = test_vec128();
    let result = mm_slli_si128::<4>(a);
    let expected = unsafe { _mm_slli_si128::<4>(a) };
    assert!(vec128_eq(result, expected));
}

#[test]
fn test_mm_srli_si128() {
    let a = test_vec128();
    let result = mm_srli_si128::<4>(a);
    let expected = unsafe { _mm_srli_si128::<4>(a) };
    assert!(vec128_eq(result, expected));
}

#[test]
fn test_mm256_bsrli_epi128() {
    let a = test_vec256();
    let result = mm256_bsrli_epi128::<4>(a);
    let expected = unsafe { _mm256_bsrli_epi128::<4>(a) };
    assert!(vec256_eq(result, expected));
}

#[test]
fn test_mm256_srlv_epi32() {
    let a = mm256_set_epi32(128, 128, 128, 128, 128, 128, 128, 128);
    let counts = mm256_set_epi32(7, 6, 5, 4, 3, 2, 1, 0);
    let result = mm256_srlv_epi32(a, counts);
    let expected = unsafe { _mm256_srlv_epi32(a, counts) };
    assert!(vec256_eq(result, expected));
}

#[test]
fn test_mm256_srlv_epi64() {
    let a = mm256_set_epi64x(128, 128, 128, 128);
    let counts = mm256_set_epi64x(4, 3, 2, 1);
    let result = mm256_srlv_epi64(a, counts);
    let expected = unsafe { _mm256_srlv_epi64(a, counts) };
    assert!(vec256_eq(result, expected));
}

#[test]
fn test_mm_sllv_epi32() {
    let a = mm_set_epi32(1, 1, 1, 1);
    let counts = mm_set_epi32(3, 2, 1, 0);
    let result = mm_sllv_epi32(a, counts);
    let expected = unsafe { _mm_sllv_epi32(a, counts) };
    assert!(vec128_eq(result, expected));
}

#[test]
fn test_mm256_sllv_epi32() {
    let a = mm256_set_epi32(1, 1, 1, 1, 1, 1, 1, 1);
    let counts = mm256_set_epi32(7, 6, 5, 4, 3, 2, 1, 0);
    let result = mm256_sllv_epi32(a, counts);
    let expected = unsafe { _mm256_sllv_epi32(a, counts) };
    assert!(vec256_eq(result, expected));
}

// =============================================================================
// Shuffle/Permute Tests
// =============================================================================

#[test]
fn test_mm_shuffle_epi8() {
    let a = test_vec128();
    let control = mm_set_epi8(15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0);
    let result = mm_shuffle_epi8(a, control);
    let expected = unsafe { _mm_shuffle_epi8(a, control) };
    assert!(vec128_eq(result, expected));
}

#[test]
fn test_mm256_shuffle_epi8() {
    let a = test_vec256();
    let control = mm256_set_epi8(
        15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6,
        5, 4, 3, 2, 1, 0,
    );
    let result = mm256_shuffle_epi8(a, control);
    let expected = unsafe { _mm256_shuffle_epi8(a, control) };
    assert!(vec256_eq(result, expected));
}

#[test]
fn test_mm256_shuffle_epi32() {
    let a = test_vec256();
    let result = mm256_shuffle_epi32::<0b00_01_10_11>(a);
    let expected = unsafe { _mm256_shuffle_epi32::<0b00_01_10_11>(a) };
    assert!(vec256_eq(result, expected));
}

#[test]
fn test_mm_shuffle_epi32() {
    let a = test_vec128();
    let result = mm_shuffle_epi32::<0b00_01_10_11>(a);
    let expected = unsafe { _mm_shuffle_epi32::<0b00_01_10_11>(a) };
    assert!(vec128_eq(result, expected));
}

#[test]
fn test_mm256_permute4x64_epi64() {
    let a = test_vec256();
    let result = mm256_permute4x64_epi64::<0b00_01_10_11>(a);
    let expected = unsafe { _mm256_permute4x64_epi64::<0b00_01_10_11>(a) };
    assert!(vec256_eq(result, expected));
}

#[test]
fn test_mm256_permutevar8x32_epi32() {
    let a = test_vec256();
    let control = mm256_set_epi32(0, 1, 2, 3, 4, 5, 6, 7);
    let result = mm256_permutevar8x32_epi32(a, control);
    let expected = unsafe { _mm256_permutevar8x32_epi32(a, control) };
    assert!(vec256_eq(result, expected));
}

#[test]
fn test_mm256_permute2x128_si256() {
    let a = test_vec256();
    let b = test_vec256_b();
    let result = mm256_permute2x128_si256::<0x21>(a, b);
    let expected = unsafe { _mm256_permute2x128_si256::<0x21>(a, b) };
    assert!(vec256_eq(result, expected));
}

// =============================================================================
// Unpack Tests
// =============================================================================

#[test]
fn test_mm256_unpackhi_epi64() {
    let a = test_vec256();
    let b = test_vec256_b();
    let result = mm256_unpackhi_epi64(a, b);
    let expected = unsafe { _mm256_unpackhi_epi64(a, b) };
    assert!(vec256_eq(result, expected));
}

#[test]
fn test_mm_unpackhi_epi64() {
    let a = test_vec128();
    let b = test_vec128_b();
    let result = mm_unpackhi_epi64(a, b);
    let expected = unsafe { _mm_unpackhi_epi64(a, b) };
    assert!(vec128_eq(result, expected));
}

#[test]
fn test_mm256_unpacklo_epi32() {
    let a = test_vec256();
    let b = test_vec256_b();
    let result = mm256_unpacklo_epi32(a, b);
    let expected = unsafe { _mm256_unpacklo_epi32(a, b) };
    assert!(vec256_eq(result, expected));
}

#[test]
fn test_mm256_unpackhi_epi32() {
    let a = test_vec256();
    let b = test_vec256_b();
    let result = mm256_unpackhi_epi32(a, b);
    let expected = unsafe { _mm256_unpackhi_epi32(a, b) };
    assert!(vec256_eq(result, expected));
}

#[test]
fn test_mm256_unpacklo_epi64() {
    let a = test_vec256();
    let b = test_vec256_b();
    let result = mm256_unpacklo_epi64(a, b);
    let expected = unsafe { _mm256_unpacklo_epi64(a, b) };
    assert!(vec256_eq(result, expected));
}

#[test]
fn test_mm_unpacklo_epi64() {
    let a = test_vec128();
    let b = test_vec128_b();
    let result = mm_unpacklo_epi64(a, b);
    let expected = unsafe { _mm_unpacklo_epi64(a, b) };
    assert!(vec128_eq(result, expected));
}

// =============================================================================
// Compare Tests
// =============================================================================

#[test]
fn test_mm256_cmpgt_epi16() {
    let a = mm256_set1_epi16(10);
    let b = mm256_set1_epi16(5);
    let result = mm256_cmpgt_epi16(a, b);
    let expected = unsafe { _mm256_cmpgt_epi16(a, b) };
    assert!(vec256_eq(result, expected));
}

#[test]
fn test_mm256_cmpgt_epi32() {
    let a = mm256_set1_epi32(10);
    let b = mm256_set1_epi32(5);
    let result = mm256_cmpgt_epi32(a, b);
    let expected = unsafe { _mm256_cmpgt_epi32(a, b) };
    assert!(vec256_eq(result, expected));
}

#[test]
fn test_mm256_cmpeq_epi32() {
    let a = mm256_set_epi32(1, 2, 3, 4, 5, 6, 7, 8);
    let b = mm256_set_epi32(1, 0, 3, 0, 5, 0, 7, 0);
    let result = mm256_cmpeq_epi32(a, b);
    let expected = unsafe { _mm256_cmpeq_epi32(a, b) };
    assert!(vec256_eq(result, expected));
}

#[test]
fn test_mm256_sign_epi32() {
    let a = mm256_set_epi32(1, 2, 3, 4, 5, 6, 7, 8);
    let b = mm256_set_epi32(-1, 1, -1, 1, -1, 1, -1, 1);
    let result = mm256_sign_epi32(a, b);
    let expected = unsafe { _mm256_sign_epi32(a, b) };
    assert!(vec256_eq(result, expected));
}

// =============================================================================
// Cast/Convert Tests
// =============================================================================

#[test]
fn test_mm256_castsi256_si128() {
    let a = test_vec256();
    let result = mm256_castsi256_si128(a);
    let expected = unsafe { _mm256_castsi256_si128(a) };
    assert!(vec128_eq(result, expected));
}

#[test]
fn test_mm256_castsi128_si256() {
    let a = test_vec128();
    let result = mm256_castsi128_si256(a);
    let expected = unsafe { _mm256_castsi128_si256(a) };
    // Only compare lower 128 bits since upper bits are undefined
    let result_lo = mm256_castsi256_si128(result);
    let expected_lo = unsafe { _mm256_castsi256_si128(expected) };
    assert!(vec128_eq(result_lo, expected_lo));
}

#[test]
fn test_mm256_cvtepi16_epi32() {
    let a = mm_set_epi32(0x00040003, 0x00020001, 0x00080007, 0x00060005);
    let result = mm256_cvtepi16_epi32(a);
    let expected = unsafe { _mm256_cvtepi16_epi32(a) };
    assert!(vec256_eq(result, expected));
}

#[test]
fn test_mm_packs_epi16() {
    let a = mm_set1_epi16(100);
    let b = mm_set1_epi16(-100);
    let result = mm_packs_epi16(a, b);
    let expected = unsafe { _mm_packs_epi16(a, b) };
    assert!(vec128_eq(result, expected));
}

#[test]
fn test_mm256_packs_epi32() {
    let a = mm256_set1_epi32(100);
    let b = mm256_set1_epi32(-100);
    let result = mm256_packs_epi32(a, b);
    let expected = unsafe { _mm256_packs_epi32(a, b) };
    assert!(vec256_eq(result, expected));
}

// =============================================================================
// Extract/Insert Tests
// =============================================================================

#[test]
fn test_mm256_extracti128_si256() {
    let a = test_vec256();
    let result_lo = mm256_extracti128_si256::<0>(a);
    let result_hi = mm256_extracti128_si256::<1>(a);
    let expected_lo = unsafe { _mm256_extracti128_si256::<0>(a) };
    let expected_hi = unsafe { _mm256_extracti128_si256::<1>(a) };
    assert!(vec128_eq(result_lo, expected_lo));
    assert!(vec128_eq(result_hi, expected_hi));
}

#[test]
fn test_mm256_inserti128_si256() {
    let a = test_vec256();
    let b = test_vec128();
    let result_lo = mm256_inserti128_si256::<0>(a, b);
    let result_hi = mm256_inserti128_si256::<1>(a, b);
    let expected_lo = unsafe { _mm256_inserti128_si256::<0>(a, b) };
    let expected_hi = unsafe { _mm256_inserti128_si256::<1>(a, b) };
    assert!(vec256_eq(result_lo, expected_lo));
    assert!(vec256_eq(result_hi, expected_hi));
}

// =============================================================================
// Blend Tests
// =============================================================================

#[test]
fn test_mm256_blend_epi16() {
    let a = mm256_set1_epi16(1);
    let b = mm256_set1_epi16(2);
    let result = mm256_blend_epi16::<0b10101010>(a, b);
    let expected = unsafe { _mm256_blend_epi16::<0b10101010>(a, b) };
    assert!(vec256_eq(result, expected));
}

#[test]
fn test_mm256_blend_epi32() {
    let a = mm256_set1_epi32(1);
    let b = mm256_set1_epi32(2);
    let result = mm256_blend_epi32::<0b10101010>(a, b);
    let expected = unsafe { _mm256_blend_epi32::<0b10101010>(a, b) };
    assert!(vec256_eq(result, expected));
}

#[test]
fn test_vec256_blendv_epi32() {
    let a = mm256_set1_epi32(1);
    let b = mm256_set1_epi32(2);
    let mask = mm256_set_epi32(-1, 0, -1, 0, -1, 0, -1, 0);
    let result = vec256_blendv_epi32(a, b, mask);
    let expected = unsafe {
        _mm256_castps_si256(_mm256_blendv_ps(
            _mm256_castsi256_ps(a),
            _mm256_castsi256_ps(b),
            _mm256_castsi256_ps(mask),
        ))
    };
    assert!(vec256_eq(result, expected));
}

// =============================================================================
// Floating Point Cast Tests
// =============================================================================

#[test]
fn test_mm256_castsi256_ps_and_back() {
    let a = test_vec256();
    let ps = mm256_castsi256_ps(a);
    let expected_ps = unsafe { _mm256_castsi256_ps(a) };
    let back = mm256_castps_si256(ps);
    let expected_back = unsafe { _mm256_castps_si256(expected_ps) };
    assert!(vec256_eq(back, expected_back));
}

#[test]
fn test_mm256_movemask_ps() {
    let a = mm256_set_epi32(-1, 0, -1, 0, -1, 0, -1, 0);
    let ps = mm256_castsi256_ps(a);
    let result = mm256_movemask_ps(ps);
    let expected = unsafe { _mm256_movemask_ps(ps) };
    assert_eq!(result, expected);
}

#[test]
fn test_mm_movemask_epi8() {
    let a = mm_set_epi8(-1, 0, -1, 0, -1, 0, -1, 0, -1, 0, -1, 0, -1, 0, -1, 0);
    let result = mm_movemask_epi8(a);
    let expected = unsafe { _mm_movemask_epi8(a) };
    assert_eq!(result, expected);
}

// =============================================================================
// CLMUL Tests (these test the potentially buggy function)
// =============================================================================

#[cfg(target_feature = "pclmulqdq")]
#[test]
fn test_mm_clmulepi64_si128() {
    let a = mm_set_epi32(0, 0x12345678, 0, 0x9ABCDEF0u32 as i32);
    let b = mm_set_epi32(0, 0x11111111, 0, 0x22222222);

    // Test with IMM8 = 0x00 (multiply lower 64-bit parts)
    let result_00 = mm_clmulepi64_si128::<0x00>(a, b);
    let expected_00 = unsafe { _mm_clmulepi64_si128::<0x00>(a, b) };
    assert!(vec128_eq(result_00, expected_00));

    // Test with IMM8 = 0x11 (multiply upper 64-bit parts)
    let result_11 = mm_clmulepi64_si128::<0x11>(a, b);
    let expected_11 = unsafe { _mm_clmulepi64_si128::<0x11>(a, b) };
    assert!(vec128_eq(result_11, expected_11));

    // Test with IMM8 = 0x10 (multiply lower a with upper b)
    let result_10 = mm_clmulepi64_si128::<0x10>(a, b);
    let expected_10 = unsafe { _mm_clmulepi64_si128::<0x10>(a, b) };
    assert!(vec128_eq(result_10, expected_10));
}

// =============================================================================
// AES Tests (these test the potentially buggy function)
// =============================================================================

#[cfg(target_feature = "aes")]
#[test]
fn test_mm_aesenc_si128() {
    let data = mm_set_epi32(0x12345678, 0x9ABCDEF0u32 as i32, 0x11111111, 0x22222222);
    let key = mm_set_epi32(0xAAAAAAAAu32 as i32, 0xBBBBBBBBu32 as i32, 0xCCCCCCCCu32 as i32, 0xDDDDDDDDu32 as i32);
    let result = mm_aesenc_si128(data, key);
    let expected = unsafe { _mm_aesenc_si128(data, key) };
    assert!(vec128_eq(result, expected));
}

#[cfg(target_feature = "aes")]
#[test]
fn test_mm_aesenclast_si128() {
    let data = mm_set_epi32(0x12345678, 0x9ABCDEF0u32 as i32, 0x11111111, 0x22222222);
    let key = mm_set_epi32(0xAAAAAAAAu32 as i32, 0xBBBBBBBBu32 as i32, 0xCCCCCCCCu32 as i32, 0xDDDDDDDDu32 as i32);
    let result = mm_aesenclast_si128(data, key);
    let expected = unsafe { _mm_aesenclast_si128(data, key) };
    assert!(vec128_eq(result, expected));
}

#[cfg(target_feature = "aes")]
#[test]
fn test_mm_aeskeygenassist_si128() {
    let key = mm_set_epi32(0x12345678, 0x9ABCDEF0u32 as i32, 0x11111111, 0x22222222);

    let result_01 = mm_aeskeygenassist_si128::<0x01>(key);
    let expected_01 = unsafe { _mm_aeskeygenassist_si128::<0x01>(key) };
    assert!(vec128_eq(result_01, expected_01));

    let result_02 = mm_aeskeygenassist_si128::<0x02>(key);
    let expected_02 = unsafe { _mm_aeskeygenassist_si128::<0x02>(key) };
    assert!(vec128_eq(result_02, expected_02));
}
