//! This file does not contain correct function signatures!
//! Replace with a hand-written file after extraction.

#![allow(unused_variables, non_camel_case_types)]

pub type Vec256 = u8;
pub type Vec128 = u8;
pub type Vec256Float = u8;

pub fn mm256_storeu_si256_u8(output: &mut [u8], vector: Vec256) {
    debug_assert_eq!(output.len(), 32);
    unimplemented!()
}
pub fn mm256_storeu_si256_i16(output: &mut [i16], vector: Vec256) {
    debug_assert_eq!(output.len(), 16);
    unimplemented!()
}
pub fn mm256_storeu_si256_i32(output: &mut [i32], vector: Vec256) {
    debug_assert_eq!(output.len(), 8);
    unimplemented!()
}

pub fn mm_storeu_si128(output: &mut [i16], vector: Vec128) {
    debug_assert!(output.len() >= 8);
    unimplemented!()
}
pub fn mm_storeu_si128_i32(output: &mut [i32], vector: Vec128) {
    debug_assert_eq!(output.len(), 4);
    unimplemented!()
}

pub fn mm_storeu_bytes_si128(output: &mut [u8], vector: Vec128) {
    debug_assert_eq!(output.len(), 16);
    unimplemented!()
}

pub fn mm_loadu_si128(input: &[u8]) -> Vec128 {
    debug_assert_eq!(input.len(), 16);
    unimplemented!()
}

pub fn mm256_loadu_si256_u8(input: &[u8]) -> Vec256 {
    debug_assert_eq!(input.len(), 32);
    unimplemented!()
}
pub fn mm256_loadu_si256_i16(input: &[i16]) -> Vec256 {
    debug_assert_eq!(input.len(), 16);
    unimplemented!()
}
pub fn mm256_loadu_si256_i32(input: &[i32]) -> Vec256 {
    debug_assert_eq!(input.len(), 8);
    unimplemented!()
}

pub fn mm256_setzero_si256() -> Vec256 {
    unimplemented!()
}
pub fn mm256_set_m128i(hi: Vec128, lo: Vec128) -> Vec256 {
    unimplemented!()
}

pub fn mm_set_epi8(
    byte15: u8,
    byte14: u8,
    byte13: u8,
    byte12: u8,
    byte11: u8,
    byte10: u8,
    byte9: u8,
    byte8: u8,
    byte7: u8,
    byte6: u8,
    byte5: u8,
    byte4: u8,
    byte3: u8,
    byte2: u8,
    byte1: u8,
    byte0: u8,
) -> Vec128 {
    unimplemented!()
}

pub fn mm256_set_epi8(
    byte31: i8,
    byte30: i8,
    byte29: i8,
    byte28: i8,
    byte27: i8,
    byte26: i8,
    byte25: i8,
    byte24: i8,
    byte23: i8,
    byte22: i8,
    byte21: i8,
    byte20: i8,
    byte19: i8,
    byte18: i8,
    byte17: i8,
    byte16: i8,
    byte15: i8,
    byte14: i8,
    byte13: i8,
    byte12: i8,
    byte11: i8,
    byte10: i8,
    byte9: i8,
    byte8: i8,
    byte7: i8,
    byte6: i8,
    byte5: i8,
    byte4: i8,
    byte3: i8,
    byte2: i8,
    byte1: i8,
    byte0: i8,
) -> Vec256 {
    unimplemented!()
}

pub fn mm256_set1_epi16(constant: i16) -> Vec256 {
    unimplemented!()
}
pub fn mm256_set_epi16(
    input15: i16,
    input14: i16,
    input13: i16,
    input12: i16,
    input11: i16,
    input10: i16,
    input9: i16,
    input8: i16,
    input7: i16,
    input6: i16,
    input5: i16,
    input4: i16,
    input3: i16,
    input2: i16,
    input1: i16,
    input0: i16,
) -> Vec256 {
    unimplemented!()
}

#[inline(always)]
pub fn mm_set1_epi16(constant: i16) -> Vec128 {
    unimplemented!()
}

#[inline(always)]
pub fn mm256_set1_epi32(constant: i32) -> Vec256 {
    unimplemented!()
}

#[inline(always)]
pub fn mm_set_epi32(input3: i32, input2: i32, input1: i32, input0: i32) -> Vec128 {
    unimplemented!()
}
#[inline(always)]
pub fn mm256_set_epi32(
    input7: i32,
    input6: i32,
    input5: i32,
    input4: i32,
    input3: i32,
    input2: i32,
    input1: i32,
    input0: i32,
) -> Vec256 {
    unimplemented!()
}

#[inline(always)]
pub fn mm_add_epi16(lhs: Vec128, rhs: Vec128) -> Vec128 {
    unimplemented!()
}
#[inline(always)]
pub fn mm256_add_epi16(lhs: Vec256, rhs: Vec256) -> Vec256 {
    unimplemented!()
}
#[inline(always)]
pub fn mm256_madd_epi16(lhs: Vec256, rhs: Vec256) -> Vec256 {
    unimplemented!()
}
#[inline(always)]
pub fn mm256_add_epi32(lhs: Vec256, rhs: Vec256) -> Vec256 {
    unimplemented!()
}

#[inline(always)]
pub fn mm256_add_epi64(lhs: Vec256, rhs: Vec256) -> Vec256 {
    unimplemented!()
}

#[inline(always)]
pub fn mm256_abs_epi32(a: Vec256) -> Vec256 {
    unimplemented!()
}

pub fn mm256_sub_epi16(lhs: Vec256, rhs: Vec256) -> Vec256 {
    unimplemented!()
}
pub fn mm256_sub_epi32(lhs: Vec256, rhs: Vec256) -> Vec256 {
    unimplemented!()
}

pub fn mm_sub_epi16(lhs: Vec128, rhs: Vec128) -> Vec128 {
    unimplemented!()
}

pub fn mm256_mullo_epi16(lhs: Vec256, rhs: Vec256) -> Vec256 {
    unimplemented!()
}

pub fn mm_mullo_epi16(lhs: Vec128, rhs: Vec128) -> Vec128 {
    unimplemented!()
}

#[inline(always)]
pub fn mm256_cmpgt_epi16(lhs: Vec256, rhs: Vec256) -> Vec256 {
    unimplemented!()
}
#[inline(always)]
pub fn mm256_cmpgt_epi32(lhs: Vec256, rhs: Vec256) -> Vec256 {
    unimplemented!()
}
#[inline(always)]
pub fn mm256_cmpeq_epi32(a: Vec256, b: Vec256) -> Vec256 {
    unimplemented!()
}

#[inline(always)]
pub fn mm256_sign_epi32(a: Vec256, b: Vec256) -> Vec256 {
    unimplemented!()
}

#[inline(always)]
pub fn mm256_castsi256_ps(a: Vec256) -> Vec256Float {
    unimplemented!()
}

#[inline(always)]
pub fn mm256_movemask_ps(a: Vec256Float) -> i32 {
    unimplemented!()
}

pub fn mm_mulhi_epi16(lhs: Vec128, rhs: Vec128) -> Vec128 {
    unimplemented!()
}

pub fn mm256_mullo_epi32(lhs: Vec256, rhs: Vec256) -> Vec256 {
    unimplemented!()
}

pub fn mm256_mulhi_epi16(lhs: Vec256, rhs: Vec256) -> Vec256 {
    unimplemented!()
}

pub fn mm256_mul_epu32(lhs: Vec256, rhs: Vec256) -> Vec256 {
    unimplemented!()
}

#[inline(always)]
pub fn mm256_mul_epi32(lhs: Vec256, rhs: Vec256) -> Vec256 {
    unimplemented!()
}

#[inline(always)]
pub fn mm256_and_si256(lhs: Vec256, rhs: Vec256) -> Vec256 {
    unimplemented!()
}

#[inline(always)]
pub fn mm256_or_si256(a: Vec256, b: Vec256) -> Vec256 {
    unimplemented!()
}

pub fn mm256_testz_si256(lhs: Vec256, rhs: Vec256) -> i32 {
    unimplemented!()
}

pub fn mm256_xor_si256(lhs: Vec256, rhs: Vec256) -> Vec256 {
    unimplemented!()
}

pub fn mm256_srai_epi16<const SHIFT_BY: i32>(vector: Vec256) -> Vec256 {
    debug_assert!(SHIFT_BY >= 0 && SHIFT_BY < 16);
    unimplemented!()
}
pub fn mm256_srai_epi32<const SHIFT_BY: i32>(vector: Vec256) -> Vec256 {
    debug_assert!(SHIFT_BY >= 0 && SHIFT_BY < 32);
    unimplemented!()
}

pub fn mm256_srli_epi16<const SHIFT_BY: i32>(vector: Vec256) -> Vec256 {
    debug_assert!(SHIFT_BY >= 0 && SHIFT_BY < 16);
    unimplemented!()
}
pub fn mm256_srli_epi32<const SHIFT_BY: i32>(vector: Vec256) -> Vec256 {
    debug_assert!(SHIFT_BY >= 0 && SHIFT_BY < 32);
    unimplemented!()
}

pub fn mm_srli_epi64<const SHIFT_BY: i32>(vector: Vec128) -> Vec128 {
    debug_assert!(SHIFT_BY >= 0 && SHIFT_BY < 64);
    unimplemented!()
}
pub fn mm256_srli_epi64<const SHIFT_BY: i32>(vector: Vec256) -> Vec256 {
    debug_assert!(SHIFT_BY >= 0 && SHIFT_BY < 64);
    unimplemented!()
}

pub fn mm256_slli_epi16<const SHIFT_BY: i32>(vector: Vec256) -> Vec256 {
    debug_assert!(SHIFT_BY >= 0 && SHIFT_BY < 16);
    unimplemented!()
}

pub fn mm256_slli_epi32<const SHIFT_BY: i32>(vector: Vec256) -> Vec256 {
    debug_assert!(SHIFT_BY >= 0 && SHIFT_BY < 32);
    unimplemented!()
}

pub fn mm_shuffle_epi8(vector: Vec128, control: Vec128) -> Vec128 {
    unimplemented!()
}
pub fn mm256_shuffle_epi8(vector: Vec256, control: Vec256) -> Vec256 {
    unimplemented!()
}
pub fn mm256_shuffle_epi32<const CONTROL: i32>(vector: Vec256) -> Vec256 {
    debug_assert!(CONTROL >= 0 && CONTROL < 256);
    unimplemented!()
}

pub fn mm256_permute4x64_epi64<const CONTROL: i32>(vector: Vec256) -> Vec256 {
    debug_assert!(CONTROL >= 0 && CONTROL < 256);
    unimplemented!()
}

pub fn mm256_unpackhi_epi64(lhs: Vec256, rhs: Vec256) -> Vec256 {
    unimplemented!()
}

pub fn mm256_unpacklo_epi32(lhs: Vec256, rhs: Vec256) -> Vec256 {
    unimplemented!()
}

pub fn mm256_unpackhi_epi32(lhs: Vec256, rhs: Vec256) -> Vec256 {
    unimplemented!()
}

pub fn mm256_castsi256_si128(vector: Vec256) -> Vec128 {
    unimplemented!()
}
pub fn mm256_castsi128_si256(vector: Vec128) -> Vec256 {
    unimplemented!()
}

pub fn mm256_cvtepi16_epi32(vector: Vec128) -> Vec256 {
    unimplemented!()
}

pub fn mm_packs_epi16(lhs: Vec128, rhs: Vec128) -> Vec128 {
    unimplemented!()
}
pub fn mm256_packs_epi32(lhs: Vec256, rhs: Vec256) -> Vec256 {
    unimplemented!()
}

pub fn mm256_extracti128_si256<const CONTROL: i32>(vector: Vec256) -> Vec128 {
    debug_assert!(CONTROL == 0 || CONTROL == 1);
    unimplemented!()
}

pub fn mm256_inserti128_si256<const CONTROL: i32>(vector: Vec256, vector_i128: Vec128) -> Vec256 {
    debug_assert!(CONTROL == 0 || CONTROL == 1);
    unimplemented!()
}

#[inline(always)]
pub fn mm256_blend_epi16<const CONTROL: i32>(lhs: Vec256, rhs: Vec256) -> Vec256 {
    debug_assert!(CONTROL >= 0 && CONTROL < 256);
    unimplemented!()
}

#[inline(always)]
pub fn mm256_blend_epi32<const CONTROL: i32>(lhs: Vec256, rhs: Vec256) -> Vec256 {
    debug_assert!(CONTROL >= 0 && CONTROL < 256);
    unimplemented!()
}

// This is essentially _mm256_blendv_ps adapted for use with the Vec256 type.
// It is not offered by the AVX2 instruction set.
#[inline(always)]
pub fn vec256_blendv_epi32(a: Vec256, b: Vec256, mask: Vec256) -> Vec256 {
    unimplemented!()
}

#[inline(always)]
pub fn mm_movemask_epi8(vector: Vec128) -> i32 {
    unimplemented!()
}

#[inline(always)]
pub fn mm256_permutevar8x32_epi32(vector: Vec256, control: Vec256) -> Vec256 {
    unimplemented!()
}

#[inline(always)]
pub fn mm256_srlv_epi32(vector: Vec256, counts: Vec256) -> Vec256 {
    unimplemented!()
}
#[inline(always)]
pub fn mm256_srlv_epi64(vector: Vec256, counts: Vec256) -> Vec256 {
    unimplemented!()
}

pub fn mm_sllv_epi32(vector: Vec128, counts: Vec128) -> Vec128 {
    unimplemented!()
}
pub fn mm256_sllv_epi32(vector: Vec256, counts: Vec256) -> Vec256 {
    unimplemented!()
}

#[inline(always)]
pub fn mm256_slli_epi64<const LEFT: i32>(x: Vec256) -> Vec256 {
    unimplemented!()
}

#[inline(always)]
pub fn mm256_bsrli_epi128<const SHIFT_BY: i32>(x: Vec256) -> Vec256 {
    debug_assert!(SHIFT_BY > 0 && SHIFT_BY < 16);
    unimplemented!()
}

#[inline(always)]
pub fn mm256_andnot_si256(a: Vec256, b: Vec256) -> Vec256 {
    unimplemented!()
}

#[inline(always)]
pub fn mm256_set1_epi64x(a: i64) -> Vec256 {
    unimplemented!()
}
#[inline(always)]
pub fn mm256_set_epi64x(input3: i64, input2: i64, input1: i64, input0: i64) -> Vec256 {
    unimplemented!()
}

#[inline(always)]
pub fn mm256_unpacklo_epi64(a: Vec256, b: Vec256) -> Vec256 {
    unimplemented!()
}

#[inline(always)]
pub fn mm256_permute2x128_si256<const IMM8: i32>(a: Vec256, b: Vec256) -> Vec256 {
    unimplemented!()
}
