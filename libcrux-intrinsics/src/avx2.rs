#[cfg(target_arch = "x86")]
pub use core::arch::x86::*;
#[cfg(target_arch = "x86_64")]
pub use core::arch::x86_64::*;

use libcrux_secrets::*;

pub type Vec256 = Secret<__m256i>;
pub type Vec128 = Secret<__m128i>;
pub type Vec256Float = Secret<__m256>;

#[inline(always)]
pub fn mm256_storeu_si256_u8(output: &mut [u8], vector: Vec256) {
    debug_assert_eq!(output.len(), 32);
    unsafe {
        _mm256_storeu_si256(output.as_mut_ptr() as *mut __m256i, vector.declassify());
    }
}
#[inline(always)]
pub fn mm256_storeu_si256_i16(output: &mut [i16], vector: Vec256) {
    debug_assert_eq!(output.len(), 16);
    unsafe {
        _mm256_storeu_si256(output.as_mut_ptr() as *mut __m256i, vector.declassify());
    }
}
#[inline(always)]
pub fn mm256_storeu_si256_i32(output: &mut [i32], vector: Vec256) {
    debug_assert_eq!(output.len(), 8);
    unsafe {
        _mm256_storeu_si256(output.as_mut_ptr() as *mut __m256i, vector.declassify());
    }
}

#[inline(always)]
pub fn mm_storeu_si128(output: &mut [i16], vector: Vec128) {
    debug_assert!(output.len() >= 8);
    unsafe {
        _mm_storeu_si128(output.as_mut_ptr() as *mut __m128i, vector.declassify());
    }
}
#[inline(always)]
pub fn mm_storeu_si128_i32(output: &mut [i32], vector: Vec128) {
    debug_assert_eq!(output.len(), 4);
    unsafe {
        _mm_storeu_si128(output.as_mut_ptr() as *mut __m128i, vector.declassify());
    }
}

#[inline(always)]
pub fn mm_storeu_bytes_si128(output: &mut [u8], vector: Vec128) {
    debug_assert_eq!(output.len(), 16);
    unsafe {
        _mm_storeu_si128(output.as_mut_ptr() as *mut __m128i, vector.declassify());
    }
}

#[inline(always)]
pub fn mm_loadu_si128(input: &[U8]) -> Vec128 {
    debug_assert_eq!(input.len(), 16);
    unsafe { _mm_loadu_si128(input.declassify().as_ptr() as *const __m128i).classify() }
}

#[inline(always)]
pub fn mm256_loadu_si256_u8(input: &[U8]) -> Vec256 {
    debug_assert_eq!(input.len(), 32);
    unsafe { _mm256_loadu_si256(input.declassify().as_ptr() as *const __m256i).classify() }
}
#[inline(always)]
pub fn mm256_loadu_si256_i16(input: &[I16]) -> Vec256 {
    debug_assert_eq!(input.len(), 16);
    unsafe { _mm256_loadu_si256(input.declassify().as_ptr() as *const __m256i).classify() }
}
#[inline(always)]
pub fn mm256_loadu_si256_i32(input: &[I32]) -> Vec256 {
    debug_assert_eq!(input.len(), 8);
    unsafe { _mm256_loadu_si256(input.declassify().as_ptr() as *const __m256i).classify() }
}

#[inline(always)]
pub fn mm256_setzero_si256() -> Vec256 {
    unsafe { _mm256_setzero_si256().classify() }
}
#[inline(always)]
pub fn mm256_set_m128i(hi: Vec128, lo: Vec128) -> Vec256 {
    unsafe { _mm256_set_m128i(hi.declassify(), lo.declassify()).classify() }
}

#[inline(always)]
pub fn mm_set_epi8(
    byte15: U8,
    byte14: U8,
    byte13: U8,
    byte12: U8,
    byte11: U8,
    byte10: U8,
    byte9: U8,
    byte8: U8,
    byte7: U8,
    byte6: U8,
    byte5: U8,
    byte4: U8,
    byte3: U8,
    byte2: U8,
    byte1: U8,
    byte0: U8,
) -> Vec128 {
    unsafe {
        _mm_set_epi8(
            byte15.declassify() as i8,
            byte14.declassify() as i8,
            byte13.declassify() as i8,
            byte12.declassify() as i8,
            byte11.declassify() as i8,
            byte10.declassify() as i8,
            byte9.declassify() as i8,
            byte8.declassify() as i8,
            byte7.declassify() as i8,
            byte6.declassify() as i8,
            byte5.declassify() as i8,
            byte4.declassify() as i8,
            byte3.declassify() as i8,
            byte2.declassify() as i8,
            byte1.declassify() as i8,
            byte0.declassify() as i8,
        ).classify()
    }
}

#[inline(always)]
pub fn mm256_set_epi8(
    byte31: I8,
    byte30: I8,
    byte29: I8,
    byte28: I8,
    byte27: I8,
    byte26: I8,
    byte25: I8,
    byte24: I8,
    byte23: I8,
    byte22: I8,
    byte21: I8,
    byte20: I8,
    byte19: I8,
    byte18: I8,
    byte17: I8,
    byte16: I8,
    byte15: I8,
    byte14: I8,
    byte13: I8,
    byte12: I8,
    byte11: I8,
    byte10: I8,
    byte9: I8,
    byte8: I8,
    byte7: I8,
    byte6: I8,
    byte5: I8,
    byte4: I8,
    byte3: I8,
    byte2: I8,
    byte1: I8,
    byte0: I8,
) -> Vec256 {
    unsafe {
        _mm256_set_epi8(
            byte31.declassify(), byte30.declassify(), byte29.declassify(), byte28.declassify(), 
            byte27.declassify(), byte26.declassify(), byte25.declassify(), byte24.declassify(), 
            byte23.declassify(), byte22.declassify(), byte21.declassify(), byte20.declassify(), 
            byte19.declassify(), byte18.declassify(), byte17.declassify(), byte16.declassify(), 
            byte15.declassify(), byte14.declassify(), byte13.declassify(), byte12.declassify(), 
            byte11.declassify(), byte10.declassify(), byte9.declassify(), byte8.declassify(), 
            byte7.declassify(), byte6.declassify(), byte5.declassify(), byte4.declassify(), 
            byte3.declassify(), byte2.declassify(), byte1.declassify(), byte0.declassify(),
        ).classify()
    }
}

#[inline(always)]
pub fn mm256_set1_epi16(constant: I16) -> Vec256 {
    unsafe { _mm256_set1_epi16(constant.declassify()).classify() }
}
#[inline(always)]
pub fn mm256_set_epi16(
    input15: I16,
    input14: I16,
    input13: I16,
    input12: I16,
    input11: I16,
    input10: I16,
    input9: I16,
    input8: I16,
    input7: I16,
    input6: I16,
    input5: I16,
    input4: I16,
    input3: I16,
    input2: I16,
    input1: I16,
    input0: I16,
) -> Vec256 {
    unsafe {
        _mm256_set_epi16(
            input15.declassify(), input14.declassify(), input13.declassify(), input12.declassify(), 
            input11.declassify(), input10.declassify(), input9.declassify(), input8.declassify(), 
            input7.declassify(), input6.declassify(), input5.declassify(), input4.declassify(), 
            input3.declassify(), input2.declassify(), input1.declassify(), input0.declassify(),
        ).classify()
    }
}

#[inline(always)]
pub fn mm_set1_epi16(constant: I16) -> Vec128 {
    unsafe { _mm_set1_epi16(constant.declassify()).classify() }
}

#[inline(always)]
pub fn mm256_set1_epi32(constant: I32) -> Vec256 {
    unsafe { _mm256_set1_epi32(constant.declassify()).classify() }
}

#[inline(always)]
pub fn mm_set_epi32(input3: I32, input2: I32, input1: I32, input0: I32) -> Vec128 {
    unsafe { _mm_set_epi32(input3.declassify(), input2.declassify(), input1.declassify(), input0.declassify()).classify() }
}
#[inline(always)]
pub fn mm256_set_epi32(
    input7: I32,
    input6: I32,
    input5: I32,
    input4: I32,
    input3: I32,
    input2: I32,
    input1: I32,
    input0: I32,
) -> Vec256 {
    unsafe {
        _mm256_set_epi32(
            input7.declassify(), input6.declassify(), input5.declassify(), input4.declassify(), 
            input3.declassify(), input2.declassify(), input1.declassify(), input0.declassify(),
        ).classify()
    }
}

#[inline(always)]
pub fn mm_add_epi16(lhs: Vec128, rhs: Vec128) -> Vec128 {
    unsafe { _mm_add_epi16(lhs.declassify(), rhs.declassify()).classify() }
}
#[inline(always)]
pub fn mm256_add_epi16(lhs: Vec256, rhs: Vec256) -> Vec256 {
    unsafe { _mm256_add_epi16(lhs.declassify(), rhs.declassify()).classify() }
}
#[inline(always)]
pub fn mm256_madd_epi16(lhs: Vec256, rhs: Vec256) -> Vec256 {
    unsafe { _mm256_madd_epi16(lhs.declassify(), rhs.declassify()).classify() }
}
#[inline(always)]
pub fn mm256_add_epi32(lhs: Vec256, rhs: Vec256) -> Vec256 {
    unsafe { _mm256_add_epi32(lhs.declassify(), rhs.declassify()).classify() }
}

#[inline(always)]
pub fn mm256_add_epi64(lhs: Vec256, rhs: Vec256) -> Vec256 {
    unsafe { _mm256_add_epi64(lhs.declassify(), rhs.declassify()).classify() }
}

#[inline(always)]
pub fn mm256_abs_epi32(a: Vec256) -> Vec256 {
    unsafe { _mm256_abs_epi32(a.declassify()).classify() }
}

#[inline(always)]
pub fn mm256_sub_epi16(lhs: Vec256, rhs: Vec256) -> Vec256 {
    unsafe { _mm256_sub_epi16(lhs.declassify(), rhs.declassify()).classify() }
}
#[inline(always)]
pub fn mm256_sub_epi32(lhs: Vec256, rhs: Vec256) -> Vec256 {
    unsafe { _mm256_sub_epi32(lhs.declassify(), rhs.declassify()).classify() }
}

#[inline(always)]
pub fn mm_sub_epi16(lhs: Vec128, rhs: Vec128) -> Vec128 {
    unsafe { _mm_sub_epi16(lhs.declassify(), rhs.declassify()).classify() }
}

#[inline(always)]
pub fn mm256_mullo_epi16(lhs: Vec256, rhs: Vec256) -> Vec256 {
    unsafe { _mm256_mullo_epi16(lhs.declassify(), rhs.declassify()).classify() }
}

#[inline(always)]
pub fn mm_mullo_epi16(lhs: Vec128, rhs: Vec128) -> Vec128 {
    unsafe { _mm_mullo_epi16(lhs.declassify(), rhs.declassify()).classify() }
}

#[inline(always)]
pub fn mm256_cmpgt_epi16(lhs: Vec256, rhs: Vec256) -> Vec256 {
    unsafe { _mm256_cmpgt_epi16(lhs.declassify(), rhs.declassify()).classify() }
}
#[inline(always)]
pub fn mm256_cmpgt_epi32(lhs: Vec256, rhs: Vec256) -> Vec256 {
    unsafe { _mm256_cmpgt_epi32(lhs.declassify(), rhs.declassify()).classify() }
}
#[inline(always)]
pub fn mm256_cmpeq_epi32(a: Vec256, b: Vec256) -> Vec256 {
    unsafe { _mm256_cmpeq_epi32(a.declassify(), b.declassify()).classify() }
}

#[inline(always)]
pub fn mm256_sign_epi32(a: Vec256, b: Vec256) -> Vec256 {
    unsafe { _mm256_sign_epi32(a.declassify(), b.declassify()).classify() }
}

#[inline(always)]
pub fn mm256_castsi256_ps(a: Vec256) -> Vec256Float {
    unsafe { _mm256_castsi256_ps(a.declassify()).classify() }
}

#[inline(always)]
pub fn mm256_castps_si256(a: Vec256Float) -> Vec256 {
    unsafe { _mm256_castps_si256(a.declassify()).classify() }
}

#[inline(always)]
pub fn mm256_movemask_ps(a: Vec256Float) -> I32 {
    unsafe { _mm256_movemask_ps(a.declassify()).classify() }
}

#[inline(always)]
pub fn mm_mulhi_epi16(lhs: Vec128, rhs: Vec128) -> Vec128 {
    unsafe { _mm_mulhi_epi16(lhs.declassify(), rhs.declassify()).classify() }
}

#[inline(always)]
pub fn mm256_mullo_epi32(lhs: Vec256, rhs: Vec256) -> Vec256 {
    unsafe { _mm256_mullo_epi32(lhs.declassify(), rhs.declassify()).classify() }
}

#[inline(always)]
pub fn mm256_mulhi_epi16(lhs: Vec256, rhs: Vec256) -> Vec256 {
    unsafe { _mm256_mulhi_epi16(lhs.declassify(), rhs.declassify()).classify() }
}

#[inline(always)]
pub fn mm256_mul_epu32(lhs: Vec256, rhs: Vec256) -> Vec256 {
    unsafe { _mm256_mul_epu32(lhs.declassify(), rhs.declassify()).classify() }
}

#[inline(always)]
pub fn mm256_mul_epi32(lhs: Vec256, rhs: Vec256) -> Vec256 {
    unsafe { _mm256_mul_epi32(lhs.declassify(), rhs.declassify()).classify() }
}

#[inline(always)]
pub fn mm256_and_si256(lhs: Vec256, rhs: Vec256) -> Vec256 {
    unsafe { _mm256_and_si256(lhs.declassify(), rhs.declassify()).classify() }
}

#[inline(always)]
pub fn mm256_or_si256(a: Vec256, b: Vec256) -> Vec256 {
    unsafe { _mm256_or_si256(a.declassify(), b.declassify()).classify() }
}

#[inline(always)]
pub fn mm256_testz_si256(lhs: Vec256, rhs: Vec256) -> I32 {
    unsafe { _mm256_testz_si256(lhs.declassify(), rhs.declassify()).classify() }
}

#[inline(always)]
pub fn mm256_xor_si256(lhs: Vec256, rhs: Vec256) -> Vec256 {
    // This floating point xor may or may not be faster than regular xor.
    // Local testing seems to indicate that it's a little more stable in
    // benchmarks though.
    // See https://stackoverflow.com/questions/27804476/difference-between-mm256-xor-si256-and-mm256-xor-ps
    //
    // However, using this pushes the doc test in ml-kem over the limit for
    // stack size on Windows.
    // unsafe {
    //     _mm256_castps_si256(_mm256_xor_ps(
    //         _mm256_castsi256_ps(lhs),
    //         _mm256_castsi256_ps(rhs),
    //     ))
    // }
    unsafe { _mm256_xor_si256(lhs.declassify(), rhs.declassify()).classify() }
}

#[inline(always)]
pub fn mm256_srai_epi16<const SHIFT_BY: i32>(vector: Vec256) -> Vec256 {
    debug_assert!(SHIFT_BY >= 0 && SHIFT_BY < 16);
    unsafe { _mm256_srai_epi16(vector.declassify(), SHIFT_BY).classify() }
}
#[inline(always)]
pub fn mm256_srai_epi32<const SHIFT_BY: i32>(vector: Vec256) -> Vec256 {
    debug_assert!(SHIFT_BY >= 0 && SHIFT_BY < 32);
    unsafe { _mm256_srai_epi32(vector.declassify(), SHIFT_BY).classify() }
}

#[inline(always)]
pub fn mm256_srli_epi16<const SHIFT_BY: i32>(vector: Vec256) -> Vec256 {
    debug_assert!(SHIFT_BY >= 0 && SHIFT_BY < 16);
    unsafe { _mm256_srli_epi16(vector.declassify(), SHIFT_BY).classify() }
}
#[inline(always)]
pub fn mm256_srli_epi32<const SHIFT_BY: i32>(vector: Vec256) -> Vec256 {
    debug_assert!(SHIFT_BY >= 0 && SHIFT_BY < 32);
    unsafe { _mm256_srli_epi32(vector.declassify(), SHIFT_BY).classify() }
}

#[inline(always)]
pub fn mm_srli_epi64<const SHIFT_BY: i32>(vector: Vec128) -> Vec128 {
    debug_assert!(SHIFT_BY >= 0 && SHIFT_BY < 64);
    unsafe { _mm_srli_epi64(vector.declassify(), SHIFT_BY).classify() }
}
#[inline(always)]
pub fn mm256_srli_epi64<const SHIFT_BY: i32>(vector: Vec256) -> Vec256 {
    debug_assert!(SHIFT_BY >= 0 && SHIFT_BY < 64);
    unsafe { _mm256_srli_epi64(vector.declassify(), SHIFT_BY).classify() }
}

#[inline(always)]
pub fn mm256_slli_epi16<const SHIFT_BY: i32>(vector: Vec256) -> Vec256 {
    debug_assert!(SHIFT_BY >= 0 && SHIFT_BY < 16);
    unsafe { _mm256_slli_epi16(vector.declassify(), SHIFT_BY).classify() }
}

#[inline(always)]
pub fn mm256_slli_epi32<const SHIFT_BY: i32>(vector: Vec256) -> Vec256 {
    debug_assert!(SHIFT_BY >= 0 && SHIFT_BY < 32);
    unsafe { _mm256_slli_epi32(vector.declassify(), SHIFT_BY).classify() }
}

#[inline(always)]
pub fn mm_shuffle_epi8(vector: Vec128, control: Vec128) -> Vec128 {
    unsafe { _mm_shuffle_epi8(vector.declassify(), control.declassify()).classify() }
}
#[inline(always)]
pub fn mm256_shuffle_epi8(vector: Vec256, control: Vec256) -> Vec256 {
    unsafe { _mm256_shuffle_epi8(vector.declassify(), control.declassify()).classify() }
}
#[inline(always)]
pub fn mm256_shuffle_epi32<const CONTROL: i32>(vector: Vec256) -> Vec256 {
    debug_assert!(CONTROL >= 0 && CONTROL < 256);
    unsafe { _mm256_shuffle_epi32(vector.declassify(), CONTROL).classify() }
}

#[inline(always)]
pub fn mm256_permute4x64_epi64<const CONTROL: i32>(vector: Vec256) -> Vec256 {
    debug_assert!(CONTROL >= 0 && CONTROL < 256);
    unsafe { _mm256_permute4x64_epi64(vector.declassify(), CONTROL).classify() }
}

#[inline(always)]
pub fn mm256_unpackhi_epi64(lhs: Vec256, rhs: Vec256) -> Vec256 {
    unsafe { _mm256_unpackhi_epi64(lhs.declassify(), rhs.declassify()).classify() }
}

#[inline(always)]
pub fn mm256_unpacklo_epi32(lhs: Vec256, rhs: Vec256) -> Vec256 {
    unsafe { _mm256_unpacklo_epi32(lhs.declassify(), rhs.declassify()).classify() }
}

#[inline(always)]
pub fn mm256_unpackhi_epi32(lhs: Vec256, rhs: Vec256) -> Vec256 {
    unsafe { _mm256_unpackhi_epi32(lhs.declassify(), rhs.declassify()).classify() }
}

#[inline(always)]
pub fn mm256_castsi256_si128(vector: Vec256) -> Vec128 {
    unsafe { _mm256_castsi256_si128(vector.declassify()).classify() }
}
#[inline(always)]
pub fn mm256_castsi128_si256(vector: Vec128) -> Vec256 {
    unsafe { _mm256_castsi128_si256(vector.declassify()).classify() }
}

#[inline(always)]
pub fn mm256_cvtepi16_epi32(vector: Vec128) -> Vec256 {
    unsafe { _mm256_cvtepi16_epi32(vector.declassify()).classify() }
}

#[inline(always)]
pub fn mm_packs_epi16(lhs: Vec128, rhs: Vec128) -> Vec128 {
    unsafe { _mm_packs_epi16(lhs.declassify(), rhs.declassify()).classify() }
}
#[inline(always)]
pub fn mm256_packs_epi32(lhs: Vec256, rhs: Vec256) -> Vec256 {
    unsafe { _mm256_packs_epi32(lhs.declassify(), rhs.declassify()).classify() }
}

#[inline(always)]
pub fn mm256_extracti128_si256<const CONTROL: i32>(vector: Vec256) -> Vec128 {
    debug_assert!(CONTROL == 0 || CONTROL == 1);
    unsafe { _mm256_extracti128_si256(vector.declassify(), CONTROL).classify()}
}

#[inline(always)]
pub fn mm256_inserti128_si256<const CONTROL: i32>(vector: Vec256, vector_i128: Vec128) -> Vec256 {
    debug_assert!(CONTROL == 0 || CONTROL == 1);
    unsafe { _mm256_inserti128_si256(vector.declassify(), vector_i128.declassify(), CONTROL).classify() }
}

#[inline(always)]
pub fn mm256_blend_epi16<const CONTROL: i32>(lhs: Vec256, rhs: Vec256) -> Vec256 {
    debug_assert!(CONTROL >= 0 && CONTROL < 256);
    unsafe { _mm256_blend_epi16(lhs.declassify(), rhs.declassify(), CONTROL).classify() }
}

#[inline(always)]
pub fn mm256_blend_epi32<const CONTROL: i32>(lhs: Vec256, rhs: Vec256) -> Vec256 {
    debug_assert!(CONTROL >= 0 && CONTROL < 256);
    unsafe { _mm256_blend_epi32(lhs.declassify(), rhs.declassify(), CONTROL).classify() }
}

// This is essentially _mm256_blendv_ps adapted for use with the Vec256 type.
// It is not offered by the AVX2 instruction set.
#[inline(always)]
pub fn vec256_blendv_epi32(a: Vec256, b: Vec256, mask: Vec256) -> Vec256 {
    unsafe {
        _mm256_castps_si256(_mm256_blendv_ps(
            _mm256_castsi256_ps(a.declassify()),
            _mm256_castsi256_ps(b.declassify()),
            _mm256_castsi256_ps(mask.declassify()),
        )).classify()
    }
}

#[inline(always)]
pub fn mm_movemask_epi8(vector: Vec128) -> I32 {
    unsafe { _mm_movemask_epi8(vector.declassify()).classify() }
}

#[inline(always)]
pub fn mm256_permutevar8x32_epi32(vector: Vec256, control: Vec256) -> Vec256 {
    unsafe { _mm256_permutevar8x32_epi32(vector.declassify(), control.declassify()).classify() }
}

#[inline(always)]
pub fn mm256_srlv_epi32(vector: Vec256, counts: Vec256) -> Vec256 {
    unsafe { _mm256_srlv_epi32(vector.declassify(), counts.declassify()).classify() }
}
#[inline(always)]
pub fn mm256_srlv_epi64(vector: Vec256, counts: Vec256) -> Vec256 {
    unsafe { _mm256_srlv_epi64(vector.declassify(), counts.declassify()).classify() }
}

#[inline(always)]
pub fn mm_sllv_epi32(vector: Vec128, counts: Vec128) -> Vec128 {
    unsafe { _mm_sllv_epi32(vector.declassify(), counts.declassify()).classify() }
}
#[inline(always)]
pub fn mm256_sllv_epi32(vector: Vec256, counts: Vec256) -> Vec256 {
    unsafe { _mm256_sllv_epi32(vector.declassify(), counts.declassify()).classify() }
}

#[inline(always)]
pub fn mm256_slli_epi64<const LEFT: i32>(x: Vec256) -> Vec256 {
    unsafe { _mm256_slli_epi64::<LEFT>(x.declassify()).classify() }
}

#[inline(always)]
pub fn mm256_bsrli_epi128<const SHIFT_BY: i32>(x: Vec256) -> Vec256 {
    debug_assert!(SHIFT_BY > 0 && SHIFT_BY < 16);
    unsafe { _mm256_bsrli_epi128::<SHIFT_BY>(x.declassify()).classify() }
}

#[inline(always)]
pub fn mm256_andnot_si256(a: Vec256, b: Vec256) -> Vec256 {
    unsafe { _mm256_andnot_si256(a.declassify(), b.declassify()).classify() }
}

#[inline(always)]
pub fn mm256_set1_epi64x(a: I64) -> Vec256 {
    unsafe { _mm256_set1_epi64x(a.declassify()).classify() }
}
#[inline(always)]
pub fn mm256_set_epi64x(input3: I64, input2: I64, input1: I64, input0: I64) -> Vec256 {
    unsafe { _mm256_set_epi64x(input3.declassify(), input2.declassify(), input1.declassify(), input0.declassify()).classify() }
}

#[inline(always)]
pub fn mm256_unpacklo_epi64(lhs: Vec256, rhs: Vec256) -> Vec256 {
    unsafe { _mm256_unpacklo_epi64(lhs.declassify(), rhs.declassify()).classify() }
}

#[inline(always)]
pub fn mm256_permute2x128_si256<const IMM8: i32>(a: Vec256, b: Vec256) -> Vec256 {
    unsafe { _mm256_permute2x128_si256::<IMM8>(a.declassify(), b.declassify()).classify() }
}
