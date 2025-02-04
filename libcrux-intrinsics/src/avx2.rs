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
pub fn mm_set_epi8<T:Into<U8>>(
    byte15: T,
    byte14: T,
    byte13: T,
    byte12: T,
    byte11: T,
    byte10: T,
    byte9: T,
    byte8: T,
    byte7: T,
    byte6: T,
    byte5: T,
    byte4: T,
    byte3: T,
    byte2: T,
    byte1: T,
    byte0: T,
) -> Vec128 {
    unsafe {
        _mm_set_epi8(
            byte15.into().declassify() as i8,
            byte14.into().declassify() as i8,
            byte13.into().declassify() as i8,
            byte12.into().declassify() as i8,
            byte11.into().declassify() as i8,
            byte10.into().declassify() as i8,
            byte9.into().declassify() as i8,
            byte8.into().declassify() as i8,
            byte7.into().declassify() as i8,
            byte6.into().declassify() as i8,
            byte5.into().declassify() as i8,
            byte4.into().declassify() as i8,
            byte3.into().declassify() as i8,
            byte2.into().declassify() as i8,
            byte1.into().declassify() as i8,
            byte0.into().declassify() as i8,
        ).classify()
    }
}

#[inline(always)]
pub fn mm256_set_epi8<T:Into<I8>>(
    byte31: T,
    byte30: T,
    byte29: T,
    byte28: T,
    byte27: T,
    byte26: T,
    byte25: T,
    byte24: T,
    byte23: T,
    byte22: T,
    byte21: T,
    byte20: T,
    byte19: T,
    byte18: T,
    byte17: T,
    byte16: T,
    byte15: T,
    byte14: T,
    byte13: T,
    byte12: T,
    byte11: T,
    byte10: T,
    byte9: T,
    byte8: T,
    byte7: T,
    byte6: T,
    byte5: T,
    byte4: T,
    byte3: T,
    byte2: T,
    byte1: T,
    byte0: T,
) -> Vec256 {
    unsafe {
        _mm256_set_epi8(
            byte31.into().declassify(), byte30.into().declassify(), byte29.into().declassify(), byte28.into().declassify(), 
            byte27.into().declassify(), byte26.into().declassify(), byte25.into().declassify(), byte24.into().declassify(), 
            byte23.into().declassify(), byte22.into().declassify(), byte21.into().declassify(), byte20.into().declassify(), 
            byte19.into().declassify(), byte18.into().declassify(), byte17.into().declassify(), byte16.into().declassify(), 
            byte15.into().declassify(), byte14.into().declassify(), byte13.into().declassify(), byte12.into().declassify(), 
            byte11.into().declassify(), byte10.into().declassify(), byte9.into().declassify(), byte8.into().declassify(), 
            byte7.into().declassify(), byte6.into().declassify(), byte5.into().declassify(), byte4.into().declassify(), 
            byte3.into().declassify(), byte2.into().declassify(), byte1.into().declassify(), byte0.into().declassify(),
        ).classify()
    }
}

#[inline(always)]
pub fn mm256_set1_epi16<T:Into<I16>>(constant: T) -> Vec256 {
    unsafe { _mm256_set1_epi16(constant.into().declassify()).classify() }
}
#[inline(always)]
pub fn mm256_set_epi16<T:Into<I16>>(
    input15: T,
    input14: T,
    input13: T,
    input12: T,
    input11: T,
    input10: T,
    input9: T,
    input8: T,
    input7: T,
    input6: T,
    input5: T,
    input4: T,
    input3: T,
    input2: T,
    input1: T,
    input0: T,
) -> Vec256 {
    unsafe {
        _mm256_set_epi16(
            input15.into().declassify(), input14.into().declassify(), input13.into().declassify(), input12.into().declassify(), 
            input11.into().declassify(), input10.into().declassify(), input9.into().declassify(), input8.into().declassify(), 
            input7.into().declassify(), input6.into().declassify(), input5.into().declassify(), input4.into().declassify(), 
            input3.into().declassify(), input2.into().declassify(), input1.into().declassify(), input0.into().declassify(),
        ).classify()
    }
}

#[inline(always)]
pub fn mm_set1_epi16<T:Into<I16>>(constant: T) -> Vec128 {
    unsafe { _mm_set1_epi16(constant.into().declassify()).classify() }
}

#[inline(always)]
pub fn mm256_set1_epi32<T:Into<I32>>(constant: T) -> Vec256 {
    unsafe { _mm256_set1_epi32(constant.into().declassify()).classify() }
}

#[inline(always)]
pub fn mm_set_epi32<T:Into<I32>>(input3: T, input2: T, input1: T, input0: T) -> Vec128 {
    unsafe { _mm_set_epi32(input3.into().declassify(), input2.into().declassify(), input1.into().declassify(), input0.into().declassify()).classify() }
}
#[inline(always)]
pub fn mm256_set_epi32<T:Into<I32>>(
    input7: T,
    input6: T,
    input5: T,
    input4: T,
    input3: T,
    input2: T,
    input1: T,
    input0: T,
) -> Vec256 {
    unsafe {
        _mm256_set_epi32(
            input7.into().declassify(), input6.into().declassify(), input5.into().declassify(), input4.into().declassify(), 
            input3.into().declassify(), input2.into().declassify(), input1.into().declassify(), input0.into().declassify(),
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
pub fn mm256_set1_epi64x<T:Into<I64>>(a: T) -> Vec256 {
    unsafe { _mm256_set1_epi64x(a.into().declassify()).classify() }
}
#[inline(always)]
pub fn mm256_set_epi64x<T:Into<I64>>(input3: T, input2: T, input1: T, input0: T) -> Vec256 {
    unsafe { _mm256_set_epi64x(input3.into().declassify(), input2.into().declassify(), 
                              input1.into().declassify(), input0.into().declassify()).classify() }
}

#[inline(always)]
pub fn mm256_unpacklo_epi64(lhs: Vec256, rhs: Vec256) -> Vec256 {
    unsafe { _mm256_unpacklo_epi64(lhs.declassify(), rhs.declassify()).classify() }
}

#[inline(always)]
pub fn mm256_permute2x128_si256<const IMM8: i32>(a: Vec256, b: Vec256) -> Vec256 {
    unsafe { _mm256_permute2x128_si256::<IMM8>(a.declassify(), b.declassify()).classify() }
}
