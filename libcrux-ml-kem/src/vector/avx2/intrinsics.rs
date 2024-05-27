// TODO: Move this into a separate intrinsics crate.

#![allow(unsafe_code)]

#[cfg(target_arch = "x86")]
pub(crate) use core::arch::x86::*;
#[cfg(target_arch = "x86_64")]
pub(crate) use core::arch::x86_64::*;

pub(crate) type Vec256 = __m256i;
pub(crate) type Vec128 = __m128i;

pub(crate) fn mm256_storeu_si256(output: &mut [i16], vector: __m256i) {
    debug_assert_eq!(output.len(), 16);
    unsafe {
        _mm256_storeu_si256(output.as_mut_ptr() as *mut __m256i, vector);
    }
}
pub(crate) fn mm_storeu_si128(output: &mut [i16], vector: __m128i) {
    // debug_assert_eq!(output.len(), 8);
    unsafe {
        _mm_storeu_si128(output.as_mut_ptr() as *mut __m128i, vector);
    }
}

pub(crate) fn mm_storeu_bytes_si128(output: &mut [u8], vector: __m128i) {
    debug_assert_eq!(output.len(), 16);
    unsafe {
        _mm_storeu_si128(output.as_mut_ptr() as *mut __m128i, vector);
    }
}

pub(crate) fn mm_loadu_si128(input: &[u8]) -> __m128i {
    debug_assert_eq!(input.len(), 16);
    unsafe { _mm_loadu_si128(input.as_ptr() as *const __m128i) }
}

pub(crate) fn mm256_loadu_si256(input: &[i16]) -> __m256i {
    debug_assert_eq!(input.len(), 16);
    unsafe { _mm256_loadu_si256(input.as_ptr() as *const __m256i) }
}

pub(crate) fn mm256_setzero_si256() -> __m256i {
    unsafe { _mm256_setzero_si256() }
}

pub(crate) fn mm_set_epi8(
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
) -> __m128i {
    unsafe {
        _mm_set_epi8(
            byte15 as i8,
            byte14 as i8,
            byte13 as i8,
            byte12 as i8,
            byte11 as i8,
            byte10 as i8,
            byte9 as i8,
            byte8 as i8,
            byte7 as i8,
            byte6 as i8,
            byte5 as i8,
            byte4 as i8,
            byte3 as i8,
            byte2 as i8,
            byte1 as i8,
            byte0 as i8,
        )
    }
}

pub(crate) fn mm256_set_epi8(
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
) -> __m256i {
    unsafe {
        _mm256_set_epi8(
            byte31, byte30, byte29, byte28, byte27, byte26, byte25, byte24, byte23, byte22, byte21,
            byte20, byte19, byte18, byte17, byte16, byte15, byte14, byte13, byte12, byte11, byte10,
            byte9, byte8, byte7, byte6, byte5, byte4, byte3, byte2, byte1, byte0,
        )
    }
}

pub(crate) fn mm256_set1_epi16(constant: i16) -> __m256i {
    unsafe { _mm256_set1_epi16(constant) }
}
pub(crate) fn mm256_set_epi16(
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
) -> __m256i {
    unsafe {
        _mm256_set_epi16(
            input15, input14, input13, input12, input11, input10, input9, input8, input7, input6,
            input5, input4, input3, input2, input1, input0,
        )
    }
}

pub(crate) fn mm_set1_epi16(constant: i16) -> __m128i {
    unsafe { _mm_set1_epi16(constant) }
}

pub(crate) fn mm256_set1_epi32(constant: i32) -> __m256i {
    unsafe { _mm256_set1_epi32(constant) }
}
pub(crate) fn mm256_set_epi32(
    input7: i32,
    input6: i32,
    input5: i32,
    input4: i32,
    input3: i32,
    input2: i32,
    input1: i32,
    input0: i32,
) -> __m256i {
    unsafe {
        _mm256_set_epi32(
            input7, input6, input5, input4, input3, input2, input1, input0,
        )
    }
}

pub(crate) fn mm_add_epi16(lhs: __m128i, rhs: __m128i) -> __m128i {
    unsafe { _mm_add_epi16(lhs, rhs) }
}
pub(crate) fn mm256_add_epi16(lhs: __m256i, rhs: __m256i) -> __m256i {
    unsafe { _mm256_add_epi16(lhs, rhs) }
}
pub(crate) fn mm256_madd_epi16(lhs: __m256i, rhs: __m256i) -> __m256i {
    unsafe { _mm256_madd_epi16(lhs, rhs) }
}
pub(crate) fn mm256_add_epi32(lhs: __m256i, rhs: __m256i) -> __m256i {
    unsafe { _mm256_add_epi32(lhs, rhs) }
}

pub(crate) fn mm256_sub_epi16(lhs: __m256i, rhs: __m256i) -> __m256i {
    unsafe { _mm256_sub_epi16(lhs, rhs) }
}
pub(crate) fn mm_sub_epi16(lhs: __m128i, rhs: __m128i) -> __m128i {
    unsafe { _mm_sub_epi16(lhs, rhs) }
}

pub(crate) fn mm256_mullo_epi16(lhs: __m256i, rhs: __m256i) -> __m256i {
    unsafe { _mm256_mullo_epi16(lhs, rhs) }
}

pub(crate) fn mm_mullo_epi16(lhs: __m128i, rhs: __m128i) -> __m128i {
    unsafe { _mm_mullo_epi16(lhs, rhs) }
}

pub(crate) fn mm256_cmpgt_epi16(lhs: __m256i, rhs: __m256i) -> __m256i {
    unsafe { _mm256_cmpgt_epi16(lhs, rhs) }
}

pub(crate) fn mm_mulhi_epi16(lhs: __m128i, rhs: __m128i) -> __m128i {
    unsafe { _mm_mulhi_epi16(lhs, rhs) }
}

pub(crate) fn mm256_mullo_epi32(lhs: __m256i, rhs: __m256i) -> __m256i {
    unsafe { _mm256_mullo_epi32(lhs, rhs) }
}

pub(crate) fn mm256_mulhi_epi16(lhs: __m256i, rhs: __m256i) -> __m256i {
    unsafe { _mm256_mulhi_epi16(lhs, rhs) }
}

pub(crate) fn mm256_mul_epu32(lhs: __m256i, rhs: __m256i) -> __m256i {
    unsafe { _mm256_mul_epu32(lhs, rhs) }
}

pub(crate) fn mm256_and_si256(lhs: __m256i, rhs: __m256i) -> __m256i {
    unsafe { _mm256_and_si256(lhs, rhs) }
}

pub(crate) fn mm256_xor_si256(lhs: __m256i, rhs: __m256i) -> __m256i {
    unsafe { _mm256_xor_si256(lhs, rhs) }
}

pub(crate) fn mm256_srai_epi16<const SHIFT_BY: i32>(vector: __m256i) -> __m256i {
    debug_assert!(SHIFT_BY >= 0 && SHIFT_BY < 16);
    unsafe { _mm256_srai_epi16(vector, SHIFT_BY) }
}
pub(crate) fn mm256_srai_epi32<const SHIFT_BY: i32>(vector: __m256i) -> __m256i {
    debug_assert!(SHIFT_BY >= 0 && SHIFT_BY < 32);
    unsafe { _mm256_srai_epi32(vector, SHIFT_BY) }
}

pub(crate) fn mm256_srli_epi16<const SHIFT_BY: i32>(vector: __m256i) -> __m256i {
    debug_assert!(SHIFT_BY >= 0 && SHIFT_BY < 16);
    unsafe { _mm256_srli_epi16(vector, SHIFT_BY) }
}
pub(crate) fn mm256_srli_epi32<const SHIFT_BY: i32>(vector: __m256i) -> __m256i {
    debug_assert!(SHIFT_BY >= 0 && SHIFT_BY < 32);
    unsafe { _mm256_srli_epi32(vector, SHIFT_BY) }
}

pub(crate) fn mm256_srli_epi64<const SHIFT_BY: i32>(vector: __m256i) -> __m256i {
    debug_assert!(SHIFT_BY >= 0 && SHIFT_BY < 64);
    unsafe { _mm256_srli_epi64(vector, SHIFT_BY) }
}

pub(crate) fn mm256_slli_epi16<const SHIFT_BY: i32>(vector: __m256i) -> __m256i {
    debug_assert!(SHIFT_BY >= 0 && SHIFT_BY < 16);
    unsafe { _mm256_slli_epi16(vector, SHIFT_BY) }
}

pub(crate) fn mm256_slli_epi32<const SHIFT_BY: i32>(vector: __m256i) -> __m256i {
    debug_assert!(SHIFT_BY >= 0 && SHIFT_BY < 32);
    unsafe { _mm256_slli_epi32(vector, SHIFT_BY) }
}

pub(crate) fn mm_shuffle_epi8(vector: __m128i, control: __m128i) -> __m128i {
    unsafe { _mm_shuffle_epi8(vector, control) }
}
pub(crate) fn mm256_shuffle_epi8(vector: __m256i, control: __m256i) -> __m256i {
    unsafe { _mm256_shuffle_epi8(vector, control) }
}
pub(crate) fn mm256_shuffle_epi32<const CONTROL: i32>(vector: __m256i) -> __m256i {
    debug_assert!(CONTROL >= 0 && CONTROL < 256);
    unsafe { _mm256_shuffle_epi32(vector, CONTROL) }
}

pub(crate) fn mm256_permute4x64_epi64<const CONTROL: i32>(vector: __m256i) -> __m256i {
    debug_assert!(CONTROL >= 0 && CONTROL < 256);
    unsafe { _mm256_permute4x64_epi64(vector, CONTROL) }
}

pub(crate) fn mm256_unpackhi_epi64(lhs: __m256i, rhs: __m256i) -> __m256i {
    unsafe { _mm256_unpackhi_epi64(lhs, rhs) }
}

pub(crate) fn mm256_unpacklo_epi32(lhs: __m256i, rhs: __m256i) -> __m256i {
    unsafe { _mm256_unpacklo_epi32(lhs, rhs) }
}

pub(crate) fn mm256_unpackhi_epi32(lhs: __m256i, rhs: __m256i) -> __m256i {
    unsafe { _mm256_unpackhi_epi32(lhs, rhs) }
}

pub(crate) fn mm256_castsi256_si128(vector: __m256i) -> __m128i {
    unsafe { _mm256_castsi256_si128(vector) }
}
pub(crate) fn mm256_castsi128_si256(vector: __m128i) -> __m256i {
    unsafe { _mm256_castsi128_si256(vector) }
}

pub(crate) fn mm256_cvtepi16_epi32(vector: __m128i) -> __m256i {
    unsafe { _mm256_cvtepi16_epi32(vector) }
}

pub(crate) fn mm_packs_epi16(lhs: __m128i, rhs: __m128i) -> __m128i {
    unsafe { _mm_packs_epi16(lhs, rhs) }
}
pub(crate) fn mm256_packs_epi32(lhs: __m256i, rhs: __m256i) -> __m256i {
    unsafe { _mm256_packs_epi32(lhs, rhs) }
}

pub(crate) fn mm256_extracti128_si256<const CONTROL: i32>(vector: __m256i) -> __m128i {
    debug_assert!(CONTROL == 0 || CONTROL == 1);
    unsafe { _mm256_extracti128_si256(vector, CONTROL) }
}

pub(crate) fn mm256_inserti128_si256<const CONTROL: i32>(
    vector: __m256i,
    vector_i128: __m128i,
) -> __m256i {
    debug_assert!(CONTROL == 0 || CONTROL == 1);
    unsafe { _mm256_inserti128_si256(vector, vector_i128, CONTROL) }
}

pub(crate) fn mm256_blend_epi16<const CONTROL: i32>(lhs: __m256i, rhs: __m256i) -> __m256i {
    debug_assert!(CONTROL >= 0 && CONTROL < 256);
    unsafe { _mm256_blend_epi16(lhs, rhs, CONTROL) }
}

pub(crate) fn mm_movemask_epi8(vector: __m128i) -> i32 {
    unsafe { _mm_movemask_epi8(vector) }
}

pub(crate) fn mm256_permutevar8x32_epi32(vector: __m256i, control: __m256i) -> __m256i {
    unsafe { _mm256_permutevar8x32_epi32(vector, control) }
}

pub(crate) fn mm256_sllv_epi32(vector: __m256i, counts: __m256i) -> __m256i {
    unsafe { _mm256_sllv_epi32(vector, counts) }
}
