#[cfg(target_arch = "x86")]
pub(crate) use core::arch::x86::*;
#[cfg(target_arch = "x86_64")]
pub(crate) use core::arch::x86_64::*;

pub(crate) fn mm256_set1_epi16(constant: i16) -> __m256i {
    unsafe { _mm256_set1_epi16(constant) }
}
pub(crate) fn mm256_set1_epi32(constant: i32) -> __m256i {
    unsafe { _mm256_set1_epi32(constant) }
}

pub(crate) fn mm256_add_epi16(lhs: __m256i, rhs: __m256i) -> __m256i {
    unsafe { _mm256_add_epi16(lhs, rhs) }
}
pub(crate) fn mm256_add_epi32(lhs: __m256i, rhs: __m256i) -> __m256i {
    unsafe { _mm256_add_epi32(lhs, rhs) }
}

pub(crate) fn mm256_sub_epi16(lhs: __m256i, rhs: __m256i) -> __m256i {
    unsafe { _mm256_sub_epi16(lhs, rhs) }
}

pub(crate) fn mm256_mullo_epi16(lhs: __m256i, rhs: __m256i) -> __m256i {
    unsafe { _mm256_mullo_epi16(lhs, rhs) }
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
pub(crate) fn mm256_srli_epi16<const SHIFT_BY: i32>(vector: __m256i) -> __m256i {
    debug_assert!(SHIFT_BY >= 0 && SHIFT_BY < 16);
    unsafe { _mm256_srli_epi16(vector, SHIFT_BY) }
}
pub(crate) fn mm256_srli_epi32<const SHIFT_BY: i32>(vector: __m256i) -> __m256i {
    debug_assert!(SHIFT_BY >= 0 && SHIFT_BY < 32);
    unsafe { _mm256_srli_epi32(vector, SHIFT_BY) }
}

pub(crate) fn mm256_slli_epi16<const SHIFT_BY: i32>(vector: __m256i) -> __m256i {
    debug_assert!(SHIFT_BY >= 0 && SHIFT_BY < 16);
    unsafe { _mm256_slli_epi16(vector, SHIFT_BY) }
}

pub(crate) fn mm256_slli_epi32<const SHIFT_BY: i32>(vector: __m256i) -> __m256i {
    debug_assert!(SHIFT_BY >= 0 && SHIFT_BY < 32);
    unsafe { _mm256_slli_epi32(vector, SHIFT_BY) }
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

pub(crate) fn mm256_cvtepi16_epi32(vector: __m128i) -> __m256i {
    unsafe { _mm256_cvtepi16_epi32(vector) }
}

pub(crate) fn mm256_packs_epi32(lhs: __m256i, rhs: __m256i) -> __m256i {
    unsafe { _mm256_packs_epi32(lhs, rhs) }
}

pub(crate) fn mm256_extracti128_si256<const CONTROL: i32>(vector: __m256i) -> __m128i {
    debug_assert!(CONTROL == 0 || CONTROL == 1);
    unsafe { _mm256_extracti128_si256(vector, CONTROL) }
}
