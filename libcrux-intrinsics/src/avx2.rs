pub use core::arch::x86_64::*;

#[inline(always)]
pub fn mm256_xor_si256(a: __m256i, b: __m256i) -> __m256i {
    unsafe { _mm256_xor_si256(a, b) }
}

#[inline(always)]
pub fn mm256_slli_epi64<const LEFT: i32>(x: __m256i) -> __m256i {
    unsafe { _mm256_slli_epi64::<LEFT>(x) }
}

#[inline(always)]
pub fn mm256_srli_epi64<const RIGHT: i32>(x: __m256i) -> __m256i {
    unsafe { _mm256_srli_epi64::<RIGHT>(x) }
}

#[inline(always)]
pub fn mm256_andnot_si256(a: __m256i, b: __m256i) -> __m256i {
    unsafe { _mm256_andnot_si256(a, b) }
}
#[inline(always)]
pub fn mm256_set1_epi64x(a: i64) -> __m256i {
    unsafe { _mm256_set1_epi64x(a) }
}
#[inline(always)]
pub fn mm256_loadu_si256(mem_addr: *const __m256i) -> __m256i {
    unsafe { _mm256_loadu_si256(mem_addr) }
}
#[inline(always)]
pub fn mm256_unpacklo_epi64(a: __m256i, b: __m256i) -> __m256i {
    unsafe { _mm256_unpacklo_epi64(a, b) }
}
#[inline(always)]
pub fn mm256_unpackhi_epi64(a: __m256i, b: __m256i) -> __m256i {
    unsafe { _mm256_unpackhi_epi64(a, b) }
}
#[inline(always)]
pub fn mm256_permute2x128_si256<const IMM8: i32>(a: __m256i, b: __m256i) -> __m256i {
    unsafe { _mm256_permute2x128_si256::<IMM8>(a, b) }
}
#[inline(always)]
pub fn mm256_storeu_si256(mem_addr: *mut __m256i, a: __m256i) {
    unsafe { _mm256_storeu_si256(mem_addr, a) }
}
