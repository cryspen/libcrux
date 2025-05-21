#![allow(unused_variables)]

//! A module providing a opaque interfaces to intrinsics.
//! Those functions are not intended to be used in F*: they are useful only for Rust typoechecking.

use super::*;

pub type Vec128 = __m128i;
pub type Vec256 = __m256i;
pub type Vec256Float = __m256;

#[hax_lib::opaque]
pub unsafe fn _mm256_setzero_si256() -> __m256i {
    unimplemented!()
}
#[hax_lib::opaque]
pub unsafe fn _mm256_set_m128i(hi: __m128i, lo: __m128i) -> __m256i {
    unimplemented!()
}
#[hax_lib::opaque]
pub unsafe fn _mm256_set1_epi16(a: i16) -> __m256i {
    unimplemented!()
}
#[hax_lib::opaque]
pub unsafe fn _mm_set1_epi16(a: i16) -> __m128i {
    unimplemented!()
}
#[hax_lib::opaque]
pub unsafe fn _mm_set_epi32(e3: i32, e2: i32, e1: i32, e0: i32) -> __m128i {
    unimplemented!()
}
#[hax_lib::opaque]
pub unsafe fn _mm_add_epi16(a: __m128i, b: __m128i) -> __m128i {
    unimplemented!()
}
#[hax_lib::opaque]
pub unsafe fn _mm256_add_epi16(a: __m256i, b: __m256i) -> __m256i {
    unimplemented!()
}
#[hax_lib::opaque]
pub unsafe fn _mm256_madd_epi16(a: __m256i, b: __m256i) -> __m256i {
    unimplemented!()
}
#[hax_lib::opaque]
pub unsafe fn _mm256_add_epi32(a: __m256i, b: __m256i) -> __m256i {
    unimplemented!()
}
#[hax_lib::opaque]
pub unsafe fn _mm256_add_epi64(a: __m256i, b: __m256i) -> __m256i {
    unimplemented!()
}
#[hax_lib::opaque]
pub unsafe fn _mm256_abs_epi32(a: __m256i) -> __m256i {
    unimplemented!()
}
#[hax_lib::opaque]
pub unsafe fn _mm256_sub_epi16(a: __m256i, b: __m256i) -> __m256i {
    unimplemented!()
}
#[hax_lib::opaque]
pub unsafe fn _mm_sub_epi16(a: __m128i, b: __m128i) -> __m128i {
    unimplemented!()
}
#[hax_lib::opaque]
pub unsafe fn _mm_mullo_epi16(a: __m128i, b: __m128i) -> __m128i {
    unimplemented!()
}
#[hax_lib::opaque]
pub unsafe fn _mm256_cmpgt_epi16(a: __m256i, b: __m256i) -> __m256i {
    unimplemented!()
}
#[hax_lib::opaque]
pub unsafe fn _mm256_cmpgt_epi32(a: __m256i, b: __m256i) -> __m256i {
    unimplemented!()
}
#[hax_lib::opaque]
pub unsafe fn _mm256_cmpeq_epi32(a: __m256i, b: __m256i) -> __m256i {
    unimplemented!()
}
#[hax_lib::opaque]
pub unsafe fn _mm256_sign_epi32(a: __m256i, b: __m256i) -> __m256i {
    unimplemented!()
}
#[hax_lib::opaque]
pub unsafe fn _mm256_castsi256_ps(a: __m256i) -> __m256 {
    unimplemented!()
}
#[hax_lib::opaque]
pub unsafe fn _mm256_castps_si256(a: __m256) -> __m256i {
    unimplemented!()
}
#[hax_lib::opaque]
pub unsafe fn _mm256_movemask_ps(a: __m256) -> i32 {
    unimplemented!()
}
#[hax_lib::opaque]
pub unsafe fn _mm_mulhi_epi16(a: __m128i, b: __m128i) -> __m128i {
    unimplemented!()
}
#[hax_lib::opaque]
pub unsafe fn _mm256_mullo_epi32(a: __m256i, b: __m256i) -> __m256i {
    unimplemented!()
}
#[hax_lib::opaque]
pub unsafe fn _mm256_mulhi_epi16(a: __m256i, b: __m256i) -> __m256i {
    unimplemented!()
}
#[hax_lib::opaque]
pub unsafe fn _mm256_mul_epu32(a: __m256i, b: __m256i) -> __m256i {
    unimplemented!()
}
#[hax_lib::opaque]
pub unsafe fn _mm256_and_si256(a: __m256i, b: __m256i) -> __m256i {
    unimplemented!()
}
#[hax_lib::opaque]
pub unsafe fn _mm256_or_si256(a: __m256i, b: __m256i) -> __m256i {
    unimplemented!()
}
#[hax_lib::opaque]
pub unsafe fn _mm256_testz_si256(a: __m256i, b: __m256i) -> i32 {
    unimplemented!()
}
#[hax_lib::opaque]
pub unsafe fn _mm256_xor_si256(a: __m256i, b: __m256i) -> __m256i {
    unimplemented!()
}
#[hax_lib::opaque]
pub unsafe fn _mm256_srai_epi16<const IMM8: i32>(a: __m256i) -> __m256i {
    unimplemented!()
}
#[hax_lib::opaque]
pub unsafe fn _mm256_srai_epi32<const IMM8: i32>(a: __m256i) -> __m256i {
    unimplemented!()
}
#[hax_lib::opaque]
pub unsafe fn _mm256_srli_epi16<const IMM8: i32>(a: __m256i) -> __m256i {
    unimplemented!()
}
#[hax_lib::opaque]
pub unsafe fn _mm256_srli_epi32<const IMM8: i32>(a: __m256i) -> __m256i {
    unimplemented!()
}
#[hax_lib::opaque]
pub unsafe fn _mm_srli_epi64<const IMM8: i32>(a: __m128i) -> __m128i {
    unimplemented!()
}
#[hax_lib::opaque]
pub unsafe fn _mm256_slli_epi32<const IMM8: i32>(a: __m256i) -> __m256i {
    unimplemented!()
}
#[hax_lib::opaque]
pub unsafe fn _mm256_permute4x64_epi64<const IMM8: i32>(a: __m256i) -> __m256i {
    unimplemented!()
}
#[hax_lib::opaque]
pub unsafe fn _mm256_unpackhi_epi64(a: __m256i, b: __m256i) -> __m256i {
    unimplemented!()
}
#[hax_lib::opaque]
pub unsafe fn _mm256_unpacklo_epi32(a: __m256i, b: __m256i) -> __m256i {
    unimplemented!()
}
#[hax_lib::opaque]
pub unsafe fn _mm256_unpackhi_epi32(a: __m256i, b: __m256i) -> __m256i {
    unimplemented!()
}
#[hax_lib::opaque]
pub unsafe fn _mm256_castsi128_si256(a: __m128i) -> __m256i {
    unimplemented!()
}
#[hax_lib::opaque]
pub unsafe fn _mm256_cvtepi16_epi32(a: __m128i) -> __m256i {
    unimplemented!()
}
#[hax_lib::opaque]
pub unsafe fn _mm_packs_epi16(a: __m128i, b: __m128i) -> __m128i {
    unimplemented!()
}
#[hax_lib::opaque]
pub unsafe fn _mm256_packs_epi32(a: __m256i, b: __m256i) -> __m256i {
    unimplemented!()
}
#[hax_lib::opaque]
pub unsafe fn _mm256_inserti128_si256<const IMM8: i32>(a: __m256i, b: __m128i) -> __m256i {
    unimplemented!()
}
#[hax_lib::opaque]
pub unsafe fn _mm256_blend_epi16<const IMM8: i32>(a: __m256i, b: __m256i) -> __m256i {
    unimplemented!()
}
#[hax_lib::opaque]
pub unsafe fn _mm256_blendv_ps(a: __m256, b: __m256, mask: __m256) -> __m256 {
    unimplemented!()
}
#[hax_lib::opaque]
pub unsafe fn _mm_movemask_epi8(a: __m128i) -> i32 {
    unimplemented!()
}
#[hax_lib::opaque]
pub unsafe fn _mm256_srlv_epi64(a: __m256i, b: __m256i) -> __m256i {
    unimplemented!()
}
#[hax_lib::opaque]
pub unsafe fn _mm_sllv_epi32(a: __m128i, b: __m128i) -> __m128i {
    unimplemented!()
}
#[hax_lib::opaque]
pub unsafe fn _mm256_slli_epi64<const IMM8: i32>(a: __m256i) -> __m256i {
    unimplemented!()
}
#[hax_lib::opaque]
pub unsafe fn _mm256_bsrli_epi128<const IMM8: i32>(a: __m256i) -> __m256i {
    unimplemented!()
}
#[hax_lib::opaque]
pub unsafe fn _mm256_andnot_si256(a: __m256i, b: __m256i) -> __m256i {
    unimplemented!()
}
#[hax_lib::opaque]
pub unsafe fn _mm256_set1_epi64x(a: i64) -> __m256i {
    unimplemented!()
}
#[hax_lib::opaque]
pub unsafe fn _mm256_set_epi64x(e3: i64, e2: i64, e1: i64, e0: i64) -> __m256i {
    unimplemented!()
}
#[hax_lib::opaque]
pub unsafe fn _mm256_unpacklo_epi64(a: __m256i, b: __m256i) -> __m256i {
    unimplemented!()
}
#[hax_lib::opaque]
pub unsafe fn _mm256_permute2x128_si256<const IMM8: i32>(a: __m256i, b: __m256i) -> __m256i {
    unimplemented!()
}

#[hax_lib::exclude]
pub unsafe fn _mm256_storeu_si256(mem_addr: *mut __m256i, a: __m256i) {
    unimplemented!()
}
#[hax_lib::exclude]
pub unsafe fn _mm_loadu_si128(mem_addr: *const __m128i) -> __m128i {
    unimplemented!()
}
#[hax_lib::exclude]
pub unsafe fn _mm256_loadu_si256(mem_addr: *const __m256i) -> __m256i {
    unimplemented!()
}
