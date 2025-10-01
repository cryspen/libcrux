#![cfg_attr(hax, allow(unused_unsafe))]

#[cfg(all(target_arch = "x86", not(hax)))]
pub use core::arch::x86::*;
#[cfg(all(target_arch = "x86_64", not(hax)))]
pub use core::arch::x86_64::*;

#[cfg(hax)]
pub use core_models::arch::x86::*;

/// 256-bit SIMD vector of integers
pub type Vec256 = __m256i;
/// 128-bit SIMD vector of integers
pub type Vec128 = __m128i;
/// 256-bit SIMD vector of floats
pub type Vec256Float = __m256;

/// Store a 256-bit integer vector to an unaligned u8 array
#[hax_lib::opaque]
#[inline(always)]
pub fn mm256_storeu_si256_u8(output: &mut [u8], vector: Vec256) {
    // Note: in this module the `debug_assert_eq!` are essentially sanity
    // checks. In the context of hax, those are counterproductive. Our models
    // are total: for example, `mm256_extracti128_si256` asserts CONTROL is
    // either zero or one, but the intel spec allows any value, so our model
    // does. Thus, we guard those debug asserts so that they don't appear in F*.
    #[cfg(not(hax))]
    debug_assert_eq!(output.len(), 32);
    unsafe {
        _mm256_storeu_si256(output.as_mut_ptr() as *mut Vec256, vector);
    }
}

/// Store a 256-bit integer vector to an unaligned i16 array
#[hax_lib::opaque]
#[inline(always)]
pub fn mm256_storeu_si256_i16(output: &mut [i16], vector: Vec256) {
    #[cfg(not(hax))]
    debug_assert_eq!(output.len(), 16);
    unsafe {
        _mm256_storeu_si256(output.as_mut_ptr() as *mut Vec256, vector);
    }
}

/// Store a 256-bit integer vector to an unaligned i32 array
#[hax_lib::opaque]
#[inline(always)]
pub fn mm256_storeu_si256_i32(output: &mut [i32], vector: Vec256) {
    #[cfg(not(hax))]
    debug_assert_eq!(output.len(), 8);
    unsafe {
        _mm256_storeu_si256(output.as_mut_ptr() as *mut Vec256, vector);
    }
}

/// Store a 128-bit integer vector to an unaligned i16 array
#[hax_lib::opaque]
#[inline(always)]
pub fn mm_storeu_si128(output: &mut [i16], vector: Vec128) {
    #[cfg(not(hax))]
    debug_assert!(output.len() >= 8);
    unsafe {
        _mm_storeu_si128(output.as_mut_ptr() as *mut Vec128, vector);
    }
}

/// Store a 128-bit integer vector to an unaligned i32 array
#[hax_lib::opaque]
#[inline(always)]
pub fn mm_storeu_si128_i32(output: &mut [i32], vector: Vec128) {
    #[cfg(not(hax))]
    debug_assert_eq!(output.len(), 4);
    unsafe {
        _mm_storeu_si128(output.as_mut_ptr() as *mut Vec128, vector);
    }
}

/// Store a 128-bit integer vector to an unaligned u8 array
#[hax_lib::opaque]
#[hax_lib::ensures(|_r| future(output).len() == output.len())]
#[inline(always)]
pub fn mm_storeu_bytes_si128(output: &mut [u8], vector: Vec128) {
    #[cfg(not(hax))]
    debug_assert_eq!(output.len(), 16);
    unsafe {
        _mm_storeu_si128(output.as_mut_ptr() as *mut Vec128, vector);
    }
}

/// Load a 128-bit integer vector from an unaligned u8 array
#[hax_lib::opaque]
#[inline(always)]
pub fn mm_loadu_si128(input: &[u8]) -> Vec128 {
    #[cfg(not(hax))]
    debug_assert_eq!(input.len(), 16);
    unsafe { _mm_loadu_si128(input.as_ptr() as *const Vec128) }
}

/// Load a 256-bit integer vector from an unaligned u8 array
#[hax_lib::opaque]
#[inline(always)]
pub fn mm256_loadu_si256_u8(input: &[u8]) -> Vec256 {
    #[cfg(not(hax))]
    debug_assert_eq!(input.len(), 32);
    unsafe { _mm256_loadu_si256(input.as_ptr() as *const Vec256) }
}

/// Load a 256-bit integer vector from an unaligned i16 array
#[hax_lib::opaque]
#[inline(always)]
pub fn mm256_loadu_si256_i16(input: &[i16]) -> Vec256 {
    #[cfg(not(hax))]
    debug_assert_eq!(input.len(), 16);
    unsafe { _mm256_loadu_si256(input.as_ptr() as *const Vec256) }
}

/// Load a 256-bit integer vector from an unaligned i32 array
#[hax_lib::opaque]
#[inline(always)]
pub fn mm256_loadu_si256_i32(input: &[i32]) -> Vec256 {
    #[cfg(not(hax))]
    debug_assert_eq!(input.len(), 8);
    unsafe { _mm256_loadu_si256(input.as_ptr() as *const Vec256) }
}

/// Create a 256-bit vector with all elements set to zero
#[inline(always)]
pub fn mm256_setzero_si256() -> Vec256 {
    unsafe { _mm256_setzero_si256() }
}

/// Create a 256-bit vector by combining two 128-bit vectors (high and low)
#[inline(always)]
pub fn mm256_set_m128i(hi: Vec128, lo: Vec128) -> Vec256 {
    unsafe { _mm256_set_m128i(hi, lo) }
}

/// Create a 128-bit vector from 16 individual i8 values
#[inline(always)]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
pub fn mm_set_epi8(
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
) -> Vec128 {
    unsafe {
        _mm_set_epi8(
            byte15, byte14, byte13, byte12, byte11, byte10, byte9, byte8, byte7, byte6, byte5,
            byte4, byte3, byte2, byte1, byte0,
        )
    }
}

/// Create a 256-bit vector from 32 individual i8 values
#[inline(always)]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
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
    unsafe {
        _mm256_set_epi8(
            byte31, byte30, byte29, byte28, byte27, byte26, byte25, byte24, byte23, byte22, byte21,
            byte20, byte19, byte18, byte17, byte16, byte15, byte14, byte13, byte12, byte11, byte10,
            byte9, byte8, byte7, byte6, byte5, byte4, byte3, byte2, byte1, byte0,
        )
    }
}

/// Create a 256-bit vector with all i16 elements set to the same value
#[inline(always)]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
pub fn mm256_set1_epi16(constant: i16) -> Vec256 {
    unsafe { _mm256_set1_epi16(constant) }
}

/// Create a 256-bit vector from 16 individual i16 values
#[inline(always)]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
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
    unsafe {
        _mm256_set_epi16(
            input15, input14, input13, input12, input11, input10, input9, input8, input7, input6,
            input5, input4, input3, input2, input1, input0,
        )
    }
}

/// Create a 128-bit vector with all i16 elements set to the same value
#[inline(always)]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
pub fn mm_set1_epi16(constant: i16) -> Vec128 {
    unsafe { _mm_set1_epi16(constant) }
}

/// Create a 256-bit vector with all i32 elements set to the same value
#[inline(always)]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
pub fn mm256_set1_epi32(constant: i32) -> Vec256 {
    unsafe { _mm256_set1_epi32(constant) }
}

/// Create a 128-bit vector from 4 individual i32 values
#[inline(always)]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
pub fn mm_set_epi32(input3: i32, input2: i32, input1: i32, input0: i32) -> Vec128 {
    unsafe { _mm_set_epi32(input3, input2, input1, input0) }
}

/// Create a 256-bit vector from 8 individual i32 values
#[inline(always)]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
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
    unsafe {
        _mm256_set_epi32(
            input7, input6, input5, input4, input3, input2, input1, input0,
        )
    }
}

/// Add packed 16-bit integers in two 128-bit vectors
#[inline(always)]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
pub fn mm_add_epi16(lhs: Vec128, rhs: Vec128) -> Vec128 {
    unsafe { _mm_add_epi16(lhs, rhs) }
}

/// Add packed 16-bit integers in two 256-bit vectors
#[inline(always)]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
pub fn mm256_add_epi16(lhs: Vec256, rhs: Vec256) -> Vec256 {
    unsafe { _mm256_add_epi16(lhs, rhs) }
}

/// Multiply packed 16-bit integers, add adjacent pairs and store as 32-bit integers
#[inline(always)]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
pub fn mm256_madd_epi16(lhs: Vec256, rhs: Vec256) -> Vec256 {
    unsafe { _mm256_madd_epi16(lhs, rhs) }
}

/// Add packed 32-bit integers in two 256-bit vectors
#[inline(always)]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
pub fn mm256_add_epi32(lhs: Vec256, rhs: Vec256) -> Vec256 {
    unsafe { _mm256_add_epi32(lhs, rhs) }
}

/// Add packed 64-bit integers in two 256-bit vectors
#[inline(always)]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
pub fn mm256_add_epi64(lhs: Vec256, rhs: Vec256) -> Vec256 {
    unsafe { _mm256_add_epi64(lhs, rhs) }
}

/// Compute absolute value of packed 32-bit integers
#[inline(always)]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
pub fn mm256_abs_epi32(a: Vec256) -> Vec256 {
    unsafe { _mm256_abs_epi32(a) }
}

/// Subtract packed 16-bit integers in two 256-bit vectors
#[inline(always)]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
pub fn mm256_sub_epi16(lhs: Vec256, rhs: Vec256) -> Vec256 {
    unsafe { _mm256_sub_epi16(lhs, rhs) }
}

/// Subtract packed 32-bit integers in two 256-bit vectors
#[inline(always)]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
pub fn mm256_sub_epi32(lhs: Vec256, rhs: Vec256) -> Vec256 {
    unsafe { _mm256_sub_epi32(lhs, rhs) }
}

/// Subtract packed 16-bit integers in two 128-bit vectors
#[inline(always)]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
pub fn mm_sub_epi16(lhs: Vec128, rhs: Vec128) -> Vec128 {
    unsafe { _mm_sub_epi16(lhs, rhs) }
}

/// Multiply packed 16-bit integers and store low 16 bits of results
#[inline(always)]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
pub fn mm256_mullo_epi16(lhs: Vec256, rhs: Vec256) -> Vec256 {
    unsafe { _mm256_mullo_epi16(lhs, rhs) }
}

/// Multiply packed 16-bit integers and store low 16 bits of results
#[inline(always)]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
pub fn mm_mullo_epi16(lhs: Vec128, rhs: Vec128) -> Vec128 {
    unsafe { _mm_mullo_epi16(lhs, rhs) }
}

/// Compare packed 16-bit integers for greater than
#[inline(always)]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
pub fn mm256_cmpgt_epi16(lhs: Vec256, rhs: Vec256) -> Vec256 {
    unsafe { _mm256_cmpgt_epi16(lhs, rhs) }
}

/// Compare packed 32-bit integers for greater than
#[inline(always)]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
pub fn mm256_cmpgt_epi32(lhs: Vec256, rhs: Vec256) -> Vec256 {
    unsafe { _mm256_cmpgt_epi32(lhs, rhs) }
}

/// Compare packed 32-bit integers for equality
#[inline(always)]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
pub fn mm256_cmpeq_epi32(a: Vec256, b: Vec256) -> Vec256 {
    unsafe { _mm256_cmpeq_epi32(a, b) }
}

/// Apply sign of packed 32-bit integers in b to packed 32-bit integers in a
#[inline(always)]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
pub fn mm256_sign_epi32(a: Vec256, b: Vec256) -> Vec256 {
    unsafe { _mm256_sign_epi32(a, b) }
}

/// Cast 256-bit integer vector to 256-bit float vector
#[inline(always)]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
pub fn mm256_castsi256_ps(a: Vec256) -> Vec256Float {
    unsafe { _mm256_castsi256_ps(a) }
}

/// Cast 256-bit float vector to 256-bit integer vector
#[inline(always)]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
pub fn mm256_castps_si256(a: Vec256Float) -> Vec256 {
    unsafe { _mm256_castps_si256(a) }
}

/// Extract sign bits from packed single-precision floating-point elements
#[inline(always)]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
pub fn mm256_movemask_ps(a: Vec256Float) -> i32 {
    unsafe { _mm256_movemask_ps(a) }
}

/// Multiply packed 16-bit integers and store high 16 bits of results
#[inline(always)]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
pub fn mm_mulhi_epi16(lhs: Vec128, rhs: Vec128) -> Vec128 {
    unsafe { _mm_mulhi_epi16(lhs, rhs) }
}

/// Multiply packed 32-bit integers and store low 32 bits of results
#[inline(always)]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
pub fn mm256_mullo_epi32(lhs: Vec256, rhs: Vec256) -> Vec256 {
    unsafe { _mm256_mullo_epi32(lhs, rhs) }
}

/// Multiply packed 16-bit integers and store high 16 bits of results
#[inline(always)]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
pub fn mm256_mulhi_epi16(lhs: Vec256, rhs: Vec256) -> Vec256 {
    unsafe { _mm256_mulhi_epi16(lhs, rhs) }
}

/// Multiply packed unsigned 32-bit integers and store low 64 bits of results
#[inline(always)]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
pub fn mm256_mul_epu32(lhs: Vec256, rhs: Vec256) -> Vec256 {
    unsafe { _mm256_mul_epu32(lhs, rhs) }
}

/// Multiply packed signed 32-bit integers and store low 64 bits of results
#[inline(always)]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
pub fn mm256_mul_epi32(lhs: Vec256, rhs: Vec256) -> Vec256 {
    unsafe { _mm256_mul_epi32(lhs, rhs) }
}

/// Perform bitwise AND on 256-bit vectors
#[inline(always)]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
pub fn mm256_and_si256(lhs: Vec256, rhs: Vec256) -> Vec256 {
    unsafe { _mm256_and_si256(lhs, rhs) }
}

/// Perform bitwise OR on 256-bit vectors
#[inline(always)]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
pub fn mm256_or_si256(a: Vec256, b: Vec256) -> Vec256 {
    unsafe { _mm256_or_si256(a, b) }
}

/// Test if AND of two 256-bit vectors is zero
#[inline(always)]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
pub fn mm256_testz_si256(lhs: Vec256, rhs: Vec256) -> i32 {
    unsafe { _mm256_testz_si256(lhs, rhs) }
}

/// Perform bitwise XOR on 256-bit vectors
#[inline(always)]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
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
    unsafe { _mm256_xor_si256(lhs, rhs) }
}

/// Shift packed 16-bit integers right by constant count with sign extension
#[inline(always)]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
pub fn mm256_srai_epi16<const SHIFT_BY: i32>(vector: Vec256) -> Vec256 {
    #[cfg(not(hax))]
    debug_assert!(SHIFT_BY >= 0 && SHIFT_BY < 16);
    unsafe { _mm256_srai_epi16::<SHIFT_BY>(vector) }
}

/// Shift packed 32-bit integers right by constant count with sign extension
#[inline(always)]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
pub fn mm256_srai_epi32<const SHIFT_BY: i32>(vector: Vec256) -> Vec256 {
    #[cfg(not(hax))]
    debug_assert!(SHIFT_BY >= 0 && SHIFT_BY < 32);
    unsafe { _mm256_srai_epi32::<SHIFT_BY>(vector) }
}

/// Shift packed 16-bit integers right by constant count with zero extension
#[inline(always)]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
pub fn mm256_srli_epi16<const SHIFT_BY: i32>(vector: Vec256) -> Vec256 {
    #[cfg(not(hax))]
    debug_assert!(SHIFT_BY >= 0 && SHIFT_BY < 16);
    unsafe { _mm256_srli_epi16::<SHIFT_BY>(vector) }
}

/// Shift packed 32-bit integers right by constant count with zero extension
#[inline(always)]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
pub fn mm256_srli_epi32<const SHIFT_BY: i32>(vector: Vec256) -> Vec256 {
    #[cfg(not(hax))]
    debug_assert!(SHIFT_BY >= 0 && SHIFT_BY < 32);
    unsafe { _mm256_srli_epi32::<SHIFT_BY>(vector) }
}

/// Shift packed 64-bit integers right by constant count with zero extension
#[inline(always)]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
pub fn mm_srli_epi64<const SHIFT_BY: i32>(vector: Vec128) -> Vec128 {
    #[cfg(not(hax))]
    debug_assert!(SHIFT_BY >= 0 && SHIFT_BY < 64);
    unsafe { _mm_srli_epi64::<SHIFT_BY>(vector) }
}

/// Shift packed 64-bit integers right by constant count with zero extension
#[inline(always)]
#[hax_lib::requires(SHIFT_BY > 0 && SHIFT_BY < 64)]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
pub fn mm256_srli_epi64<const SHIFT_BY: i32>(vector: Vec256) -> Vec256 {
    #[cfg(not(hax))]
    debug_assert!(SHIFT_BY >= 0 && SHIFT_BY < 64);
    unsafe { _mm256_srli_epi64::<SHIFT_BY>(vector) }
}

/// Shift packed 16-bit integers left by constant count
#[inline(always)]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
pub fn mm256_slli_epi16<const SHIFT_BY: i32>(vector: Vec256) -> Vec256 {
    #[cfg(not(hax))]
    debug_assert!(SHIFT_BY >= 0 && SHIFT_BY < 16);
    unsafe { _mm256_slli_epi16::<SHIFT_BY>(vector) }
}

/// Shift packed 32-bit integers left by constant count
#[inline(always)]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
pub fn mm256_slli_epi32<const SHIFT_BY: i32>(vector: Vec256) -> Vec256 {
    #[cfg(not(hax))]
    debug_assert!(SHIFT_BY >= 0 && SHIFT_BY < 32);
    unsafe { _mm256_slli_epi32::<SHIFT_BY>(vector) }
}

/// Shuffle bytes in 128-bit vector according to control mask
#[inline(always)]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
pub fn mm_shuffle_epi8(vector: Vec128, control: Vec128) -> Vec128 {
    unsafe { _mm_shuffle_epi8(vector, control) }
}

/// Shuffle bytes in 256-bit vector according to control mask
#[inline(always)]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
pub fn mm256_shuffle_epi8(vector: Vec256, control: Vec256) -> Vec256 {
    unsafe { _mm256_shuffle_epi8(vector, control) }
}

/// Shuffle 32-bit integers in 256-bit vector using constant control
#[inline(always)]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
pub fn mm256_shuffle_epi32<const CONTROL: i32>(vector: Vec256) -> Vec256 {
    #[cfg(not(hax))]
    debug_assert!(CONTROL >= 0 && CONTROL < 256);
    unsafe { _mm256_shuffle_epi32::<CONTROL>(vector) }
}

/// Permute 64-bit integers in 256-bit vector using constant control
#[inline(always)]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
pub fn mm256_permute4x64_epi64<const CONTROL: i32>(vector: Vec256) -> Vec256 {
    #[cfg(not(hax))]
    debug_assert!(CONTROL >= 0 && CONTROL < 256);
    unsafe { _mm256_permute4x64_epi64::<CONTROL>(vector) }
}

/// Unpack and interleave high 64-bit integers from two 256-bit vectors
#[inline(always)]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
pub fn mm256_unpackhi_epi64(lhs: Vec256, rhs: Vec256) -> Vec256 {
    unsafe { _mm256_unpackhi_epi64(lhs, rhs) }
}

/// Unpack and interleave low 32-bit integers from two 256-bit vectors
#[inline(always)]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
pub fn mm256_unpacklo_epi32(lhs: Vec256, rhs: Vec256) -> Vec256 {
    unsafe { _mm256_unpacklo_epi32(lhs, rhs) }
}

/// Unpack and interleave high 32-bit integers from two 256-bit vectors
#[inline(always)]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
pub fn mm256_unpackhi_epi32(lhs: Vec256, rhs: Vec256) -> Vec256 {
    unsafe { _mm256_unpackhi_epi32(lhs, rhs) }
}

/// Cast 256-bit integer vector to 128-bit integer vector (extract low 128 bits)
#[inline(always)]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
pub fn mm256_castsi256_si128(vector: Vec256) -> Vec128 {
    unsafe { _mm256_castsi256_si128(vector) }
}

/// Cast 128-bit integer vector to 256-bit integer vector (zero-extend high 128 bits)
#[inline(always)]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
pub fn mm256_castsi128_si256(vector: Vec128) -> Vec256 {
    unsafe { _mm256_castsi128_si256(vector) }
}

/// Convert packed 16-bit integers to 32-bit integers with sign extension
#[inline(always)]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
pub fn mm256_cvtepi16_epi32(vector: Vec128) -> Vec256 {
    unsafe { _mm256_cvtepi16_epi32(vector) }
}

/// Pack signed 16-bit integers to signed 8-bit integers with saturation
#[inline(always)]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
pub fn mm_packs_epi16(lhs: Vec128, rhs: Vec128) -> Vec128 {
    unsafe { _mm_packs_epi16(lhs, rhs) }
}

/// Pack signed 32-bit integers to signed 16-bit integers with saturation
#[inline(always)]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
pub fn mm256_packs_epi32(lhs: Vec256, rhs: Vec256) -> Vec256 {
    unsafe { _mm256_packs_epi32(lhs, rhs) }
}

/// Extract 128-bit lane from 256-bit vector
#[inline(always)]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
pub fn mm256_extracti128_si256<const CONTROL: i32>(vector: Vec256) -> Vec128 {
    #[cfg(not(hax))]
    debug_assert!(CONTROL == 0 || CONTROL == 1);
    unsafe { _mm256_extracti128_si256::<CONTROL>(vector) }
}

/// Insert 128-bit value into 256-bit vector at specified lane
#[inline(always)]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
pub fn mm256_inserti128_si256<const CONTROL: i32>(vector: Vec256, vector_i128: Vec128) -> Vec256 {
    #[cfg(not(hax))]
    debug_assert!(CONTROL == 0 || CONTROL == 1);
    unsafe { _mm256_inserti128_si256::<CONTROL>(vector, vector_i128) }
}

/// Blend 16-bit integers from two vectors using constant control mask
#[inline(always)]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
pub fn mm256_blend_epi16<const CONTROL: i32>(lhs: Vec256, rhs: Vec256) -> Vec256 {
    #[cfg(not(hax))]
    debug_assert!(CONTROL >= 0 && CONTROL < 256);
    unsafe { _mm256_blend_epi16::<CONTROL>(lhs, rhs) }
}

/// Blend 32-bit integers from two vectors using constant control mask
#[inline(always)]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
pub fn mm256_blend_epi32<const CONTROL: i32>(lhs: Vec256, rhs: Vec256) -> Vec256 {
    #[cfg(not(hax))]
    debug_assert!(CONTROL >= 0 && CONTROL < 256);
    unsafe { _mm256_blend_epi32::<CONTROL>(lhs, rhs) }
}

// This is essentially _mm256_blendv_ps adapted for use with the Vec256 type.
// It is not offered by the AVX2 instruction set.

/// Blend 32-bit integers from two vectors using variable mask
#[inline(always)]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
pub fn vec256_blendv_epi32(a: Vec256, b: Vec256, mask: Vec256) -> Vec256 {
    unsafe {
        _mm256_castps_si256(_mm256_blendv_ps(
            _mm256_castsi256_ps(a),
            _mm256_castsi256_ps(b),
            _mm256_castsi256_ps(mask),
        ))
    }
}

/// Extract most significant bit from each 8-bit integer and create mask
#[inline(always)]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
pub fn mm_movemask_epi8(vector: Vec128) -> i32 {
    unsafe { _mm_movemask_epi8(vector) }
}

/// Permute 32-bit integers in 256-bit vector using variable control
#[inline(always)]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
pub fn mm256_permutevar8x32_epi32(vector: Vec256, control: Vec256) -> Vec256 {
    unsafe { _mm256_permutevar8x32_epi32(vector, control) }
}

/// Shift packed 32-bit integers right by variable counts with zero extension
#[inline(always)]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
pub fn mm256_srlv_epi32(vector: Vec256, counts: Vec256) -> Vec256 {
    unsafe { _mm256_srlv_epi32(vector, counts) }
}

/// Shift packed 64-bit integers right by variable counts with zero extension
#[inline(always)]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
pub fn mm256_srlv_epi64(vector: Vec256, counts: Vec256) -> Vec256 {
    unsafe { _mm256_srlv_epi64(vector, counts) }
}

/// Shift packed 32-bit integers left by variable counts
#[inline(always)]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
pub fn mm_sllv_epi32(vector: Vec128, counts: Vec128) -> Vec128 {
    unsafe { _mm_sllv_epi32(vector, counts) }
}

/// Shift packed 32-bit integers left by variable counts
#[inline(always)]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
pub fn mm256_sllv_epi32(vector: Vec256, counts: Vec256) -> Vec256 {
    unsafe { _mm256_sllv_epi32(vector, counts) }
}

/// Shift packed 64-bit integers left by constant count
#[inline(always)]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
pub fn mm256_slli_epi64<const LEFT: i32>(x: Vec256) -> Vec256 {
    unsafe { _mm256_slli_epi64::<LEFT>(x) }
}

/// Shift 128-bit lanes right by constant byte count
#[inline(always)]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
pub fn mm256_bsrli_epi128<const SHIFT_BY: i32>(x: Vec256) -> Vec256 {
    #[cfg(not(hax))]
    debug_assert!(SHIFT_BY > 0 && SHIFT_BY < 16);
    unsafe { _mm256_bsrli_epi128::<SHIFT_BY>(x) }
}

/// Perform bitwise AND NOT operation on 256-bit vectors (NOT a AND b)
#[inline(always)]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
pub fn mm256_andnot_si256(a: Vec256, b: Vec256) -> Vec256 {
    unsafe { _mm256_andnot_si256(a, b) }
}

/// Create a 256-bit vector with all i64 elements set to the same value
#[inline(always)]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
pub fn mm256_set1_epi64x(a: i64) -> Vec256 {
    unsafe { _mm256_set1_epi64x(a) }
}

/// Create a 256-bit vector from 4 individual i64 values
#[inline(always)]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
pub fn mm256_set_epi64x(input3: i64, input2: i64, input1: i64, input0: i64) -> Vec256 {
    unsafe { _mm256_set_epi64x(input3, input2, input1, input0) }
}

/// Unpack and interleave low 64-bit integers from two 256-bit vectors
#[inline(always)]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
pub fn mm256_unpacklo_epi64(lhs: Vec256, rhs: Vec256) -> Vec256 {
    unsafe { _mm256_unpacklo_epi64(lhs, rhs) }
}

/// Permute 128-bit lanes within and between two 256-bit vectors
#[inline(always)]
#[hax_lib::fstar::before(r#"[@@ "opaque_to_smt"]"#)]
pub fn mm256_permute2x128_si256<const IMM8: i32>(a: Vec256, b: Vec256) -> Vec256 {
    unsafe { _mm256_permute2x128_si256::<IMM8>(a, b) }
}
