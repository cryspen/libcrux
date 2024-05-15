#[cfg(target_arch = "x86")]
use core::arch::x86::*;
#[cfg(target_arch = "x86_64")]
use core::arch::x86_64::*;

use crate::SIMD256Vector;
use libcrux_traits::FIELD_MODULUS;

// This implementation was taken from:
// https://ei1333.github.io/library/math/combinatorics/vectorize-mod-int.hpp.html
//
// TODO: Optimize this implementation if performance numbers suggest doing so.
#[inline(always)]
fn mulhi_mm256_epi32(lhs: __m256i, rhs: __m256i) -> __m256i {
    let result = unsafe {
        let prod02 = _mm256_mul_epu32(lhs, rhs);
        let prod13 = _mm256_mul_epu32(
            _mm256_shuffle_epi32(lhs, 0b11_11_01_01),
            _mm256_shuffle_epi32(rhs, 0b11_11_01_01),
        );

        _mm256_unpackhi_epi64(
            _mm256_unpacklo_epi32(prod02, prod13),
            _mm256_unpackhi_epi32(prod02, prod13),
        )
    };

    result
}

#[inline(always)]
pub(crate) fn compress_message_coefficient(mut v: SIMD256Vector) -> SIMD256Vector {
    v.elements = unsafe {
        let field_modulus_halved = _mm256_set1_epi16((FIELD_MODULUS - 1) / 2);
        let field_modulus_quartered = _mm256_set1_epi16((FIELD_MODULUS - 1) / 4);

        let shifted = _mm256_sub_epi16(field_modulus_halved, v.elements);
        let mask = _mm256_srai_epi16(shifted, 15);

        let shifted_to_positive = _mm256_xor_si256(mask, shifted);
        let shifted_to_positive_in_range =
            _mm256_sub_epi16(shifted_to_positive, field_modulus_quartered);

        _mm256_srli_epi16(shifted_to_positive_in_range, 15)
    };

    v
}

#[inline(always)]
pub(crate) fn compress_ciphertext_coefficient<const COEFFICIENT_BITS: i32>(
    mut v: SIMD256Vector,
) -> SIMD256Vector {
    v.elements = unsafe {
        let field_modulus_halved = _mm256_set1_epi32(((FIELD_MODULUS as i32) - 1) / 2);
        let compression_factor = _mm256_set1_epi32(10_321_340);
        let coefficient_bits_mask = _mm256_set1_epi32((1 << COEFFICIENT_BITS) - 1);

        // Compress the first 8 coefficients
        let coefficients_low = _mm256_castsi256_si128(v.elements);
        let coefficients_low = _mm256_cvtepi16_epi32(coefficients_low);

        let compressed_low = _mm256_slli_epi32(coefficients_low, COEFFICIENT_BITS);
        let compressed_low = _mm256_add_epi32(compressed_low, field_modulus_halved);

        let compressed_low = mulhi_mm256_epi32(compressed_low, compression_factor);
        let compressed_low = _mm256_srli_epi32(compressed_low, 35 - 32);
        let compressed_low = _mm256_and_si256(compressed_low, coefficient_bits_mask);

        // Compress the next 8 coefficients
        let coefficients_high = _mm256_extracti128_si256(v.elements, 1);
        let coefficients_high = _mm256_cvtepi16_epi32(coefficients_high);

        let compressed_high = _mm256_slli_epi32(coefficients_high, COEFFICIENT_BITS);
        let compressed_high = _mm256_add_epi32(compressed_high, field_modulus_halved);

        let compressed_high = mulhi_mm256_epi32(compressed_high, compression_factor);
        let compressed_high = _mm256_srli_epi32(compressed_high, 35 - 32);
        let compressed_high = _mm256_and_si256(compressed_high, coefficient_bits_mask);

        // Combine them
        let compressed = _mm256_packs_epi32(compressed_low, compressed_high);

        _mm256_permute4x64_epi64(compressed, 0b11_01_10_00)
    };

    v
}

#[inline(always)]
pub(crate) fn decompress_ciphertext_coefficient<const COEFFICIENT_BITS: i32>(
    mut v: SIMD256Vector,
) -> SIMD256Vector {
    v.elements = unsafe {
        let field_modulus = _mm256_set1_epi32(FIELD_MODULUS as i32);
        let two_pow_coefficient_bits = _mm256_set1_epi32(1 << COEFFICIENT_BITS);

        // Compress the first 8 coefficients
        let coefficients_low = _mm256_castsi256_si128(v.elements);
        let coefficients_low = _mm256_cvtepi16_epi32(coefficients_low);

        let decompressed_low = _mm256_mullo_epi32(coefficients_low, field_modulus);
        let decompressed_low = _mm256_slli_epi32(decompressed_low, 1);
        let decompressed_low = _mm256_add_epi32(decompressed_low, two_pow_coefficient_bits);

        // We can't shift in one go by (COEFFICIENT_BITS + 1) due to the lack
        // of support for const generic expressions.
        let decompressed_low = _mm256_srli_epi32(decompressed_low, COEFFICIENT_BITS);
        let decompressed_low = _mm256_srli_epi32(decompressed_low, 1);

        // Compress the next 8 coefficients
        let coefficients_high = _mm256_extracti128_si256(v.elements, 1);
        let coefficients_high = _mm256_cvtepi16_epi32(coefficients_high);

        let decompressed_high = _mm256_mullo_epi32(coefficients_high, field_modulus);
        let decompressed_high = _mm256_slli_epi32(decompressed_high, 1);
        let decompressed_high = _mm256_add_epi32(decompressed_high, two_pow_coefficient_bits);

        // We can't shift in one go by (COEFFICIENT_BITS + 1) due to the lack
        // of support for const generic expressions.
        let decompressed_high = _mm256_srli_epi32(decompressed_high, COEFFICIENT_BITS);
        let decompressed_high = _mm256_srli_epi32(decompressed_high, 1);

        // Combine them
        let compressed = _mm256_packs_epi32(decompressed_low, decompressed_high);

        _mm256_permute4x64_epi64(compressed, 0b11_01_10_00)
    };

    v
}
