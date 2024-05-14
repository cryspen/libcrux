#[cfg(target_arch = "x86")]
use core::arch::x86::*;
#[cfg(target_arch = "x86_64")]
use core::arch::x86_64::*;
use libcrux_traits::{Operations, FIELD_MODULUS, INVERSE_OF_MODULUS_MOD_MONTGOMERY_R};

mod debug;
mod portable;

const BARRETT_MULTIPLIER: i16 = 20159;

#[derive(Clone, Copy)]
pub struct SIMD256Vector {
    elements: __m256i,
}

#[inline(always)]
fn zero() -> SIMD256Vector {
    SIMD256Vector {
        elements: unsafe { _mm256_setzero_si256() },
    }
}

#[inline(always)]
fn to_i16_array(v: SIMD256Vector) -> [i16; 16] {
    let mut out = [0i16; 16];

    unsafe {
        _mm256_storeu_si256(out.as_mut_ptr() as *mut __m256i, v.elements);
    }

    out
}
#[inline(always)]
fn from_i16_array(array: &[i16]) -> SIMD256Vector {
    SIMD256Vector {
        elements: unsafe { _mm256_loadu_si256(array.as_ptr() as *const __m256i) },
    }
}

#[inline(always)]
fn add(mut lhs: SIMD256Vector, rhs: &SIMD256Vector) -> SIMD256Vector {
    lhs.elements = unsafe { _mm256_add_epi16(lhs.elements, rhs.elements) };

    lhs
}

#[inline(always)]
fn sub(mut lhs: SIMD256Vector, rhs: &SIMD256Vector) -> SIMD256Vector {
    lhs.elements = unsafe { _mm256_sub_epi16(lhs.elements, rhs.elements) };

    lhs
}

#[inline(always)]
fn multiply_by_constant(mut v: SIMD256Vector, c: i16) -> SIMD256Vector {
    v.elements = unsafe {
        let c = _mm256_set1_epi16(c);

        _mm256_mullo_epi16(v.elements, c)
    };

    v
}

#[inline(always)]
fn bitwise_and_with_constant(mut v: SIMD256Vector, c: i16) -> SIMD256Vector {
    v.elements = unsafe {
        let c = _mm256_set1_epi16(c);

        _mm256_and_si256(v.elements, c)
    };

    v
}

#[inline(always)]
fn shift_right<const SHIFT_BY: i32>(mut v: SIMD256Vector) -> SIMD256Vector {
    v.elements = unsafe { _mm256_srai_epi16(v.elements, SHIFT_BY) };

    v
}

#[inline(always)]
fn shift_left<const SHIFT_BY: i32>(mut v: SIMD256Vector) -> SIMD256Vector {
    v.elements = unsafe { _mm256_slli_epi16(v.elements, SHIFT_BY) };

    v
}

#[inline(always)]
fn cond_subtract_3329(mut v: SIMD256Vector) -> SIMD256Vector {
    v.elements = unsafe {
        let field_modulus = _mm256_set1_epi16(FIELD_MODULUS);

        let v_minus_field_modulus = _mm256_sub_epi16(v.elements, field_modulus);

        let sign_mask = _mm256_srai_epi16(v_minus_field_modulus, 15);
        let conditional_add_field_modulus = _mm256_and_si256(sign_mask, field_modulus);

        _mm256_add_epi16(v_minus_field_modulus, conditional_add_field_modulus)
    };

    v
}

#[inline(always)]
fn barrett_reduce(mut v: SIMD256Vector) -> SIMD256Vector {
    v.elements = unsafe {
        let t = _mm256_mulhi_epi16(v.elements, _mm256_set1_epi16(BARRETT_MULTIPLIER));
        let t = _mm256_add_epi16(t, _mm256_set1_epi16(512));

        let quotient = _mm256_srai_epi16(t, 10);

        let quotient_times_field_modulus =
            _mm256_mullo_epi16(quotient, _mm256_set1_epi16(FIELD_MODULUS));

        _mm256_sub_epi16(v.elements, quotient_times_field_modulus)
    };

    v
}

#[inline(always)]
fn montgomery_multiply_by_constant(mut v: SIMD256Vector, c: i16) -> SIMD256Vector {
    v.elements = unsafe {
        let c = _mm256_set1_epi16(c);
        let value_low = _mm256_mullo_epi16(v.elements, c);

        let k = _mm256_mullo_epi16(
            value_low,
            _mm256_set1_epi16(INVERSE_OF_MODULUS_MOD_MONTGOMERY_R as i16),
        );
        let k_times_modulus = _mm256_mulhi_epi16(k, _mm256_set1_epi16(FIELD_MODULUS));

        let value_high = _mm256_mulhi_epi16(v.elements, c);

        _mm256_sub_epi16(value_high, k_times_modulus)
    };

    v
}

#[inline(always)]
fn montgomery_multiply_by_constants(mut v: __m256i, c: __m256i) -> __m256i {
    v = unsafe {
        let value_low = _mm256_mullo_epi16(v, c);

        let k = _mm256_mullo_epi16(
            value_low,
            _mm256_set1_epi16(INVERSE_OF_MODULUS_MOD_MONTGOMERY_R as i16),
        );
        let k_times_modulus = _mm256_mulhi_epi16(k, _mm256_set1_epi16(FIELD_MODULUS));

        let value_high = _mm256_mulhi_epi16(v, c);

        _mm256_sub_epi16(value_high, k_times_modulus)
    };

    v
}

#[inline(always)]
fn montgomery_reduce_i32s(mut v: __m256i) -> __m256i {
    v = unsafe {
        let k = _mm256_mullo_epi16(
            v,
            _mm256_set1_epi32(INVERSE_OF_MODULUS_MOD_MONTGOMERY_R as i32),
        );
        let k_times_modulus = _mm256_mulhi_epi16(k, _mm256_set1_epi32(FIELD_MODULUS as i32));

        let value_high = _mm256_srli_epi32(v, 16);

        let result = _mm256_sub_epi16(value_high, k_times_modulus);

        let result = _mm256_slli_epi32(result, 16);
        _mm256_srai_epi32(result, 16)
    };

    v
}

#[inline(always)]
fn montgomery_multiply_m128i_by_constants(mut v: __m128i, c: __m128i) -> __m128i {
    v = unsafe {
        let value_low = _mm_mullo_epi16(v, c);

        let k = _mm_mullo_epi16(
            value_low,
            _mm_set1_epi16(INVERSE_OF_MODULUS_MOD_MONTGOMERY_R as i16),
        );
        let k_times_modulus = _mm_mulhi_epi16(k, _mm_set1_epi16(FIELD_MODULUS));

        let value_high = _mm_mulhi_epi16(v, c);

        _mm_sub_epi16(value_high, k_times_modulus)
    };

    v
}

#[inline(always)]
fn compress_1(mut v: SIMD256Vector) -> SIMD256Vector {
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
fn compress<const COEFFICIENT_BITS: i32>(mut v: SIMD256Vector) -> SIMD256Vector {
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
fn decompress_ciphertext_coefficient<const COEFFICIENT_BITS: i32>(
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

#[inline(always)]
fn ntt_layer_1_step(
    mut v: SIMD256Vector,
    zeta0: i16,
    zeta1: i16,
    zeta2: i16,
    zeta3: i16,
) -> SIMD256Vector {
    v.elements = unsafe {
        let zetas = _mm256_set_epi16(
            -zeta3, -zeta3, zeta3, zeta3, -zeta2, -zeta2, zeta2, zeta2, -zeta1, -zeta1, zeta1,
            zeta1, -zeta0, -zeta0, zeta0, zeta0,
        );

        let rhs = _mm256_shuffle_epi32(v.elements, 0b11_11_01_01);
        let rhs = montgomery_multiply_by_constants(rhs, zetas);

        let lhs = _mm256_shuffle_epi32(v.elements, 0b10_10_00_00);

        _mm256_add_epi16(lhs, rhs)
    };

    v
}

#[inline(always)]
fn ntt_layer_2_step(mut v: SIMD256Vector, zeta0: i16, zeta1: i16) -> SIMD256Vector {
    v.elements = unsafe {
        let zetas = _mm256_set_epi16(
            -zeta1, -zeta1, -zeta1, -zeta1, zeta1, zeta1, zeta1, zeta1, -zeta0, -zeta0, -zeta0,
            -zeta0, zeta0, zeta0, zeta0, zeta0,
        );

        let rhs = _mm256_shuffle_epi32(v.elements, 0b11_10_11_10);
        let rhs = montgomery_multiply_by_constants(rhs, zetas);

        let lhs = _mm256_shuffle_epi32(v.elements, 0b01_00_01_00);

        _mm256_add_epi16(lhs, rhs)
    };

    v
}

#[inline(always)]
fn ntt_layer_3_step(mut v: SIMD256Vector, zeta: i16) -> SIMD256Vector {
    v.elements = unsafe {
        let rhs = _mm256_extracti128_si256(v.elements, 1);
        let rhs = montgomery_multiply_m128i_by_constants(rhs, _mm_set1_epi16(zeta));

        let lhs = _mm256_castsi256_si128(v.elements);

        let lower_coefficients = _mm_add_epi16(lhs, rhs);
        let upper_coefficients = _mm_sub_epi16(lhs, rhs);

        let combined = _mm256_castsi128_si256(lower_coefficients);
        let combined = _mm256_inserti128_si256(combined, upper_coefficients, 1);

        combined
    };

    v
}

#[inline(always)]
fn inv_ntt_layer_1_step(
    mut v: SIMD256Vector,
    zeta0: i16,
    zeta1: i16,
    zeta2: i16,
    zeta3: i16,
) -> SIMD256Vector {
    v.elements = unsafe {
        let lhs = _mm256_shuffle_epi32(v.elements, 0b11_11_01_01);

        let rhs = _mm256_shuffle_epi32(v.elements, 0b10_10_00_00);
        let rhs = _mm256_mullo_epi16(
            rhs,
            _mm256_set_epi16(-1, -1, 1, 1, -1, -1, 1, 1, -1, -1, 1, 1, -1, -1, 1, 1),
        );

        let sum = _mm256_add_epi16(lhs, rhs);
        let sum_times_zetas = montgomery_multiply_by_constants(
            sum,
            _mm256_set_epi16(
                zeta3, zeta3, 0, 0, zeta2, zeta2, 0, 0, zeta1, zeta1, 0, 0, zeta0, zeta0, 0, 0,
            ),
        );

        let sum = barrett_reduce(SIMD256Vector { elements: sum }).elements;

        _mm256_blend_epi16(sum, sum_times_zetas, 0b1_1_0_0_1_1_0_0)
    };

    v
}

#[inline(always)]
fn inv_ntt_layer_2_step(mut v: SIMD256Vector, zeta0: i16, zeta1: i16) -> SIMD256Vector {
    v.elements = unsafe {
        let lhs = _mm256_permute4x64_epi64(v.elements, 0b11_11_01_01);

        let rhs = _mm256_permute4x64_epi64(v.elements, 0b10_10_00_00);
        let rhs = _mm256_mullo_epi16(
            rhs,
            _mm256_set_epi16(-1, -1, -1, -1, 1, 1, 1, 1, -1, -1, -1, -1, 1, 1, 1, 1),
        );

        let sum = _mm256_add_epi16(lhs, rhs);
        let sum_times_zetas = montgomery_multiply_by_constants(
            sum,
            _mm256_set_epi16(
                zeta1, zeta1, zeta1, zeta1, 0, 0, 0, 0, zeta0, zeta0, zeta0, zeta0, 0, 0, 0, 0,
            ),
        );

        _mm256_blend_epi16(sum, sum_times_zetas, 0b1_1_1_1_0_0_0_0)
    };

    v
}

#[inline(always)]
fn inv_ntt_layer_3_step(mut v: SIMD256Vector, zeta: i16) -> SIMD256Vector {
    v.elements = unsafe {
        let lhs = _mm256_extracti128_si256(v.elements, 1);
        let rhs = _mm256_castsi256_si128(v.elements);

        let lower_coefficients = _mm_add_epi16(lhs, rhs);

        let upper_coefficients = _mm_sub_epi16(lhs, rhs);
        let upper_coefficients =
            montgomery_multiply_m128i_by_constants(upper_coefficients, _mm_set1_epi16(zeta));

        let combined = _mm256_castsi128_si256(lower_coefficients);
        let combined = _mm256_inserti128_si256(combined, upper_coefficients, 1);

        combined
    };

    v
}

#[inline(always)]
fn ntt_multiply(
    lhs: &SIMD256Vector,
    rhs: &SIMD256Vector,
    zeta0: i16,
    zeta1: i16,
    zeta2: i16,
    zeta3: i16,
) -> SIMD256Vector {
    let products = unsafe {
        // Compute the first term of the product
        let shuffle_with = _mm256_set_epi8(
            15, 14, 11, 10, 7, 6, 3, 2, 13, 12, 9, 8, 5, 4, 1, 0, 15, 14, 11, 10, 7, 6, 3, 2, 13,
            12, 9, 8, 5, 4, 1, 0,
        );
        const PERMUTE_WITH: i32 = 0b11_01_10_00;

        // Prepare the left hand side
        let lhs_shuffled = _mm256_shuffle_epi8(lhs.elements, shuffle_with);
        let lhs_shuffled = _mm256_permute4x64_epi64(lhs_shuffled, PERMUTE_WITH);

        let lhs_evens = _mm256_castsi256_si128(lhs_shuffled);
        let lhs_evens = _mm256_cvtepi16_epi32(lhs_evens);

        let lhs_odds = _mm256_extracti128_si256(lhs_shuffled, 1);
        let lhs_odds = _mm256_cvtepi16_epi32(lhs_odds);

        // Prepare the right hand side
        let rhs_shuffled = _mm256_shuffle_epi8(rhs.elements, shuffle_with);
        let rhs_shuffled = _mm256_permute4x64_epi64(rhs_shuffled, PERMUTE_WITH);

        let rhs_evens = _mm256_castsi256_si128(rhs_shuffled);
        let rhs_evens = _mm256_cvtepi16_epi32(rhs_evens);

        let rhs_odds = _mm256_extracti128_si256(rhs_shuffled, 1);
        let rhs_odds = _mm256_cvtepi16_epi32(rhs_odds);

        // Start operating with them
        let left = _mm256_mullo_epi32(lhs_evens, rhs_evens);

        let right = _mm256_mullo_epi32(lhs_odds, rhs_odds);
        let right = montgomery_reduce_i32s(right);
        let right = _mm256_mullo_epi32(
            right,
            _mm256_set_epi32(
                -(zeta3 as i32),
                zeta3 as i32,
                -(zeta2 as i32),
                zeta2 as i32,
                -(zeta1 as i32),
                zeta1 as i32,
                -(zeta0 as i32),
                zeta0 as i32,
            ),
        );

        let products_left = _mm256_add_epi32(left, right);
        let products_left = montgomery_reduce_i32s(products_left);

        // Compute the second term of the product
        let rhs_adjacent_swapped = _mm256_shuffle_epi8(
            rhs.elements,
            _mm256_set_epi8(
                13, 12, 15, 14, 9, 8, 11, 10, 5, 4, 7, 6, 1, 0, 3, 2, 13, 12, 15, 14, 9, 8, 11, 10,
                5, 4, 7, 6, 1, 0, 3, 2,
            ),
        );
        let products_right = _mm256_madd_epi16(lhs.elements, rhs_adjacent_swapped);
        let products_right = montgomery_reduce_i32s(products_right);
        let products_right = _mm256_slli_epi32(products_right, 16);

        // Combine them into one vector
        _mm256_blend_epi16(products_left, products_right, 0b1_0_1_0_1_0_1_0)
    };

    SIMD256Vector { elements: products }
}

#[inline(always)]
fn serialize_1(v: SIMD256Vector) -> [u8; 2] {
    let mut serialized = [0u8; 2];

    let bits_packed = unsafe {
        let lsb_shifted_up = _mm256_slli_epi16(v.elements, 15);

        let low_lanes = _mm256_castsi256_si128(lsb_shifted_up);
        let high_lanes = _mm256_extracti128_si256(lsb_shifted_up, 1);

        let msbs = _mm_packs_epi16(low_lanes, high_lanes);

        _mm_movemask_epi8(msbs)
    };

    serialized[0] = bits_packed as u8;
    serialized[1] = (bits_packed >> 8) as u8;

    serialized
}

#[inline(always)]
fn deserialize_1(bytes: &[u8]) -> SIMD256Vector {
    let deserialized = unsafe {
        let shift_lsb_to_msb = _mm256_set_epi16(
            1 << 0,
            1 << 1,
            1 << 2,
            1 << 3,
            1 << 4,
            1 << 5,
            1 << 6,
            1 << 7,
            1 << 0,
            1 << 1,
            1 << 2,
            1 << 3,
            1 << 4,
            1 << 5,
            1 << 6,
            1 << 7,
        );

        let coefficients = _mm256_set_epi16(
            bytes[1] as i16,
            bytes[1] as i16,
            bytes[1] as i16,
            bytes[1] as i16,
            bytes[1] as i16,
            bytes[1] as i16,
            bytes[1] as i16,
            bytes[1] as i16,
            bytes[0] as i16,
            bytes[0] as i16,
            bytes[0] as i16,
            bytes[0] as i16,
            bytes[0] as i16,
            bytes[0] as i16,
            bytes[0] as i16,
            bytes[0] as i16,
        );

        let coefficients_in_msb = _mm256_mullo_epi16(coefficients, shift_lsb_to_msb);
        let coefficients_in_lsb = _mm256_srli_epi16(coefficients_in_msb, 7);

        _mm256_and_si256(coefficients_in_lsb, _mm256_set1_epi16((1 << 1) - 1))
    };

    SIMD256Vector {
        elements: deserialized,
    }
}

#[inline(always)]
fn serialize_4(v: SIMD256Vector) -> [u8; 8] {
    let mut serialized = [0u8; 16];

    unsafe {
        let adjacent_2_combined = _mm256_madd_epi16(
            v.elements,
            _mm256_set_epi16(
                1 << 4,
                1,
                1 << 4,
                1,
                1 << 4,
                1,
                1 << 4,
                1,
                1 << 4,
                1,
                1 << 4,
                1,
                1 << 4,
                1,
                1 << 4,
                1,
            ),
        );

        let adjacent_8_combined = _mm256_shuffle_epi8(
            adjacent_2_combined,
            _mm256_set_epi8(
                -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, 12, 8, 4, 0, -1, -1, -1, -1, -1,
                -1, -1, -1, -1, -1, -1, -1, 12, 8, 4, 0,
            ),
        );

        let combined = _mm256_permutevar8x32_epi32(
            adjacent_8_combined,
            _mm256_set_epi32(0, 0, 0, 0, 0, 0, 4, 0),
        );
        let combined = _mm256_castsi256_si128(combined);

        _mm_storeu_si128(serialized.as_mut_ptr() as *mut __m128i, combined);
    }

    serialized[0..8].try_into().unwrap()
}

#[inline(always)]
fn deserialize_4(bytes: &[u8]) -> SIMD256Vector {
    let deserialized = unsafe {
        let shift_lsbs_to_msbs = _mm256_set_epi16(
            1 << 0,
            1 << 4,
            1 << 0,
            1 << 4,
            1 << 0,
            1 << 4,
            1 << 0,
            1 << 4,
            1 << 0,
            1 << 4,
            1 << 0,
            1 << 4,
            1 << 0,
            1 << 4,
            1 << 0,
            1 << 4,
        );

        let coefficients = _mm256_set_epi16(
            bytes[7] as i16,
            bytes[7] as i16,
            bytes[6] as i16,
            bytes[6] as i16,
            bytes[5] as i16,
            bytes[5] as i16,
            bytes[4] as i16,
            bytes[4] as i16,
            bytes[3] as i16,
            bytes[3] as i16,
            bytes[2] as i16,
            bytes[2] as i16,
            bytes[1] as i16,
            bytes[1] as i16,
            bytes[0] as i16,
            bytes[0] as i16,
        );

        let coefficients_in_msb = _mm256_mullo_epi16(coefficients, shift_lsbs_to_msbs);
        let coefficients_in_lsb = _mm256_srli_epi16(coefficients_in_msb, 4);

        _mm256_and_si256(coefficients_in_lsb, _mm256_set1_epi16((1 << 4) - 1))
    };

    SIMD256Vector {
        elements: deserialized,
    }
}

#[inline(always)]
fn serialize_5(v: SIMD256Vector) -> [u8; 10] {
    let mut serialized = [0u8; 32];

    unsafe {
        let adjacent_2_combined = _mm256_madd_epi16(
            v.elements,
            _mm256_set_epi16(
                1 << 5,
                1,
                1 << 5,
                1,
                1 << 5,
                1,
                1 << 5,
                1,
                1 << 5,
                1,
                1 << 5,
                1,
                1 << 5,
                1,
                1 << 5,
                1,
            ),
        );

        let adjacent_4_combined = _mm256_sllv_epi32(
            adjacent_2_combined,
            _mm256_set_epi32(0, 22, 0, 22, 0, 22, 0, 22),
        );
        let adjacent_4_combined = _mm256_srli_epi64(adjacent_4_combined, 22);

        let adjacent_8_combined = _mm256_shuffle_epi32(adjacent_4_combined, 0b00_00_10_00);
        let adjacent_8_combined = _mm256_sllv_epi32(
            adjacent_8_combined,
            _mm256_set_epi32(0, 12, 0, 12, 0, 12, 0, 12),
        );
        let adjacent_8_combined = _mm256_srli_epi64(adjacent_8_combined, 12);

        let lower_8 = _mm256_castsi256_si128(adjacent_8_combined);
        let upper_8 = _mm256_extracti128_si256(adjacent_8_combined, 1);

        _mm_storeu_si128(serialized.as_mut_ptr() as *mut __m128i, lower_8);
        _mm_storeu_si128(serialized.as_mut_ptr().offset(5) as *mut __m128i, upper_8);
    }

    serialized[0..10].try_into().unwrap()
}

#[inline(always)]
fn deserialize_5(v: &[u8]) -> SIMD256Vector {
    let output = portable::deserialize_5(v);

    from_i16_array(&portable::to_i16_array(output))
}

#[inline(always)]
fn serialize_10(v: SIMD256Vector) -> [u8; 20] {
    let mut serialized = [0u8; 32];

    unsafe {
        let adjacent_2_combined = _mm256_madd_epi16(
            v.elements,
            _mm256_set_epi16(
                1 << 10,
                1,
                1 << 10,
                1,
                1 << 10,
                1,
                1 << 10,
                1,
                1 << 10,
                1,
                1 << 10,
                1,
                1 << 10,
                1,
                1 << 10,
                1,
            ),
        );

        let adjacent_4_combined = _mm256_sllv_epi32(
            adjacent_2_combined,
            _mm256_set_epi32(0, 12, 0, 12, 0, 12, 0, 12),
        );
        let adjacent_4_combined = _mm256_srli_epi64(adjacent_4_combined, 12);

        let adjacent_8_combined = _mm256_shuffle_epi8(
            adjacent_4_combined,
            _mm256_set_epi8(
                -1, -1, -1, -1, -1, -1, 12, 11, 10, 9, 8, 4, 3, 2, 1, 0, -1, -1, -1, -1, -1, -1,
                12, 11, 10, 9, 8, 4, 3, 2, 1, 0,
            ),
        );

        let lower_8 = _mm256_castsi256_si128(adjacent_8_combined);
        let upper_8 = _mm256_extracti128_si256(adjacent_8_combined, 1);

        _mm_storeu_si128(serialized.as_mut_ptr() as *mut __m128i, lower_8);
        _mm_storeu_si128(serialized.as_mut_ptr().offset(10) as *mut __m128i, upper_8);
    }

    serialized[0..20].try_into().unwrap()
}

#[inline(always)]
fn deserialize_10(v: &[u8]) -> SIMD256Vector {
    let deserialized = unsafe {
        let shift_lsbs_to_msbs = _mm256_set_epi16(
            1 << 0,
            1 << 2,
            1 << 4,
            1 << 6,
            1 << 0,
            1 << 2,
            1 << 4,
            1 << 6,
            1 << 0,
            1 << 2,
            1 << 4,
            1 << 6,
            1 << 0,
            1 << 2,
            1 << 4,
            1 << 6,
        );

        let lower_coefficients = _mm_loadu_si128(v.as_ptr() as *const __m128i);
        let lower_coefficients = _mm_shuffle_epi8(
            lower_coefficients,
            _mm_set_epi8(9, 8, 8, 7, 7, 6, 6, 5, 4, 3, 3, 2, 2, 1, 1, 0),
        );
        let upper_coefficients = _mm_loadu_si128(v.as_ptr().offset(4) as *const __m128i);
        let upper_coefficients = _mm_shuffle_epi8(
            upper_coefficients,
            _mm_set_epi8(15, 14, 14, 13, 13, 12, 12, 11, 10, 9, 9, 8, 8, 7, 7, 6),
        );

        let coefficients = _mm256_castsi128_si256(lower_coefficients);
        let coefficients = _mm256_inserti128_si256(coefficients, upper_coefficients, 1);

        let coefficients = _mm256_mullo_epi16(coefficients, shift_lsbs_to_msbs);
        let coefficients = _mm256_srli_epi16(coefficients, 6);
        let coefficients = _mm256_and_si256(coefficients, _mm256_set1_epi16((1 << 10) - 1));

        coefficients
    };

    SIMD256Vector {
        elements: deserialized,
    }
}

#[inline(always)]
fn serialize_11(v: SIMD256Vector) -> [u8; 22] {
    let input = portable::from_i16_array(to_i16_array(v));

    portable::serialize_11(input)
}

#[inline(always)]
fn deserialize_11(v: &[u8]) -> SIMD256Vector {
    let output = portable::deserialize_11(v);

    from_i16_array(&portable::to_i16_array(output))
}

#[inline(always)]
fn serialize_12(v: SIMD256Vector) -> [u8; 24] {
    let mut serialized = [0u8; 32];

    unsafe {
        let adjacent_2_combined = _mm256_madd_epi16(
            v.elements,
            _mm256_set_epi16(
                1 << 12,
                1,
                1 << 12,
                1,
                1 << 12,
                1,
                1 << 12,
                1,
                1 << 12,
                1,
                1 << 12,
                1,
                1 << 12,
                1,
                1 << 12,
                1,
            ),
        );

        let adjacent_4_combined = _mm256_sllv_epi32(
            adjacent_2_combined,
            _mm256_set_epi32(0, 8, 0, 8, 0, 8, 0, 8),
        );
        let adjacent_4_combined = _mm256_srli_epi64(adjacent_4_combined, 8);

        let adjacent_8_combined = _mm256_shuffle_epi8(
            adjacent_4_combined,
            _mm256_set_epi8(
                -1, -1, -1, -1, 13, 12, 11, 10, 9, 8, 5, 4, 3, 2, 1, 0, -1, -1, -1, -1, 13, 12, 11,
                10, 9, 8, 5, 4, 3, 2, 1, 0,
            ),
        );

        let lower_8 = _mm256_castsi256_si128(adjacent_8_combined);
        let upper_8 = _mm256_extracti128_si256(adjacent_8_combined, 1);

        _mm_storeu_si128(serialized.as_mut_ptr() as *mut __m128i, lower_8);
        _mm_storeu_si128(serialized.as_mut_ptr().offset(12) as *mut __m128i, upper_8);
    }

    serialized[0..24].try_into().unwrap()
}

#[inline(always)]
fn deserialize_12(v: &[u8]) -> SIMD256Vector {
    let deserialized = unsafe {
        let shift_lsbs_to_msbs = _mm256_set_epi16(
            1 << 0,
            1 << 4,
            1 << 0,
            1 << 4,
            1 << 0,
            1 << 4,
            1 << 0,
            1 << 4,
            1 << 0,
            1 << 4,
            1 << 0,
            1 << 4,
            1 << 0,
            1 << 4,
            1 << 0,
            1 << 4,
        );

        let lower_coefficients = _mm_loadu_si128(v.as_ptr() as *const __m128i);
        let lower_coefficients = _mm_shuffle_epi8(
            lower_coefficients,
            _mm_set_epi8(11, 10, 10, 9, 8, 7, 7, 6, 5, 4, 4, 3, 2, 1, 1, 0),
        );
        let upper_coefficients = _mm_loadu_si128(v.as_ptr().offset(8) as *const __m128i);
        let upper_coefficients = _mm_shuffle_epi8(
            upper_coefficients,
            _mm_set_epi8(15, 14, 14, 13, 12, 11, 11, 10, 9, 8, 8, 7, 6, 5, 5, 4),
        );

        let coefficients = _mm256_castsi128_si256(lower_coefficients);
        let coefficients = _mm256_inserti128_si256(coefficients, upper_coefficients, 1);

        let coefficients = _mm256_mullo_epi16(coefficients, shift_lsbs_to_msbs);
        let coefficients = _mm256_srli_epi16(coefficients, 4);
        let coefficients = _mm256_and_si256(coefficients, _mm256_set1_epi16((1 << 12) - 1));

        coefficients
    };

    SIMD256Vector {
        elements: deserialized,
    }
}

#[inline(always)]
pub(crate) fn rej_sample(uniform_bytes: &[u8], out: &mut [i16]) -> usize {
    let count = unsafe {
        let field_modulus = _mm256_set1_epi16(FIELD_MODULUS);
        let ones = _mm_set1_epi8(1);

        let potential_coefficients = deserialize_12(uniform_bytes).elements;

        let compare_with_field_modulus = _mm256_cmpgt_epi16(field_modulus, potential_coefficients);
        let good = serialize_1(SIMD256Vector {
            elements: compare_with_field_modulus,
        });

        // Write out the indices indicated by the set bits of |good| such that
        // the "good" elements can be read in sequence from the beginning of
        // |potential_coefficients|

        // Start with the first 8 bits, i.e. |good[0]|
        let byte_start_indices = _pdep_u64(good[0] as u64, 0x0101010101010101) as u128;
        let byte_start_indices = ((byte_start_indices << 8) - byte_start_indices) as u64;
        let byte_start_indices = _pext_u64(0x0E0C0A0806040200, byte_start_indices);

        let byte_shuffle_indices_first_byte = _mm_cvtsi64_si128(byte_start_indices as i64);
        let byte_shuffle_indices_second_byte = _mm_add_epi8(byte_shuffle_indices_first_byte, ones);

        let byte_shuffle_indices_low = _mm_unpacklo_epi8(
            byte_shuffle_indices_first_byte,
            byte_shuffle_indices_second_byte,
        );

        // Then the next 8 bits, i.e. |good[1]|
        let byte_start_indices = _pdep_u64(good[1] as u64, 0x0101010101010101) as u128;
        let byte_start_indices = ((byte_start_indices << 8) - byte_start_indices) as u64;
        let byte_start_indices = _pext_u64(0x0E0C0A0806040200, byte_start_indices);

        let byte_shuffle_indices_first_byte = _mm_cvtsi64_si128(byte_start_indices as i64);
        let byte_shuffle_indices_second_byte = _mm_add_epi8(byte_shuffle_indices_first_byte, ones);

        let byte_shuffle_indices_high = _mm_unpacklo_epi8(
            byte_shuffle_indices_first_byte,
            byte_shuffle_indices_second_byte,
        );

        // Write out the indices to an __m256 and then shuffle
        let byte_shuffle_indices = _mm256_castsi128_si256(byte_shuffle_indices_low);
        let byte_shuffle_indices =
            _mm256_inserti128_si256(byte_shuffle_indices, byte_shuffle_indices_high, 1);

        let coefficients = _mm256_shuffle_epi8(potential_coefficients, byte_shuffle_indices);

        // Write out the elements themselves
        let low_coefficients = _mm256_castsi256_si128(coefficients);
        _mm_storeu_si128(out.as_mut_ptr() as *mut __m128i, low_coefficients);
        let count_sampled = good[0].count_ones();

        let high_coefficients = _mm256_extracti128_si256(coefficients, 1);
        _mm_storeu_si128(
            out.as_mut_ptr().offset(count_sampled as isize) as *mut __m128i,
            high_coefficients,
        );
        let count_sampled = count_sampled + good[1].count_ones();

        count_sampled
    };

    count as usize
}

impl Operations for SIMD256Vector {
    fn ZERO() -> Self {
        zero()
    }

    fn to_i16_array(v: Self) -> [i16; 16] {
        to_i16_array(v)
    }

    fn from_i16_array(array: &[i16]) -> Self {
        from_i16_array(array)
    }

    fn add(lhs: Self, rhs: &Self) -> Self {
        add(lhs, rhs)
    }

    fn sub(lhs: Self, rhs: &Self) -> Self {
        sub(lhs, rhs)
    }

    fn multiply_by_constant(v: Self, c: i16) -> Self {
        multiply_by_constant(v, c)
    }

    fn bitwise_and_with_constant(v: Self, c: i16) -> Self {
        bitwise_and_with_constant(v, c)
    }

    fn shift_right<const SHIFT_BY: i32>(v: Self) -> Self {
        shift_right::<{ SHIFT_BY }>(v)
    }

    fn shift_left<const SHIFT_BY: i32>(v: Self) -> Self {
        shift_left::<{ SHIFT_BY }>(v)
    }

    fn cond_subtract_3329(v: Self) -> Self {
        cond_subtract_3329(v)
    }

    fn barrett_reduce(v: Self) -> Self {
        barrett_reduce(v)
    }

    fn montgomery_multiply_by_constant(v: Self, r: i16) -> Self {
        montgomery_multiply_by_constant(v, r)
    }

    fn compress_1(v: Self) -> Self {
        compress_1(v)
    }

    fn compress<const COEFFICIENT_BITS: i32>(v: Self) -> Self {
        compress::<COEFFICIENT_BITS>(v)
    }

    fn decompress_ciphertext_coefficient<const COEFFICIENT_BITS: i32>(v: Self) -> Self {
        decompress_ciphertext_coefficient::<COEFFICIENT_BITS>(v)
    }

    fn ntt_layer_1_step(a: Self, zeta0: i16, zeta1: i16, zeta2: i16, zeta3: i16) -> Self {
        ntt_layer_1_step(a, zeta0, zeta1, zeta2, zeta3)
    }

    fn ntt_layer_2_step(a: Self, zeta0: i16, zeta1: i16) -> Self {
        ntt_layer_2_step(a, zeta0, zeta1)
    }

    fn ntt_layer_3_step(a: Self, zeta: i16) -> Self {
        ntt_layer_3_step(a, zeta)
    }

    fn inv_ntt_layer_1_step(a: Self, zeta0: i16, zeta1: i16, zeta2: i16, zeta3: i16) -> Self {
        inv_ntt_layer_1_step(a, zeta0, zeta1, zeta2, zeta3)
    }

    fn inv_ntt_layer_2_step(a: Self, zeta0: i16, zeta1: i16) -> Self {
        inv_ntt_layer_2_step(a, zeta0, zeta1)
    }

    fn inv_ntt_layer_3_step(a: Self, zeta: i16) -> Self {
        inv_ntt_layer_3_step(a, zeta)
    }

    fn ntt_multiply(
        lhs: &Self,
        rhs: &Self,
        zeta0: i16,
        zeta1: i16,
        zeta2: i16,
        zeta3: i16,
    ) -> Self {
        ntt_multiply(lhs, rhs, zeta0, zeta1, zeta2, zeta3)
    }

    fn serialize_1(a: Self) -> [u8; 2] {
        serialize_1(a)
    }

    fn deserialize_1(a: &[u8]) -> Self {
        deserialize_1(a)
    }

    fn serialize_4(a: Self) -> [u8; 8] {
        serialize_4(a)
    }

    fn deserialize_4(a: &[u8]) -> Self {
        deserialize_4(a)
    }

    fn serialize_5(a: Self) -> [u8; 10] {
        serialize_5(a)
    }

    fn deserialize_5(a: &[u8]) -> Self {
        deserialize_5(a)
    }

    fn serialize_10(a: Self) -> [u8; 20] {
        serialize_10(a)
    }

    fn deserialize_10(a: &[u8]) -> Self {
        deserialize_10(a)
    }

    fn serialize_11(a: Self) -> [u8; 22] {
        serialize_11(a)
    }

    fn deserialize_11(a: &[u8]) -> Self {
        deserialize_11(a)
    }

    fn serialize_12(a: Self) -> [u8; 24] {
        serialize_12(a)
    }

    fn deserialize_12(a: &[u8]) -> Self {
        deserialize_12(a)
    }

    fn rej_sample(a: &[u8], out: &mut [i16]) -> usize {
        rej_sample(a, out)
    }
}
