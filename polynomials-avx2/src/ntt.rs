#[cfg(target_arch = "x86")]
use core::arch::x86::*;
#[cfg(target_arch = "x86_64")]
use core::arch::x86_64::*;

use crate::{arithmetic, SIMD256Vector};
use libcrux_traits::{FIELD_MODULUS, INVERSE_OF_MODULUS_MOD_MONTGOMERY_R};

#[inline(always)]
pub(crate) fn montgomery_multiply_by_constants(mut v: __m256i, c: __m256i) -> __m256i {
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
pub(crate) fn montgomery_reduce_i32s(mut v: __m256i) -> __m256i {
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
pub(crate) fn montgomery_multiply_m128i_by_constants(mut v: __m128i, c: __m128i) -> __m128i {
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
pub(crate) fn ntt_layer_1_step(
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
pub(crate) fn ntt_layer_2_step(mut v: SIMD256Vector, zeta0: i16, zeta1: i16) -> SIMD256Vector {
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
pub(crate) fn ntt_layer_3_step(mut v: SIMD256Vector, zeta: i16) -> SIMD256Vector {
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
pub(crate) fn inv_ntt_layer_1_step(
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

        let sum = arithmetic::barrett_reduce(SIMD256Vector { elements: sum }).elements;

        _mm256_blend_epi16(sum, sum_times_zetas, 0b1_1_0_0_1_1_0_0)
    };

    v
}

#[inline(always)]
pub(crate) fn inv_ntt_layer_2_step(mut v: SIMD256Vector, zeta0: i16, zeta1: i16) -> SIMD256Vector {
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
pub(crate) fn inv_ntt_layer_3_step(mut v: SIMD256Vector, zeta: i16) -> SIMD256Vector {
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
pub(crate) fn ntt_multiply(
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
