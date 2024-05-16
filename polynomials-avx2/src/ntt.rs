use crate::intrinsics::*;

use crate::arithmetic;
use libcrux_traits::{FIELD_MODULUS, INVERSE_OF_MODULUS_MOD_MONTGOMERY_R};

#[inline(always)]
fn montgomery_multiply_by_constants(v: __m256i, c: __m256i) -> __m256i {
    let value_low = mm256_mullo_epi16(v, c);

    let k = mm256_mullo_epi16(
        value_low,
        mm256_set1_epi16(INVERSE_OF_MODULUS_MOD_MONTGOMERY_R as i16),
    );
    let k_times_modulus = mm256_mulhi_epi16(k, mm256_set1_epi16(FIELD_MODULUS));

    let value_high = mm256_mulhi_epi16(v, c);

    mm256_sub_epi16(value_high, k_times_modulus)
}

#[inline(always)]
fn montgomery_reduce_i32s(v: __m256i) -> __m256i {
    let k = mm256_mullo_epi16(
        v,
        mm256_set1_epi32(INVERSE_OF_MODULUS_MOD_MONTGOMERY_R as i32),
    );
    let k_times_modulus = mm256_mulhi_epi16(k, mm256_set1_epi32(FIELD_MODULUS as i32));

    let value_high = mm256_srli_epi32::<16>(v);

    let result = mm256_sub_epi16(value_high, k_times_modulus);

    let result = mm256_slli_epi32::<16>(result);

    mm256_srai_epi32::<16>(result)
}

#[inline(always)]
fn montgomery_multiply_m128i_by_constants(v: __m128i, c: __m128i) -> __m128i {
    let value_low = mm_mullo_epi16(v, c);

    let k = mm_mullo_epi16(
        value_low,
        mm_set1_epi16(INVERSE_OF_MODULUS_MOD_MONTGOMERY_R as i16),
    );
    let k_times_modulus = mm_mulhi_epi16(k, mm_set1_epi16(FIELD_MODULUS));

    let value_high = mm_mulhi_epi16(v, c);

    mm_sub_epi16(value_high, k_times_modulus)
}

#[inline(always)]
pub(crate) fn ntt_layer_1_step(
    vector: __m256i,
    zeta0: i16,
    zeta1: i16,
    zeta2: i16,
    zeta3: i16,
) -> __m256i {
    let zetas = mm256_set_epi16(
        -zeta3, -zeta3, zeta3, zeta3, -zeta2, -zeta2, zeta2, zeta2, -zeta1, -zeta1, zeta1, zeta1,
        -zeta0, -zeta0, zeta0, zeta0,
    );

    let rhs = mm256_shuffle_epi32::<0b11_11_01_01>(vector);
    let rhs = montgomery_multiply_by_constants(rhs, zetas);

    let lhs = mm256_shuffle_epi32::<0b10_10_00_00>(vector);

    mm256_add_epi16(lhs, rhs)
}

#[inline(always)]
pub(crate) fn ntt_layer_2_step(vector: __m256i, zeta0: i16, zeta1: i16) -> __m256i {
    let zetas = mm256_set_epi16(
        -zeta1, -zeta1, -zeta1, -zeta1, zeta1, zeta1, zeta1, zeta1, -zeta0, -zeta0, -zeta0, -zeta0,
        zeta0, zeta0, zeta0, zeta0,
    );

    let rhs = mm256_shuffle_epi32::<0b11_10_11_10>(vector);
    let rhs = montgomery_multiply_by_constants(rhs, zetas);

    let lhs = mm256_shuffle_epi32::<0b01_00_01_00>(vector);

    mm256_add_epi16(lhs, rhs)
}

#[inline(always)]
pub(crate) fn ntt_layer_3_step(vector: __m256i, zeta: i16) -> __m256i {
    let rhs = mm256_extracti128_si256::<1>(vector);
    let rhs = montgomery_multiply_m128i_by_constants(rhs, mm_set1_epi16(zeta));

    let lhs = mm256_castsi256_si128(vector);

    let lower_coefficients = mm_add_epi16(lhs, rhs);
    let upper_coefficients = mm_sub_epi16(lhs, rhs);

    let combined = mm256_castsi128_si256(lower_coefficients);
    let combined = mm256_inserti128_si256::<1>(combined, upper_coefficients);

    combined
}

#[inline(always)]
pub(crate) fn inv_ntt_layer_1_step(
    vector: __m256i,
    zeta0: i16,
    zeta1: i16,
    zeta2: i16,
    zeta3: i16,
) -> __m256i {
    let lhs = mm256_shuffle_epi32::<0b11_11_01_01>(vector);

    let rhs = mm256_shuffle_epi32::<0b10_10_00_00>(vector);
    let rhs = mm256_mullo_epi16(
        rhs,
        mm256_set_epi16(-1, -1, 1, 1, -1, -1, 1, 1, -1, -1, 1, 1, -1, -1, 1, 1),
    );

    let sum = mm256_add_epi16(lhs, rhs);
    let sum_times_zetas = montgomery_multiply_by_constants(
        sum,
        mm256_set_epi16(
            zeta3, zeta3, 0, 0, zeta2, zeta2, 0, 0, zeta1, zeta1, 0, 0, zeta0, zeta0, 0, 0,
        ),
    );

    let sum = arithmetic::barrett_reduce(sum);

    mm256_blend_epi16::<0b1_1_0_0_1_1_0_0>(sum, sum_times_zetas)
}

#[inline(always)]
pub(crate) fn inv_ntt_layer_2_step(vector: __m256i, zeta0: i16, zeta1: i16) -> __m256i {
    let lhs = mm256_permute4x64_epi64::<0b11_11_01_01>(vector);

    let rhs = mm256_permute4x64_epi64::<0b10_10_00_00>(vector);
    let rhs = mm256_mullo_epi16(
        rhs,
        mm256_set_epi16(-1, -1, -1, -1, 1, 1, 1, 1, -1, -1, -1, -1, 1, 1, 1, 1),
    );

    let sum = mm256_add_epi16(lhs, rhs);
    let sum_times_zetas = montgomery_multiply_by_constants(
        sum,
        mm256_set_epi16(
            zeta1, zeta1, zeta1, zeta1, 0, 0, 0, 0, zeta0, zeta0, zeta0, zeta0, 0, 0, 0, 0,
        ),
    );

    mm256_blend_epi16::<0b1_1_1_1_0_0_0_0>(sum, sum_times_zetas)
}

#[inline(always)]
pub(crate) fn inv_ntt_layer_3_step(vector: __m256i, zeta: i16) -> __m256i {
    let lhs = mm256_extracti128_si256::<1>(vector);
    let rhs = mm256_castsi256_si128(vector);

    let lower_coefficients = mm_add_epi16(lhs, rhs);

    let upper_coefficients = mm_sub_epi16(lhs, rhs);
    let upper_coefficients =
        montgomery_multiply_m128i_by_constants(upper_coefficients, mm_set1_epi16(zeta));

    let combined = mm256_castsi128_si256(lower_coefficients);
    let combined = mm256_inserti128_si256::<1>(combined, upper_coefficients);

    combined
}

#[inline(always)]
pub(crate) fn ntt_multiply(
    lhs: __m256i,
    rhs: __m256i,
    zeta0: i16,
    zeta1: i16,
    zeta2: i16,
    zeta3: i16,
) -> __m256i {
    // Compute the first term of the product
    let shuffle_with = mm256_set_epi8(
        15, 14, 11, 10, 7, 6, 3, 2, 13, 12, 9, 8, 5, 4, 1, 0, 15, 14, 11, 10, 7, 6, 3, 2, 13, 12,
        9, 8, 5, 4, 1, 0,
    );
    const PERMUTE_WITH: i32 = 0b11_01_10_00;

    // Prepare the left hand side
    let lhs_shuffled = mm256_shuffle_epi8(lhs, shuffle_with);
    let lhs_shuffled = mm256_permute4x64_epi64::<{ PERMUTE_WITH }>(lhs_shuffled);

    let lhs_evens = mm256_castsi256_si128(lhs_shuffled);
    let lhs_evens = mm256_cvtepi16_epi32(lhs_evens);

    let lhs_odds = mm256_extracti128_si256::<1>(lhs_shuffled);
    let lhs_odds = mm256_cvtepi16_epi32(lhs_odds);

    // Prepare the right hand side
    let rhs_shuffled = mm256_shuffle_epi8(rhs, shuffle_with);
    let rhs_shuffled = mm256_permute4x64_epi64::<{ PERMUTE_WITH }>(rhs_shuffled);

    let rhs_evens = mm256_castsi256_si128(rhs_shuffled);
    let rhs_evens = mm256_cvtepi16_epi32(rhs_evens);

    let rhs_odds = mm256_extracti128_si256::<1>(rhs_shuffled);
    let rhs_odds = mm256_cvtepi16_epi32(rhs_odds);

    // Start operating with them
    let left = mm256_mullo_epi32(lhs_evens, rhs_evens);

    let right = mm256_mullo_epi32(lhs_odds, rhs_odds);
    let right = montgomery_reduce_i32s(right);
    let right = mm256_mullo_epi32(
        right,
        mm256_set_epi32(
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

    let products_left = mm256_add_epi32(left, right);
    let products_left = montgomery_reduce_i32s(products_left);

    // Compute the second term of the product
    let rhs_adjacent_swapped = mm256_shuffle_epi8(
        rhs,
        mm256_set_epi8(
            13, 12, 15, 14, 9, 8, 11, 10, 5, 4, 7, 6, 1, 0, 3, 2, 13, 12, 15, 14, 9, 8, 11, 10, 5,
            4, 7, 6, 1, 0, 3, 2,
        ),
    );
    let products_right = mm256_madd_epi16(lhs, rhs_adjacent_swapped);
    let products_right = montgomery_reduce_i32s(products_right);
    let products_right = mm256_slli_epi32::<16>(products_right);

    // Combine them into one vector
    mm256_blend_epi16::<0b1_0_1_0_1_0_1_0>(products_left, products_right)
}
