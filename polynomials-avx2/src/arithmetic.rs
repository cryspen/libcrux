use crate::intrinsics::*;
use libcrux_traits::{FIELD_MODULUS, INVERSE_OF_MODULUS_MOD_MONTGOMERY_R};

#[inline(always)]
pub(crate) fn add(lhs: __m256i, rhs: __m256i) -> __m256i {
    mm256_add_epi16(lhs, rhs)
}

#[inline(always)]
pub(crate) fn sub(lhs: __m256i, rhs: __m256i) -> __m256i {
    mm256_sub_epi16(lhs, rhs)
}

#[inline(always)]
pub(crate) fn multiply_by_constant(vector: __m256i, constant: i16) -> __m256i {
    mm256_mullo_epi16(vector, mm256_set1_epi16(constant))
}

#[inline(always)]
pub(crate) fn bitwise_and_with_constant(vector: __m256i, constant: i16) -> __m256i {
    mm256_and_si256(vector, mm256_set1_epi16(constant))
}

#[inline(always)]
pub(crate) fn shift_right<const SHIFT_BY: i32>(vector: __m256i) -> __m256i {
    mm256_srai_epi16::<{ SHIFT_BY }>(vector)
}

#[inline(always)]
pub(crate) fn shift_left<const SHIFT_BY: i32>(vector: __m256i) -> __m256i {
    mm256_slli_epi16::<{ SHIFT_BY }>(vector)
}

#[inline(always)]
pub(crate) fn cond_subtract_3329(vector: __m256i) -> __m256i {
    let field_modulus = mm256_set1_epi16(FIELD_MODULUS);

    let v_minus_field_modulus = mm256_sub_epi16(vector, field_modulus);

    let sign_mask = mm256_srai_epi16::<15>(v_minus_field_modulus);
    let conditional_add_field_modulus = mm256_and_si256(sign_mask, field_modulus);

    mm256_add_epi16(v_minus_field_modulus, conditional_add_field_modulus)
}

const BARRETT_MULTIPLIER: i16 = 20159;

#[inline(always)]
pub(crate) fn barrett_reduce(vector: __m256i) -> __m256i {
    let t = mm256_mulhi_epi16(vector, mm256_set1_epi16(BARRETT_MULTIPLIER));
    let t = mm256_add_epi16(t, mm256_set1_epi16(512));

    let quotient = mm256_srai_epi16::<10>(t);

    let quotient_times_field_modulus = mm256_mullo_epi16(quotient, mm256_set1_epi16(FIELD_MODULUS));

    mm256_sub_epi16(vector, quotient_times_field_modulus)
}

#[inline(always)]
pub(crate) fn montgomery_multiply_by_constant(vector: __m256i, constant: i16) -> __m256i {
    let constant = mm256_set1_epi16(constant);
    let value_low = mm256_mullo_epi16(vector, constant);

    let k = mm256_mullo_epi16(
        value_low,
        mm256_set1_epi16(INVERSE_OF_MODULUS_MOD_MONTGOMERY_R as i16),
    );
    let k_times_modulus = mm256_mulhi_epi16(k, mm256_set1_epi16(FIELD_MODULUS));

    let value_high = mm256_mulhi_epi16(vector, constant);

    mm256_sub_epi16(value_high, k_times_modulus)
}
