use crate::vector::{traits::INVERSE_OF_MODULUS_MOD_MONTGOMERY_R, FIELD_MODULUS};

use super::*;

#[inline(always)]
pub(crate) fn add(lhs: Vec256, rhs: Vec256) -> Vec256 {
    mm256_add_epi16(lhs, rhs)
}

#[inline(always)]
pub(crate) fn sub(lhs: Vec256, rhs: Vec256) -> Vec256 {
    mm256_sub_epi16(lhs, rhs)
}

#[inline(always)]
pub(crate) fn multiply_by_constant(vector: Vec256, constant: i16) -> Vec256 {
    mm256_mullo_epi16(vector, mm256_set1_epi16(constant))
}

#[inline(always)]
pub(crate) fn bitwise_and_with_constant(vector: Vec256, constant: i16) -> Vec256 {
    mm256_and_si256(vector, mm256_set1_epi16(constant))
}

#[inline(always)]
pub(crate) fn shift_right<const SHIFT_BY: i32>(vector: Vec256) -> Vec256 {
    mm256_srai_epi16::<{ SHIFT_BY }>(vector)
}

// #[inline(always)]
// pub(crate) fn shift_left<const SHIFT_BY: i32>(vector: Vec256) -> Vec256 {
//     mm256_slli_epi16::<{ SHIFT_BY }>(vector)
// }

#[inline(always)]
pub(crate) fn cond_subtract_3329(vector: Vec256) -> Vec256 {
    let field_modulus = mm256_set1_epi16(FIELD_MODULUS);

    // Compute v_i - Q and crate a mask from the sign bit of each of these
    // quantities.
    let v_minus_field_modulus = mm256_sub_epi16(vector, field_modulus);
    let sign_mask = mm256_srai_epi16::<15>(v_minus_field_modulus);

    // If v_i - Q < 0 then add back Q to (v_i - Q).
    let conditional_add_field_modulus = mm256_and_si256(sign_mask, field_modulus);
    mm256_add_epi16(v_minus_field_modulus, conditional_add_field_modulus)
}

const BARRETT_MULTIPLIER: i16 = 20159;

/// See Section 3.2 of the implementation notes document for an explanation
/// of this code.
#[inline(always)]
pub(crate) fn barrett_reduce(vector: Vec256) -> Vec256 {
    let t = mm256_mulhi_epi16(vector, mm256_set1_epi16(BARRETT_MULTIPLIER));
    let t = mm256_add_epi16(t, mm256_set1_epi16(512));

    let quotient = mm256_srai_epi16::<10>(t);

    let quotient_times_field_modulus = mm256_mullo_epi16(quotient, mm256_set1_epi16(FIELD_MODULUS));

    mm256_sub_epi16(vector, quotient_times_field_modulus)
}

#[inline(always)]
pub(crate) fn montgomery_multiply_by_constant(vector: Vec256, constant: i16) -> Vec256 {
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

#[inline(always)]
pub(crate) fn montgomery_multiply_by_constants(v: Vec256, c: Vec256) -> Vec256 {
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
pub(crate) fn montgomery_reduce_i32s(v: Vec256) -> Vec256 {
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
pub(crate) fn montgomery_multiply_m128i_by_constants(v: Vec128, c: Vec128) -> Vec128 {
    let value_low = mm_mullo_epi16(v, c);

    let k = mm_mullo_epi16(
        value_low,
        mm_set1_epi16(INVERSE_OF_MODULUS_MOD_MONTGOMERY_R as i16),
    );
    let k_times_modulus = mm_mulhi_epi16(k, mm_set1_epi16(FIELD_MODULUS));

    let value_high = mm_mulhi_epi16(v, c);

    mm_sub_epi16(value_high, k_times_modulus)
}
