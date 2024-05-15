#[cfg(target_arch = "x86")]
use core::arch::x86::*;
#[cfg(target_arch = "x86_64")]
use core::arch::x86_64::*;

use libcrux_traits::{FIELD_MODULUS, INVERSE_OF_MODULUS_MOD_MONTGOMERY_R};

#[inline(always)]
pub(crate) fn add(mut lhs: __m256i, rhs: __m256i) -> __m256i {
    lhs = unsafe { _mm256_add_epi16(lhs, rhs) };

    lhs
}

#[inline(always)]
pub(crate) fn sub(mut lhs: __m256i, rhs: __m256i) -> __m256i {
    lhs = unsafe { _mm256_sub_epi16(lhs, rhs) };

    lhs
}

#[inline(always)]
pub(crate) fn multiply_by_constant(mut vector: __m256i, constant: i16) -> __m256i {
    vector = unsafe { _mm256_mullo_epi16(vector, _mm256_set1_epi16(constant)) };

    vector
}

#[inline(always)]
pub(crate) fn bitwise_and_with_constant(mut vector: __m256i, constant: i16) -> __m256i {
    vector = unsafe { _mm256_and_si256(vector, _mm256_set1_epi16(constant)) };

    vector
}

#[inline(always)]
pub(crate) fn shift_right<const SHIFT_BY: i32>(mut vector: __m256i) -> __m256i {
    vector = unsafe { _mm256_srai_epi16(vector, SHIFT_BY) };

    vector
}

#[inline(always)]
pub(crate) fn shift_left<const SHIFT_BY: i32>(mut vector: __m256i) -> __m256i {
    vector = unsafe { _mm256_slli_epi16(vector, SHIFT_BY) };

    vector
}

#[inline(always)]
pub(crate) fn cond_subtract_3329(mut vector: __m256i) -> __m256i {
    vector = unsafe {
        let field_modulus = _mm256_set1_epi16(FIELD_MODULUS);

        let v_minus_field_modulus = _mm256_sub_epi16(vector, field_modulus);

        let sign_mask = _mm256_srai_epi16(v_minus_field_modulus, 15);
        let conditional_add_field_modulus = _mm256_and_si256(sign_mask, field_modulus);

        _mm256_add_epi16(v_minus_field_modulus, conditional_add_field_modulus)
    };

    vector
}

const BARRETT_MULTIPLIER: i16 = 20159;

#[inline(always)]
pub(crate) fn barrett_reduce(mut vector: __m256i) -> __m256i {
    vector = unsafe {
        let t = _mm256_mulhi_epi16(vector, _mm256_set1_epi16(BARRETT_MULTIPLIER));
        let t = _mm256_add_epi16(t, _mm256_set1_epi16(512));

        let quotient = _mm256_srai_epi16(t, 10);

        let quotient_times_field_modulus =
            _mm256_mullo_epi16(quotient, _mm256_set1_epi16(FIELD_MODULUS));

        _mm256_sub_epi16(vector, quotient_times_field_modulus)
    };

    vector
}

#[inline(always)]
pub(crate) fn montgomery_multiply_by_constant(mut vector: __m256i, constant: i16) -> __m256i {
    vector = unsafe {
        let constant = _mm256_set1_epi16(constant);
        let value_low = _mm256_mullo_epi16(vector, constant);

        let k = _mm256_mullo_epi16(
            value_low,
            _mm256_set1_epi16(INVERSE_OF_MODULUS_MOD_MONTGOMERY_R as i16),
        );
        let k_times_modulus = _mm256_mulhi_epi16(k, _mm256_set1_epi16(FIELD_MODULUS));

        let value_high = _mm256_mulhi_epi16(vector, constant);

        _mm256_sub_epi16(value_high, k_times_modulus)
    };

    vector
}
