#[cfg(target_arch = "x86")]
use core::arch::x86::*;
#[cfg(target_arch = "x86_64")]
use core::arch::x86_64::*;

use crate::SIMD256Vector;
use libcrux_traits::{FIELD_MODULUS, INVERSE_OF_MODULUS_MOD_MONTGOMERY_R};

#[inline(always)]
pub(crate) fn add(mut lhs: SIMD256Vector, rhs: &SIMD256Vector) -> SIMD256Vector {
    lhs.elements = unsafe { _mm256_add_epi16(lhs.elements, rhs.elements) };

    lhs
}

#[inline(always)]
pub(crate) fn sub(mut lhs: SIMD256Vector, rhs: &SIMD256Vector) -> SIMD256Vector {
    lhs.elements = unsafe { _mm256_sub_epi16(lhs.elements, rhs.elements) };

    lhs
}

#[inline(always)]
pub(crate) fn multiply_by_constant(mut v: SIMD256Vector, c: i16) -> SIMD256Vector {
    v.elements = unsafe {
        let c = _mm256_set1_epi16(c);

        _mm256_mullo_epi16(v.elements, c)
    };

    v
}

#[inline(always)]
pub(crate) fn bitwise_and_with_constant(mut v: SIMD256Vector, c: i16) -> SIMD256Vector {
    v.elements = unsafe {
        let c = _mm256_set1_epi16(c);

        _mm256_and_si256(v.elements, c)
    };

    v
}

#[inline(always)]
pub(crate) fn shift_right<const SHIFT_BY: i32>(mut v: SIMD256Vector) -> SIMD256Vector {
    v.elements = unsafe { _mm256_srai_epi16(v.elements, SHIFT_BY) };

    v
}

#[inline(always)]
pub(crate) fn shift_left<const SHIFT_BY: i32>(mut v: SIMD256Vector) -> SIMD256Vector {
    v.elements = unsafe { _mm256_slli_epi16(v.elements, SHIFT_BY) };

    v
}

#[inline(always)]
pub(crate) fn cond_subtract_3329(mut v: SIMD256Vector) -> SIMD256Vector {
    v.elements = unsafe {
        let field_modulus = _mm256_set1_epi16(FIELD_MODULUS);

        let v_minus_field_modulus = _mm256_sub_epi16(v.elements, field_modulus);

        let sign_mask = _mm256_srai_epi16(v_minus_field_modulus, 15);
        let conditional_add_field_modulus = _mm256_and_si256(sign_mask, field_modulus);

        _mm256_add_epi16(v_minus_field_modulus, conditional_add_field_modulus)
    };

    v
}

const BARRETT_MULTIPLIER: i16 = 20159;

#[inline(always)]
pub(crate) fn barrett_reduce(mut v: SIMD256Vector) -> SIMD256Vector {
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
pub(crate) fn montgomery_multiply_by_constant(mut v: SIMD256Vector, c: i16) -> SIMD256Vector {
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
