use crate::simd::traits::{FIELD_MODULUS, INVERSE_OF_MODULUS_MOD_MONTGOMERY_R};

use libcrux_intrinsics::avx2::*;

#[inline(always)]
pub fn add(lhs: Vec256, rhs: Vec256) -> Vec256 {
    mm256_add_epi32(lhs, rhs)
}

#[inline(always)]
pub fn subtract(lhs: Vec256, rhs: Vec256) -> Vec256 {
    mm256_sub_epi32(lhs, rhs)
}

// Multiply two vectors of 32-bit integers and return two vectors containing
// the high 32 bits of each of the pairwise products.
fn simd_multiply_i32_and_return_high(lhs: Vec256, rhs: Vec256) -> Vec256 {
    let prod02 = mm256_mul_epi32(lhs, rhs);
    let prod13 = mm256_mul_epi32(
        mm256_shuffle_epi32::<0b11_11_01_01>(lhs),
        mm256_shuffle_epi32::<0b11_11_01_01>(rhs),
    );

    mm256_unpackhi_epi64(
        mm256_unpacklo_epi32(prod02, prod13),
        mm256_unpackhi_epi32(prod02, prod13),
    )
}

#[inline(always)]
pub fn montgomery_multiply_by_constant(simd_unit: Vec256, constant: i32) -> Vec256 {
    let constant = mm256_set1_epi32(constant);
    let field_modulus = mm256_set1_epi32(FIELD_MODULUS);
    let inverse_of_modulus_mod_montgomery_r =
        mm256_set1_epi32(INVERSE_OF_MODULUS_MOD_MONTGOMERY_R as i32);

    let product_low = mm256_mullo_epi32(simd_unit, constant);

    let k = mm256_mullo_epi32(product_low, inverse_of_modulus_mod_montgomery_r);

    let c = simd_multiply_i32_and_return_high(k, field_modulus);
    let product_high = simd_multiply_i32_and_return_high(simd_unit, constant);

    mm256_sub_epi32(product_high, c)
}

#[inline(always)]
pub fn montgomery_multiply(lhs: Vec256, rhs: Vec256) -> Vec256 {
    let field_modulus = mm256_set1_epi32(FIELD_MODULUS);
    let inverse_of_modulus_mod_montgomery_r =
        mm256_set1_epi32(INVERSE_OF_MODULUS_MOD_MONTGOMERY_R as i32);

    let product_low = mm256_mullo_epi32(lhs, rhs);

    let k = mm256_mullo_epi32(product_low, inverse_of_modulus_mod_montgomery_r);

    let c = simd_multiply_i32_and_return_high(k, field_modulus);
    let product_high = simd_multiply_i32_and_return_high(lhs, rhs);

    mm256_sub_epi32(product_high, c)
}

#[inline(always)]
pub fn shift_left_then_reduce(simd_unit: Vec256, shift_by: usize) -> Vec256 {
    // TODO: Shift using slli
    let shift_by = mm256_set1_epi32(shift_by as i32);
    let shifted = mm256_sllv_epi32(simd_unit, shift_by);

    let quotient = mm256_add_epi32(shifted, mm256_set1_epi32(1 << 22));
    let quotient = mm256_srai_epi32::<23>(quotient);

    let quotient_times_field_modulus =
        mm256_mullo_epi32(quotient, mm256_set1_epi32(FIELD_MODULUS as i32));

    mm256_sub_epi32(shifted, quotient_times_field_modulus)
}
