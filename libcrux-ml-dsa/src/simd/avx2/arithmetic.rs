use crate::{
    constants::BITS_IN_LOWER_PART_OF_T,
    simd::traits::{FIELD_MODULUS, INVERSE_OF_MODULUS_MOD_MONTGOMERY_R},
};

use libcrux_intrinsics::avx2::*;

fn to_unsigned_representatives(t: Vec256) -> Vec256 {
    let signs = mm256_srai_epi32::<31>(t);
    let conditional_add_field_modulus = mm256_and_si256(signs, mm256_set1_epi32(FIELD_MODULUS));

    mm256_add_epi32(t, conditional_add_field_modulus)
}

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
pub fn shift_left_then_reduce<const SHIFT_BY: i32>(simd_unit: Vec256) -> Vec256 {
    let shifted = mm256_slli_epi32::<SHIFT_BY>(simd_unit);

    let quotient = mm256_add_epi32(shifted, mm256_set1_epi32(1 << 22));
    let quotient = mm256_srai_epi32::<23>(quotient);

    let quotient_times_field_modulus =
        mm256_mullo_epi32(quotient, mm256_set1_epi32(FIELD_MODULUS as i32));

    mm256_sub_epi32(shifted, quotient_times_field_modulus)
}

// TODO: Revisit this function when doing the range analysis and testing
// additional KATs.
#[inline(always)]
pub fn infinity_norm_exceeds(simd_unit: Vec256, bound: i32) -> bool {
    let absolute_values = mm256_abs_epi32(simd_unit);

    // We will test if |simd_unit| > bound - 1, because if this is the case then
    // it follows that |simd_unit| >= bound
    let bound = mm256_set1_epi32(bound - 1);

    let compare_with_bound = mm256_cmpgt_epi32(absolute_values, bound);

    // If every lane of |result| is 0, all coefficients are <= bound - 1
    let result = mm256_testz_si256(compare_with_bound, compare_with_bound);

    if result == 1 {
        false
    } else {
        true
    }
}

#[inline(always)]
pub fn power2round(r: Vec256) -> (Vec256, Vec256) {
    let r = to_unsigned_representatives(r);

    let r1 = mm256_add_epi32(
        r,
        mm256_set1_epi32((1 << (BITS_IN_LOWER_PART_OF_T - 1)) - 1),
    );
    let r1 = mm256_srai_epi32::<{ BITS_IN_LOWER_PART_OF_T as i32 }>(r1);

    let r0 = mm256_slli_epi32::<{ BITS_IN_LOWER_PART_OF_T as i32 }>(r1);
    let r0 = mm256_sub_epi32(r, r0);

    (r0, r1)
}

#[allow(non_snake_case)]
#[inline(always)]
pub fn decompose<const GAMMA2: i32>(r: Vec256) -> (Vec256, Vec256) {
    let r = to_unsigned_representatives(r);

    let field_modulus_halved = mm256_set1_epi32((FIELD_MODULUS - 1) / 2);

    // When const-generic expressions are table, this could be turned into a
    // const value.
    let ALPHA: i32 = GAMMA2 * 2;

    let r1 = {
        let ceil_of_r_by_128 = mm256_add_epi32(r, mm256_set1_epi32(127));
        let ceil_of_r_by_128 = mm256_srai_epi32::<7>(ceil_of_r_by_128);

        match ALPHA {
            190_464 => {
                // We approximate 1 / 1488 as:
                // ⌊2²⁴ / 1488⌋ / 2²⁴ = 11,275 / 2²⁴
                let result = mm256_mullo_epi32(ceil_of_r_by_128, mm256_set1_epi32(11_275));
                let result = mm256_add_epi32(result, mm256_set1_epi32(1 << 23));
                let result = mm256_srai_epi32::<24>(result);

                // For the corner-case a₁ = (q-1)/α = 44, we have to set a₁=0.
                let mask = mm256_sub_epi32(mm256_set1_epi32(43), result);
                let mask = mm256_srai_epi32::<31>(mask);

                let not_result = mm256_xor_si256(result, mask);

                mm256_and_si256(result, not_result)
            }

            523_776 => {
                // We approximate 1 / 4092 as:
                // ⌊2²² / 4092⌋ / 2²² = 1025 / 2²²
                let result = mm256_mullo_epi32(ceil_of_r_by_128, mm256_set1_epi32(1025));
                let result = mm256_add_epi32(result, mm256_set1_epi32(1 << 21));
                let result = mm256_srai_epi32::<22>(result);

                // For the corner-case a₁ = (q-1)/α = 16, we have to set a₁=0.
                mm256_and_si256(result, mm256_set1_epi32(15))
            }

            _ => unreachable!(),
        }
    };

    // In the corner-case, when we set a₁=0, we will incorrectly
    // have a₀ > (q-1)/2 and we'll need to subtract q.  As we
    // return a₀ + q, that comes down to adding q if a₀ < (q-1)/2.
    let r0 = mm256_mullo_epi32(r1, mm256_set1_epi32(ALPHA));
    let r0 = mm256_sub_epi32(r, r0);

    let mask = mm256_sub_epi32(field_modulus_halved, r0);
    let mask = mm256_srai_epi32::<31>(mask);

    let field_modulus_and_mask = mm256_and_si256(mask, mm256_set1_epi32(FIELD_MODULUS));

    let r0 = mm256_sub_epi32(r0, field_modulus_and_mask);

    (r0, r1)
}
