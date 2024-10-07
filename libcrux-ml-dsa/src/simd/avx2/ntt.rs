use super::arithmetic;
use crate::simd::traits::{
    COEFFICIENTS_IN_SIMD_UNIT, SIMD_UNITS_IN_RING_ELEMENT, ZETAS_TIMES_MONTGOMERY_R,
};

use libcrux_intrinsics::avx2::*;

#[inline(always)]
fn butterfly_2(
    a: Vec256,
    b: Vec256,
    zeta_a0: i32,
    zeta_a1: i32,
    zeta_a2: i32,
    zeta_a3: i32,
    zeta_b0: i32,
    zeta_b1: i32,
    zeta_b2: i32,
    zeta_b3: i32,
) -> (Vec256, Vec256) {
    // We shuffle the terms to group those that need to be multiplied
    // with zetas in the high QWORDS of the vectors, i.e. if the inputs are
    //   a = (a7, a6, a5, a4, a3, a2, a1, a0)
    //   b = (b7, b6, b5, b4, b3, b2, b1, b0)
    // after shuffling we have
    //   a_shuffled = ( a7, a5, a6, a4, a3, a1, a2, a0)
    //   b_shuffled = ( b7, b5, b6, b4, b3, b1, b2, b0)
    const SHUFFLE: i32 = 0b11_01_10_00;
    let a_shuffled = mm256_shuffle_epi32::<SHUFFLE>(a);
    let b_shuffled = mm256_shuffle_epi32::<SHUFFLE>(b);

    // Now we can use the same approach as for `butterfly_4`, only
    // zetas need to be adjusted.
    let summands = mm256_unpacklo_epi64(a_shuffled, b_shuffled);
    let zeta_multiplicands = mm256_unpackhi_epi64(a_shuffled, b_shuffled);
    let zetas = mm256_set_epi32(
        zeta_b3, zeta_b2, zeta_a3, zeta_a2, zeta_b1, zeta_b0, zeta_a1, zeta_a0,
    );

    let zeta_products = arithmetic::montgomery_multiply(zeta_multiplicands, zetas);

    let add_terms = arithmetic::add(summands, zeta_products);
    let sub_terms = arithmetic::subtract(summands, zeta_products);

    let a_terms_shuffled = mm256_unpacklo_epi64(add_terms, sub_terms);
    let b_terms_shuffled = mm256_unpackhi_epi64(add_terms, sub_terms);

    // Here, we undo the initial shuffle (it's self-inverse).
    let a_out = mm256_shuffle_epi32::<SHUFFLE>(a_terms_shuffled);
    let b_out = mm256_shuffle_epi32::<SHUFFLE>(b_terms_shuffled);

    (a_out, b_out)
}

// Compute (a,b) ↦ (a + ζb, a - ζb) at layer 1 for 2 SIMD Units in one go.
#[inline(always)]
fn butterfly_4(
    a: Vec256,
    b: Vec256,
    zeta_a0: i32,
    zeta_a1: i32,
    zeta_b0: i32,
    zeta_b1: i32,
) -> (Vec256, Vec256) {
    let summands = mm256_unpacklo_epi64(a, b);
    let zeta_multiplicands = mm256_unpackhi_epi64(a, b);

    let zetas = mm256_set_epi32(
        zeta_b1, zeta_b1, zeta_a1, zeta_a1, zeta_b0, zeta_b0, zeta_a0, zeta_a0,
    );
    let zeta_products = arithmetic::montgomery_multiply(zeta_multiplicands, zetas);

    let add_terms = arithmetic::add(summands, zeta_products);
    let sub_terms = arithmetic::subtract(summands, zeta_products);

    // Results are shuffled across the two SIMD registers.
    // We need to bring them in the right order.
    let a_out = mm256_unpacklo_epi64(add_terms, sub_terms);
    let b_out = mm256_unpackhi_epi64(add_terms, sub_terms);

    (a_out, b_out)
}

// Compute (a,b) ↦ (a + ζb, a - ζb) at layer 2 for 2 SIMD Units in one go.
#[inline(always)]
fn butterfly_8(a: Vec256, b: Vec256, zeta0: i32, zeta1: i32) -> (Vec256, Vec256) {
    let summands = mm256_set_m128i(mm256_castsi256_si128(b), mm256_castsi256_si128(a));
    let zeta_multiplicands = mm256_permute2x128_si256::<0b0001_0011>(b, a);

    let zetas = mm256_set_epi32(zeta1, zeta1, zeta1, zeta1, zeta0, zeta0, zeta0, zeta0);
    let zeta_products = arithmetic::montgomery_multiply(zeta_multiplicands, zetas);

    let add_terms = arithmetic::add(summands, zeta_products);
    let sub_terms = arithmetic::subtract(summands, zeta_products);

    let a_out = mm256_set_m128i(
        mm256_castsi256_si128(sub_terms),
        mm256_castsi256_si128(add_terms),
    );
    let b_out = mm256_permute2x128_si256::<0b0001_0011>(sub_terms, add_terms);

    (a_out, b_out)
}

#[inline(always)]
pub fn invert_ntt_at_layer_0(
    simd_unit: Vec256,
    zeta0: i32,
    zeta1: i32,
    zeta2: i32,
    zeta3: i32,
) -> Vec256 {
    let zetas = mm256_set_epi32(zeta3, 0, zeta2, 0, zeta1, 0, zeta0, 0);

    let add_by_signs = mm256_set_epi32(-1, 1, -1, 1, -1, 1, -1, 1);
    let add_by = mm256_shuffle_epi32::<0b10_11_00_01>(simd_unit);
    let add_by = mm256_mullo_epi32(add_by, add_by_signs);

    let sums = mm256_add_epi32(simd_unit, add_by);

    let products = arithmetic::montgomery_multiply(sums, zetas);

    mm256_blend_epi32::<0b1_0_1_0_1_0_1_0>(sums, products)
}

#[inline(always)]
fn ntt_at_layer_0(zeta_i: &mut usize, re: &mut [Vec256; SIMD_UNITS_IN_RING_ELEMENT]) {
    *zeta_i += 1;
    for round in (0..re.len()).step_by(2) {
        let (a, b) = butterfly_2(
            re[round],
            re[round + 1],
            ZETAS_TIMES_MONTGOMERY_R[*zeta_i],
            ZETAS_TIMES_MONTGOMERY_R[*zeta_i + 1],
            ZETAS_TIMES_MONTGOMERY_R[*zeta_i + 2],
            ZETAS_TIMES_MONTGOMERY_R[*zeta_i + 3],
            ZETAS_TIMES_MONTGOMERY_R[*zeta_i + 4],
            ZETAS_TIMES_MONTGOMERY_R[*zeta_i + 5],
            ZETAS_TIMES_MONTGOMERY_R[*zeta_i + 6],
            ZETAS_TIMES_MONTGOMERY_R[*zeta_i + 7],
        );
        re[round] = a;
        re[round + 1] = b;

        *zeta_i += 8;
    }

    *zeta_i -= 1;
}

#[inline(always)]
pub fn invert_ntt_at_layer_1(simd_unit: Vec256, zeta0: i32, zeta1: i32) -> Vec256 {
    let zetas = mm256_set_epi32(zeta1, zeta1, 0, 0, zeta0, zeta0, 0, 0);

    let add_by_signs = mm256_set_epi32(-1, -1, 1, 1, -1, -1, 1, 1);
    let add_by = mm256_shuffle_epi32::<0b01_00_11_10>(simd_unit);
    let add_by = mm256_mullo_epi32(add_by, add_by_signs);

    let sums = mm256_add_epi32(simd_unit, add_by);

    let products = arithmetic::montgomery_multiply(sums, zetas);

    mm256_blend_epi32::<0b1_1_0_0_1_1_0_0>(sums, products)
}

#[inline(always)]
fn ntt_at_layer_1(zeta_i: &mut usize, re: &mut [Vec256; SIMD_UNITS_IN_RING_ELEMENT]) {
    *zeta_i += 1;
    for round in (0..re.len()).step_by(2) {
        let (a, b) = butterfly_4(
            re[round],
            re[round + 1],
            ZETAS_TIMES_MONTGOMERY_R[*zeta_i],
            ZETAS_TIMES_MONTGOMERY_R[*zeta_i + 1],
            ZETAS_TIMES_MONTGOMERY_R[*zeta_i + 2],
            ZETAS_TIMES_MONTGOMERY_R[*zeta_i + 3],
        );
        re[round] = a;
        re[round + 1] = b;

        *zeta_i += 4;
    }

    *zeta_i -= 1;
}

#[inline(always)]
pub fn invert_ntt_at_layer_2(simd_unit: Vec256, zeta: i32) -> Vec256 {
    let zetas = mm256_set_epi32(zeta, zeta, zeta, zeta, 0, 0, 0, 0);

    let add_by_signs = mm256_set_epi32(-1, -1, -1, -1, 1, 1, 1, 1);
    let add_by = mm256_permute4x64_epi64::<0b01_00_11_10>(simd_unit);
    let add_by = mm256_mullo_epi32(add_by, add_by_signs);

    let sums = mm256_add_epi32(simd_unit, add_by);

    let products = arithmetic::montgomery_multiply(sums, zetas);

    mm256_blend_epi32::<0b1_1_1_1_0_0_0_0>(sums, products)
}

#[inline(always)]
fn ntt_at_layer_2(zeta_i: &mut usize, re: &mut [Vec256; SIMD_UNITS_IN_RING_ELEMENT]) {
    for round in (0..re.len()).step_by(2) {
        *zeta_i += 1;
        let (a, b) = butterfly_8(
            re[round],
            re[round + 1],
            ZETAS_TIMES_MONTGOMERY_R[*zeta_i],
            ZETAS_TIMES_MONTGOMERY_R[*zeta_i + 1],
        );
        re[round] = a;
        re[round + 1] = b;

        *zeta_i += 1;
    }
}

#[inline(always)]
fn ntt_at_layer_3_plus<const LAYER: usize>(
    zeta_i: &mut usize,
    re: &mut [Vec256; SIMD_UNITS_IN_RING_ELEMENT],
) {
    let step = 1 << LAYER;

    for round in 0..(128 >> LAYER) {
        *zeta_i += 1;

        let offset = (round * step * 2) / COEFFICIENTS_IN_SIMD_UNIT;
        let step_by = step / COEFFICIENTS_IN_SIMD_UNIT;

        for j in offset..offset + step_by {
            let t = arithmetic::montgomery_multiply_by_constant(
                re[j + step_by],
                ZETAS_TIMES_MONTGOMERY_R[*zeta_i],
            );

            re[j + step_by] = arithmetic::subtract(re[j], t);
            re[j] = arithmetic::add(re[j], t);
        }
    }
}

#[inline(always)]
pub(crate) fn ntt(
    mut re: [Vec256; SIMD_UNITS_IN_RING_ELEMENT],
) -> [Vec256; SIMD_UNITS_IN_RING_ELEMENT] {
    let mut zeta_i = 0;
    ntt_at_layer_3_plus::<7>(&mut zeta_i, &mut re);
    ntt_at_layer_3_plus::<6>(&mut zeta_i, &mut re);
    ntt_at_layer_3_plus::<5>(&mut zeta_i, &mut re);
    ntt_at_layer_3_plus::<4>(&mut zeta_i, &mut re);
    ntt_at_layer_3_plus::<3>(&mut zeta_i, &mut re);
    ntt_at_layer_2(&mut zeta_i, &mut re);
    ntt_at_layer_1(&mut zeta_i, &mut re);
    ntt_at_layer_0(&mut zeta_i, &mut re);

    re
}
