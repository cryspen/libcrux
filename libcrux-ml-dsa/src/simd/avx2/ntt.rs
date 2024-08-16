use super::arithmetic;
use crate::simd::{
    traits::{COEFFICIENTS_IN_SIMD_UNIT, SIMD_UNITS_IN_RING_ELEMENT, ZETAS_TIMES_MONTGOMERY_R},
};

use libcrux_intrinsics::avx2::*;

#[inline(always)]
pub fn simd_unit_ntt_at_layer_0(simd_unit: Vec256, zeta0: i32, zeta1: i32, zeta2: i32, zeta3: i32) -> Vec256 {
    let zetas = mm256_set_epi32(-zeta3, zeta3, -zeta2, zeta2, -zeta1, zeta1, -zeta0, zeta0);
    let zeta_multipliers = mm256_shuffle_epi32::<0b11_11_01_01>(simd_unit);

    let lhs = arithmetic::montgomery_multiply(zeta_multipliers, zetas);
    let rhs = mm256_shuffle_epi32::<0b10_10_00_00>(simd_unit);

    mm256_add_epi32(rhs, lhs)
}

#[inline(always)]
pub fn simd_unit_ntt_at_layer_1(simd_unit: Vec256, zeta0: i32, zeta1: i32) -> Vec256 {
    let zetas = mm256_set_epi32(-zeta1, -zeta1, zeta1, zeta1, -zeta0, -zeta0, zeta0, zeta0);
    let zeta_multipliers = mm256_shuffle_epi32::<0b11_10_11_10>(simd_unit);

    let rhs = arithmetic::montgomery_multiply(zeta_multipliers, zetas);
    let lhs = mm256_shuffle_epi32::<0b01_00_01_00>(simd_unit);

    mm256_add_epi32(rhs, lhs)
}

#[inline(always)]
pub fn simd_unit_ntt_at_layer_2(simd_unit: Vec256, zeta: i32) -> Vec256 {
    let zetas = mm256_set_epi32(-zeta, -zeta, -zeta, -zeta, zeta, zeta, zeta, zeta);
    let zeta_multipliers = mm256_permute4x64_epi64::<0b11_10_11_10>(simd_unit);

    let rhs = arithmetic::montgomery_multiply(zeta_multipliers, zetas);
    let lhs = mm256_permute4x64_epi64::<0b01_00_01_00>(simd_unit);

    mm256_add_epi32(rhs, lhs)
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
fn ntt_at_layer_0(zeta_i: &mut usize, re: &mut [Vec256; SIMD_UNITS_IN_RING_ELEMENT]) {
    *zeta_i += 1;

    for round in 0..re.len() {
        re[round] = simd_unit_ntt_at_layer_0(
            re[round],
            ZETAS_TIMES_MONTGOMERY_R[*zeta_i],
            ZETAS_TIMES_MONTGOMERY_R[*zeta_i + 1],
            ZETAS_TIMES_MONTGOMERY_R[*zeta_i + 2],
            ZETAS_TIMES_MONTGOMERY_R[*zeta_i + 3],
        );

        *zeta_i += 4;
    }

    *zeta_i -= 1;
}
#[inline(always)]
fn ntt_at_layer_1(zeta_i: &mut usize, re: &mut [Vec256; SIMD_UNITS_IN_RING_ELEMENT]) {
    *zeta_i += 1;

    for round in 0..re.len() {
        re[round] = simd_unit_ntt_at_layer_1(
            re[round],
            ZETAS_TIMES_MONTGOMERY_R[*zeta_i],
            ZETAS_TIMES_MONTGOMERY_R[*zeta_i + 1],
        );

        *zeta_i += 2;
    }

    *zeta_i -= 1;
}

// Compute (a,b) ↦ (a + ζb, a - ζb).
fn butterfly_8(a0: Vec256, b0: Vec256, zeta0: i32, zeta1: i32) -> (Vec256, Vec256) {
    let a = mm256_set_m128i(mm256_castsi256_si128(b0), mm256_castsi256_si128(a0));
    let b = mm256_set_m128i(mm256_extracti128_si256::<1>(b0), mm256_extracti128_si256::<1>(a0));

    let zetas = mm256_set_epi32(zeta1, zeta1, zeta1, zeta1, zeta0, zeta0, zeta0, zeta0);
    let t = arithmetic::montgomery_multiply(b, zetas);

    let out0 = arithmetic::add(a, t);
    let out1 = arithmetic::subtract(a, t);

    let sout0 = mm256_set_m128i(mm256_castsi256_si128(out1), mm256_castsi256_si128(out0));
    let sout1 = mm256_set_m128i(mm256_extracti128_si256::<1>(out1), mm256_extracti128_si256::<1>(out0));

    (sout0, sout1)
}
#[inline(always)]
fn ntt_at_layer_2(zeta_i: &mut usize, re: &mut [Vec256; SIMD_UNITS_IN_RING_ELEMENT]) {
    for round in (0..re.len()).step_by(2) {
        *zeta_i += 1;
        let (a, b) = butterfly_8(re[round], re[round + 1], ZETAS_TIMES_MONTGOMERY_R[*zeta_i], ZETAS_TIMES_MONTGOMERY_R[*zeta_i + 1]);
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
            let t = arithmetic::montgomery_multiply_by_constant(re[j + step_by], ZETAS_TIMES_MONTGOMERY_R[*zeta_i]);

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
