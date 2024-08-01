use super::arithmetic;

use libcrux_intrinsics::avx2::*;

#[inline(always)]
pub fn ntt_at_layer_0(simd_unit: Vec256, zeta0: i32, zeta1: i32, zeta2: i32, zeta3: i32) -> Vec256 {
    let zetas = mm256_set_epi32(-zeta3, zeta3, -zeta2, zeta2, -zeta1, zeta1, -zeta0, zeta0);
    let zeta_multipliers = mm256_shuffle_epi32::<0b11_11_01_01>(simd_unit);

    let lhs = arithmetic::montgomery_multiply(zeta_multipliers, zetas);
    let rhs = mm256_shuffle_epi32::<0b10_10_00_00>(simd_unit);

    mm256_add_epi32(rhs, lhs)
}

#[inline(always)]
pub fn ntt_at_layer_1(simd_unit: Vec256, zeta0: i32, zeta1: i32) -> Vec256 {
    let zetas = mm256_set_epi32(-zeta1, -zeta1, zeta1, zeta1, -zeta0, -zeta0, zeta0, zeta0);
    let zeta_multipliers = mm256_shuffle_epi32::<0b11_10_11_10>(simd_unit);

    let rhs = arithmetic::montgomery_multiply(zeta_multipliers, zetas);
    let lhs = mm256_shuffle_epi32::<0b01_00_01_00>(simd_unit);

    mm256_add_epi32(rhs, lhs)
}

#[inline(always)]
pub fn ntt_at_layer_2(simd_unit: Vec256, zeta: i32) -> Vec256 {
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
