use super::arithmetic;
use crate::simd::traits::{
    COEFFICIENTS_IN_SIMD_UNIT, FIELD_MODULUS, INVERSE_OF_MODULUS_MOD_MONTGOMERY_R,
    SIMD_UNITS_IN_RING_ELEMENT,
};

use libcrux_intrinsics::avx2::*;

#[inline(always)]
pub fn ntt_montgomery_multiply_x2(
    lhs_1: Vec256,
    zetas_h_1: Vec256,
    zetas_l_1: Vec256,
    zetas_qinv_h_1: Vec256,
    zetas_qinv_l_1: Vec256,
    lhs_2: Vec256,
    zetas_h_2: Vec256,
    zetas_l_2: Vec256,
    zetas_qinv_h_2: Vec256,
    zetas_qinv_l_2: Vec256,
) -> (Vec256, Vec256) {
    let field_modulus = mm256_set1_epi32(FIELD_MODULUS);

    let prod02_qinv_1 = mm256_mul_epi32(zetas_qinv_l_1, lhs_1);
    let prod02_1 = mm256_mul_epi32(lhs_1, zetas_l_1);
    let prod02_qinv_2 = mm256_mul_epi32(zetas_qinv_l_2, lhs_2);
    let prod02_2 = mm256_mul_epi32(lhs_2, zetas_l_2);

    let lhs_h_1 = mm256_shuffle_epi32::<0b11_11_01_01>(lhs_1);
    let lhs_h_2 = mm256_shuffle_epi32::<0b11_11_01_01>(lhs_2);
    
    let prod13_qinv_1 = mm256_mul_epi32(zetas_qinv_h_1, lhs_h_1);
    let prod13_1 = mm256_mul_epi32(lhs_h_1, zetas_h_1);
    let prod13_qinv_2 = mm256_mul_epi32(zetas_qinv_h_2, lhs_h_2);
    let prod13_2 = mm256_mul_epi32(lhs_h_2, zetas_h_2);

    let c02_1 = mm256_mul_epi32(prod02_qinv_1, field_modulus);
    let c13_1 = mm256_mul_epi32(prod13_qinv_1, field_modulus);
    let c02_2 = mm256_mul_epi32(prod02_qinv_2, field_modulus);
    let c13_2 = mm256_mul_epi32(prod13_qinv_2, field_modulus);

    let res02_1 = mm256_sub_epi32(prod02_1, c02_1);
    let res13_1 = mm256_sub_epi32(prod13_1, c13_1);
    let res02_2 = mm256_sub_epi32(prod02_2, c02_2);
    let res13_2 = mm256_sub_epi32(prod13_2, c13_2);

    let res02_shifted_1 = mm256_shuffle_epi32::<0b11_11_01_01>(res02_1);
    let res02_shifted_2 = mm256_shuffle_epi32::<0b11_11_01_01>(res02_2);

    let res_1 = mm256_blend_epi32::<0b10101010>(res02_shifted_1, res13_1);
    let res_2 = mm256_blend_epi32::<0b10101010>(res02_shifted_2, res13_2);
    
    (res_1, res_2)
}

#[inline(always)]
pub fn ntt_montgomery_multiply(
    lhs: Vec256,
    zetas_h: Vec256,
    zetas_l: Vec256,
    zetas_qinv_h: Vec256,
    zetas_qinv_l: Vec256,
) -> Vec256 {
    let field_modulus = mm256_set1_epi32(FIELD_MODULUS);

    let prod02_qinv = mm256_mul_epi32(zetas_qinv_l, lhs);
    let prod02 = mm256_mul_epi32(lhs, zetas_l);

    let lhs_h = mm256_shuffle_epi32::<0b11_11_01_01>(lhs);
    let prod13_qinv = mm256_mul_epi32(zetas_qinv_h, lhs_h);
    let prod13 = mm256_mul_epi32(lhs_h, zetas_h);

    let c02 = mm256_mul_epi32(prod02_qinv, field_modulus);
    let c13 = mm256_mul_epi32(prod13_qinv, field_modulus);

    let res02 = mm256_sub_epi32(prod02, c02);
    let res13 = mm256_sub_epi32(prod13, c13);

    let res02_shifted = mm256_shuffle_epi32::<0b11_11_01_01>(res02);
    let res = mm256_blend_epi32::<0b10101010>(res02_shifted, res13);
    res
}

/// Shuffle two 256-bit vectors, to group low and high 128-bit lanes.
///
/// If the inputs are `a = (a_high, a_low)` and `b = (b_high, b_low)`,
/// the outputs are `(lows = (b_low, a_low), highs = (b_high, a_high))`.
#[inline(always)]
fn shuffle_2x128(a: Vec256, b: Vec256) -> (Vec256, Vec256) {
    let lows = mm256_permute2x128_si256::<0x20>(a, b);
    let highs = mm256_permute2x128_si256::<0x31>(a, b);

    (lows, highs)
}

/// Shuffle two 256-bit vectors, to interleave low and high
/// 64-bit integers of both lanes, respectively.
///
/// If the inputs are `a = (a3, a2, a1, a0)` and `b = (b3, b2, b1, b0)`,
/// the outputs are `(lows = (b2, a2, b0, a0), highs = (b3, a3, b1, a1))`.
#[inline(always)]
fn shuffle_4x64(a: Vec256, b: Vec256) -> (Vec256, Vec256) {
    let lows = mm256_unpacklo_epi64(a, b);
    let highs = mm256_unpackhi_epi64(a, b);

    (lows, highs)
}

/// Shuffle two 256-bit vectors, to interleave low and high
/// 32-bit integers of both lanes, respectively.
///
/// If the inputs are `a = (a7, a6, a5, a4, a3, a2, a1, a0)` and `b
/// = (b7, b6, b5, b4, b3, b2, b1, b0)`,
/// the outputs are `(lows = (b6, a6, b4, a4, b2, a2, b0, a0), highs =
/// (b7, a7, b5, a5, b3, a3, b1, a1))`.
#[inline(always)]
fn shuffle_8x32(a: Vec256, b: Vec256) -> (Vec256, Vec256) {
    let b_shifted = mm256_castps_si256(mm256_moveldup_ps(mm256_castsi256_ps(b)));
    let lows = mm256_blend_epi32::<0xAA>(a, b_shifted);

    let a_shifted = mm256_srli_epi64::<32>(a);
    let highs = mm256_blend_epi32::<0xAA>(a_shifted, b);

    (lows, highs)
}

/// Given a packed low zeta vector for a given round, precompute the
/// high zeta vector as well as low and high products with q⁻¹.
#[allow(unused)]
fn precompute_zetas(zetas_l: Vec256) {
    let inverse_of_modulus_mod_montgomery_r =
        mm256_set1_epi32(INVERSE_OF_MODULUS_MOD_MONTGOMERY_R as i32);

    let zetas_h = mm256_shuffle_epi32::<0b11_11_01_01>(zetas_l); // zetas_h

    let zetas_l_qinv = mm256_mul_epi32(inverse_of_modulus_mod_montgomery_r, zetas_l); // prod02_alt = zetas_l * qinv

    let zetas_h_qinv = mm256_mul_epi32(zetas_h, inverse_of_modulus_mod_montgomery_r); // prod13_alt = zetas_h * qinv

    let mut zetas_array = [0i32; 8];

    // mm256_storeu_si256_i32(&mut zetas_array, zetas_l);
    // mm256_storeu_si256_i32(&mut zetas_array, zetas_h);

    mm256_storeu_si256_i32(&mut zetas_array, zetas_l_qinv);
    mm256_storeu_si256_i32(&mut zetas_array, zetas_h_qinv);
}

/// Compute (a,b) ↦ (a + ζb, a - ζb).
#[inline(always)]
fn butterfly_x2(
    summands_1: Vec256,
    zeta_multiplicands_1: Vec256,
    zetas_h_1: Vec256,
    zetas_l_1: Vec256,
    zetas_qinv_h_1: Vec256,
    zetas_qinv_l_1: Vec256,
    summands_2: Vec256,
    zeta_multiplicands_2: Vec256,
    zetas_h_2: Vec256,
    zetas_l_2: Vec256,
    zetas_qinv_h_2: Vec256,
    zetas_qinv_l_2: Vec256,
) -> (Vec256, Vec256, Vec256, Vec256) {
    let (zeta_products_1, zeta_products_2) = ntt_montgomery_multiply_x2(
        zeta_multiplicands_1,
        zetas_h_1,
        zetas_l_1,
        zetas_qinv_h_1,
        zetas_qinv_l_1,
        zeta_multiplicands_2,
        zetas_h_2,
        zetas_l_2,
        zetas_qinv_h_2,
        zetas_qinv_l_2,
    );

    let addition_terms_1 = arithmetic::add(summands_1, zeta_products_1);
    let addition_terms_2 = arithmetic::add(summands_2, zeta_products_2);

    let subtraction_terms_1 = arithmetic::subtract(summands_1, zeta_products_1);
    let subtraction_terms_2 = arithmetic::subtract(summands_2, zeta_products_2);
    
    (addition_terms_1, subtraction_terms_1, addition_terms_2, subtraction_terms_2)
}

/// Compute (a,b) ↦ (a + ζb, a - ζb).
#[inline(always)]
fn butterfly(
    summands: Vec256,
    zeta_multiplicands: Vec256,
    zetas_h: Vec256,
    zetas_l: Vec256,
    zetas_qinv_h: Vec256,
    zetas_qinv_l: Vec256,
) -> (Vec256, Vec256) {
    let zeta_products = ntt_montgomery_multiply(
        zeta_multiplicands,
        zetas_h,
        zetas_l,
        zetas_qinv_h,
        zetas_qinv_l,
    );

    let addition_terms = arithmetic::add(summands, zeta_products);
    let subtraction_terms = arithmetic::subtract(summands, zeta_products);

    (addition_terms, subtraction_terms)
}

#[inline(always)]
fn butterfly_2(round: usize, a: Vec256, b: Vec256) -> (Vec256, Vec256) {
    let (summands, zeta_multiplicands) = shuffle_8x32(a, b);
    let zeta_index = zeta_round_index(0, round);

    let zetas_l = mm256_loadu_si256_i32(&ZETAS[zeta_index]);
    let zetas_h = mm256_loadu_si256_i32(&ZETAS[zeta_index + 1]);
    let zetas_qinv_l = mm256_loadu_si256_i32(&ZETAS_QINV[zeta_index]);
    let zetas_qinv_h = mm256_loadu_si256_i32(&ZETAS_QINV[zeta_index + 1]);

    let (add_terms, sub_terms) = butterfly(
        summands,
        zeta_multiplicands,
        zetas_h,
        zetas_l,
        zetas_qinv_h,
        zetas_qinv_l,
    );

    let (a_out, b_out) = shuffle_8x32(add_terms, sub_terms);

    (a_out, b_out)
}

// Compute (a,b) ↦ (a + ζb, a - ζb) at layer 1 for 2 SIMD Units in one go.
#[inline(always)]
fn butterfly_4(round: usize, a: Vec256, b: Vec256) -> (Vec256, Vec256) {
    let (summands, zeta_multiplicands) = shuffle_4x64(a, b);
    let zetas_l = mm256_loadu_si256_i32(&ZETAS[zeta_round_index(1, round)]);
    let zetas_qinv_l = mm256_loadu_si256_i32(&ZETAS_QINV[zeta_round_index(1, round)]);

    let zetas_h = zetas_l;
    let zetas_qinv_h = zetas_qinv_l;

    let (add_terms, sub_terms) = butterfly(
        summands,
        zeta_multiplicands,
        zetas_h,
        zetas_l,
        zetas_qinv_h,
        zetas_qinv_l,
    );

    shuffle_4x64(add_terms, sub_terms)
}

// Compute (a,b) ↦ (a + ζb, a - ζb) at layer 2 for 2 SIMD Units in one go.
#[inline(always)]
fn butterfly_8(round: usize, a: Vec256, b: Vec256) -> (Vec256, Vec256) {
    let (summands, zeta_multiplicands) = shuffle_2x128(a, b);
    let zetas_l = mm256_loadu_si256_i32(&ZETAS[zeta_round_index(2, round)]);
    let zetas_qinv_l = mm256_loadu_si256_i32(&ZETAS_QINV[zeta_round_index(2, round)]);

    let zetas_h = zetas_l;
    let zetas_qinv_h = zetas_qinv_l;

    let (add_terms, sub_terms) = butterfly(
        summands,
        zeta_multiplicands,
        zetas_h,
        zetas_l,
        zetas_qinv_h,
        zetas_qinv_l,
    );

    shuffle_2x128(add_terms, sub_terms)
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
        let (a, b) = butterfly_2(round, re[round], re[round + 1]);
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
        let (a, b) = butterfly_4(round, re[round], re[round + 1]);
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

        let (a, b) = butterfly_8(round, re[round], re[round + 1]);
        re[round] = a;
        re[round + 1] = b;

        *zeta_i += 1;
    }
}

/// Computes the offset in the precomputed Zeta tables of one (or, the
/// case of layer 0) two Zeta vectors to be used in the given round in
/// the given layer.
fn zeta_round_index(layer: usize, round: usize) -> usize {
    match layer {
        l @ 3..=7 => {
            // At layers 7 through 3, we have one zeta vector per round.
            debug_assert!(round < (1 << (7 - l)));
            zeta_layer_offset(layer) + round
        }
        2 | 1 => {
            // At layers 2 and 1, we have one zeta vector per two rounds.
            debug_assert!(round <= 32);
            zeta_layer_offset(layer) + round / 2
        }
        0 => {
            // At layers 0, we have two zeta vectors per two rounds.
            debug_assert!(round <= 32);
            zeta_layer_offset(layer) + round
        }
        _ => panic!(),
    }
}

/// Computes the offset in the precomputed tables of a Zetas belonging
/// to a given layer.
fn zeta_layer_offset(layer: usize) -> usize {
    debug_assert!(layer <= 7);
    // At layers 7 through 2, this is the zeta offset.
    let singleton_layer_offset = (1 << (7 - layer)) - 1;
    if layer >= 2 {
        singleton_layer_offset
    } else {
        // For layers 1 and 0, we have to correct for the grouping of
        // 2 and 4 zetas in one vector at layers 2 and 1,
        // respectively, i.e. the grouped zetas of layer 2 and layer 1
        // each contribute an increment of 16 to the offset, instead
        // of 32, or 64 respectively.
        let correction = 1 << (6 - 2 * layer);
        singleton_layer_offset - correction
    }
}

#[inline(always)]
fn ntt_at_layer_3_plus<const LAYER: usize>(re: &mut [Vec256; SIMD_UNITS_IN_RING_ELEMENT]) {
    let step = 1 << LAYER;

    for round in 0..(128 >> LAYER) {
        let offset = (round * step * 2) / COEFFICIENTS_IN_SIMD_UNIT;
        let step_by = step / COEFFICIENTS_IN_SIMD_UNIT;

        let zeta_index = zeta_round_index(LAYER, round);

        let zetas = ZETAS[zeta_index];
        let zetas_l = mm256_loadu_si256_i32(&zetas);
        let zetas_h = zetas_l;
        let zetas_l_qinv = ZETAS_QINV[zeta_index];
        let zetas_qinv_l = mm256_loadu_si256_i32(&zetas_l_qinv);
        let zetas_qinv_h = zetas_qinv_l;

        for j in offset..offset + step_by {
            let (add_terms, sub_terms) = butterfly(
                re[j],
                re[j + step_by],
                zetas_h,
                zetas_l,
                zetas_qinv_h,
                zetas_qinv_l,
            );
            re[j] = add_terms;
            re[j + step_by] = sub_terms;
        }
    }
}

#[inline(always)]
fn load_zetas(
    layer: usize,
    inner_round: usize,
    outer_round: usize,
) -> (Vec256, Vec256, Vec256, Vec256) {
    let multiplier = match layer {
        5 => 1,
        4 => 2,
        3 => 4,
        2 => 4,
        _ => panic!(),
    };
    let zeta_index = zeta_round_index(layer, outer_round * multiplier + inner_round);
    let zeta_index = if layer == 2 {
        zeta_index + outer_round * 2
    } else {
        zeta_index
    };

    let zetas = ZETAS[zeta_index];
    let zetas_l = mm256_loadu_si256_i32(&zetas);
    let zetas_h = zetas_l;
    let zetas_l_qinv = ZETAS_QINV[zeta_index];
    let zetas_qinv_l = mm256_loadu_si256_i32(&zetas_l_qinv);
    let zetas_qinv_h = zetas_qinv_l;
    (zetas_h, zetas_l, zetas_qinv_h, zetas_qinv_l)
}

#[inline(always)]
fn ntt_from_layer_5(re: &mut [Vec256; SIMD_UNITS_IN_RING_ELEMENT]) {
    macro_rules! butterfly {
        ($chunk:ident, $l:literal, $h:literal, $zetas_h:ident, $zetas_l:ident, $zetas_qinv_h:ident, $zetas_qinv_l:ident) => {
            ($chunk[$l], $chunk[$h]) = butterfly(
                $chunk[$l],
                $chunk[$h],
                $zetas_h,
                $zetas_l,
                $zetas_qinv_h,
                $zetas_qinv_l,
            );
        };
    }

    macro_rules! butterfly_x2_same {
        ($chunk:ident, $l_1:literal, $h_1:literal, $zetas_h_1:ident, $zetas_l_1:ident, $zetas_qinv_h_1:ident, $zetas_qinv_l_1:ident, $l_2:literal, $h_2:literal) => {
            ($chunk[$l_1], $chunk[$h_1], $chunk[$l_2], $chunk[$h_2]) = butterfly_x2(
                $chunk[$l_1],
                $chunk[$h_1],
                $zetas_h_1,
                $zetas_l_1,
                $zetas_qinv_h_1,
                $zetas_qinv_l_1,
                $chunk[$l_2],
                $chunk[$h_2],
                $zetas_h_1,
                $zetas_l_1,
                $zetas_qinv_h_1,
                $zetas_qinv_l_1,
            );
        };
    }

        macro_rules! butterfly_x2 {
            ($chunk:ident, $l_1:literal, $h_1:literal, $zetas_h_1:ident, $zetas_l_1:ident, $zetas_qinv_h_1:ident, $zetas_qinv_l_1:ident, $l_2:literal, $h_2:literal, $zetas_h_2:ident, $zetas_l_2:ident, $zetas_qinv_h_2:ident, $zetas_qinv_l_2:ident) => {
            ($chunk[$l_1], $chunk[$h_1], $chunk[$l_2], $chunk[$h_2]) = butterfly_x2(
                $chunk[$l_1],
                $chunk[$h_1],
                $zetas_h_1,
                $zetas_l_1,
                $zetas_qinv_h_1,
                $zetas_qinv_l_1,
                $chunk[$l_2],
                $chunk[$h_2],
                $zetas_h_2,
                $zetas_l_2,
                $zetas_qinv_h_2,
                $zetas_qinv_l_2,
            );
        };
    }
    
    for (layer_5_round, current_chunk) in re.chunks_exact_mut(8).enumerate() {
        let (zetas_h, zetas_l, zetas_qinv_h, zetas_qinv_l) = load_zetas(5, 0, layer_5_round);
        // butterfly!(
        //     current_chunk,
        //     0,
        //     4,
        //     zetas_h,
        //     zetas_l,
        //     zetas_qinv_h,
        //     zetas_qinv_l
        // );
        // butterfly!(
        //     current_chunk,
        //     1,
        //     5,
        //     zetas_h,
        //     zetas_l,
        //     zetas_qinv_h,
        //     zetas_qinv_l
        // );
        
        butterfly_x2_same!(
            current_chunk,
            0,
            4,
            zetas_h,
            zetas_l,
            zetas_qinv_h,
            zetas_qinv_l,
            1,
            5
        );
                
        // butterfly!(
        //     current_chunk,
        //     2,
        //     6,
        //     zetas_h,
        //     zetas_l,
        //     zetas_qinv_h,
        //     zetas_qinv_l
        // );
        // butterfly!(
        //     current_chunk,
        //     3,
        //     7,
        //     zetas_h,
        //     zetas_l,
        //     zetas_qinv_h,
        //     zetas_qinv_l
        // );
        
        butterfly_x2_same!(
            current_chunk,
            2,
            6,
            zetas_h,
            zetas_l,
            zetas_qinv_h,
            zetas_qinv_l,
            3,
            7
        );
        
        // layer 4
        let (zetas_h, zetas_l, zetas_qinv_h, zetas_qinv_l) = load_zetas(4, 0, layer_5_round);

        butterfly_x2_same!(
            current_chunk,
            0,
            2,
            zetas_h,
            zetas_l,
            zetas_qinv_h,
            zetas_qinv_l,
            1,
            3
        );
        
        // butterfly!(
        //     current_chunk,
        //     0,
        //     2,
        //     zetas_h,
        //     zetas_l,
        //     zetas_qinv_h,
        //     zetas_qinv_l
        // );
        // butterfly!(
        //     current_chunk,
        //     1,
        //     3,
        //     zetas_h,
        //     zetas_l,
        //     zetas_qinv_h,
        //     zetas_qinv_l
        // );

        let (zetas_h, zetas_l, zetas_qinv_h, zetas_qinv_l) = load_zetas(4, 1, layer_5_round);

        butterfly_x2_same!(
            current_chunk,
            4,
            6,
            zetas_h,
            zetas_l,
            zetas_qinv_h,
            zetas_qinv_l,
            5,
            7
        );
        
        // butterfly!(
        //     current_chunk,
        //     4,
        //     6,
        //     zetas_h,
        //     zetas_l,
        //     zetas_qinv_h,
        //     zetas_qinv_l
        // );
        // butterfly!(
        //     current_chunk,
        //     5,
        //     7,
        //     zetas_h,
        //     zetas_l,
        //     zetas_qinv_h,
        //     zetas_qinv_l
        // );

        // layer 3
        let (zetas_h_1, zetas_l_1, zetas_qinv_h_1, zetas_qinv_l_1) = load_zetas(3, 0, layer_5_round);
        let (zetas_h_2, zetas_l_2, zetas_qinv_h_2, zetas_qinv_l_2) = load_zetas(3, 1, layer_5_round);

        butterfly_x2!(
            current_chunk,
            0,
            1,
            zetas_h_1,
            zetas_l_1,
            zetas_qinv_h_1,
            zetas_qinv_l_1,
            2,
            3,
            zetas_h_2,
            zetas_l_2,
            zetas_qinv_h_2,
            zetas_qinv_l_2
        );

        // butterfly!(
        //     current_chunk,
        //     0,
        //     1,
        //     zetas_h_1,
        //     zetas_l_1,
        //     zetas_qinv_h_1,
        //     zetas_qinv_l_1
        // );

        // butterfly!(
        //     current_chunk,
        //     2,
        //     3,
        //     zetas_h_2,
        //     zetas_l_2,
        //     zetas_qinv_h_2,
        //     zetas_qinv_l_2
        // );

        let (zetas_h_1, zetas_l_1, zetas_qinv_h_1, zetas_qinv_l_1) = load_zetas(3, 2, layer_5_round);
        let (zetas_h_2, zetas_l_2, zetas_qinv_h_2, zetas_qinv_l_2) = load_zetas(3, 3, layer_5_round);


        butterfly_x2!(
            current_chunk,
            4,
            5,
            zetas_h_1,
            zetas_l_1,
            zetas_qinv_h_1,
            zetas_qinv_l_1,
            6,
            7,
            zetas_h_2,
            zetas_l_2,
            zetas_qinv_h_2,
            zetas_qinv_l_2
        );
        
        // butterfly!(
        //     current_chunk,
        //     4,
        //     5,
        //     zetas_h_1,
        //     zetas_l_1,
        //     zetas_qinv_h_1,
        //     zetas_qinv_l_1
        // );


        // butterfly!(
        //     current_chunk,
        //     6,
        //     7,
        //     zetas_h_2,
        //     zetas_l_2,
        //     zetas_qinv_h_2,
        //     zetas_qinv_l_2
        // );
        // TODO: Remaining layers
    }
}

#[inline(always)]
pub(crate) fn ntt(
    mut re: [Vec256; SIMD_UNITS_IN_RING_ELEMENT],
) -> [Vec256; SIMD_UNITS_IN_RING_ELEMENT] {
    let mut zeta_i = 0;
    ntt_at_layer_3_plus::<7>(&mut re);
    ntt_at_layer_3_plus::<6>(&mut re);
    ntt_from_layer_5(&mut re); // 5 + 4 + 3 in one
    ntt_at_layer_2(&mut zeta_i, &mut re);
    ntt_at_layer_1(&mut zeta_i, &mut re);
    ntt_at_layer_0(&mut zeta_i, &mut re);

    re
}

#[test]
fn shuffle8() {
    let a = mm256_set_epi32(07, 06, 05, 04, 03, 02, 01, 00);
    let b = mm256_set_epi32(15, 14, 13, 12, 11, 10, 09, 08);

    let expected_lows = [00, 08, 02, 10, 04, 12, 06, 14];
    let expected_highs = [01, 09, 03, 11, 05, 13, 07, 15];

    let (computed_lows, computed_highs) = shuffle_8x32(a, b);

    let mut array_low = [0; 8];
    let mut array_high = [0; 8];
    mm256_storeu_si256_i32(&mut array_low, computed_lows);
    mm256_storeu_si256_i32(&mut array_high, computed_highs);

    assert_eq!(array_low, expected_lows, "low 32-bit integers differ");
    assert_eq!(array_high, expected_highs, "high 32-bit integers differ");
}

/// Precomputed table of ζ vectors for all rounds in all layers.
const ZETAS: [[i32; 8]; 95] = [
    [25847, 25847, 25847, 25847, 25847, 25847, 25847, 25847],
    [
        -2608894, -2608894, -2608894, -2608894, -2608894, -2608894, -2608894, -2608894,
    ],
    [
        -518909, -518909, -518909, -518909, -518909, -518909, -518909, -518909,
    ],
    [
        237124, 237124, 237124, 237124, 237124, 237124, 237124, 237124,
    ],
    [
        -777960, -777960, -777960, -777960, -777960, -777960, -777960, -777960,
    ],
    [
        -876248, -876248, -876248, -876248, -876248, -876248, -876248, -876248,
    ],
    [
        466468, 466468, 466468, 466468, 466468, 466468, 466468, 466468,
    ],
    [
        1826347, 1826347, 1826347, 1826347, 1826347, 1826347, 1826347, 1826347,
    ],
    [
        2353451, 2353451, 2353451, 2353451, 2353451, 2353451, 2353451, 2353451,
    ],
    [
        -359251, -359251, -359251, -359251, -359251, -359251, -359251, -359251,
    ],
    [
        -2091905, -2091905, -2091905, -2091905, -2091905, -2091905, -2091905, -2091905,
    ],
    [
        3119733, 3119733, 3119733, 3119733, 3119733, 3119733, 3119733, 3119733,
    ],
    [
        -2884855, -2884855, -2884855, -2884855, -2884855, -2884855, -2884855, -2884855,
    ],
    [
        3111497, 3111497, 3111497, 3111497, 3111497, 3111497, 3111497, 3111497,
    ],
    [
        2680103, 2680103, 2680103, 2680103, 2680103, 2680103, 2680103, 2680103,
    ],
    [
        2725464, 2725464, 2725464, 2725464, 2725464, 2725464, 2725464, 2725464,
    ],
    [
        1024112, 1024112, 1024112, 1024112, 1024112, 1024112, 1024112, 1024112,
    ],
    [
        -1079900, -1079900, -1079900, -1079900, -1079900, -1079900, -1079900, -1079900,
    ],
    [
        3585928, 3585928, 3585928, 3585928, 3585928, 3585928, 3585928, 3585928,
    ],
    [
        -549488, -549488, -549488, -549488, -549488, -549488, -549488, -549488,
    ],
    [
        -1119584, -1119584, -1119584, -1119584, -1119584, -1119584, -1119584, -1119584,
    ],
    [
        2619752, 2619752, 2619752, 2619752, 2619752, 2619752, 2619752, 2619752,
    ],
    [
        -2108549, -2108549, -2108549, -2108549, -2108549, -2108549, -2108549, -2108549,
    ],
    [
        -2118186, -2118186, -2118186, -2118186, -2118186, -2118186, -2118186, -2118186,
    ],
    [
        -3859737, -3859737, -3859737, -3859737, -3859737, -3859737, -3859737, -3859737,
    ],
    [
        -1399561, -1399561, -1399561, -1399561, -1399561, -1399561, -1399561, -1399561,
    ],
    [
        -3277672, -3277672, -3277672, -3277672, -3277672, -3277672, -3277672, -3277672,
    ],
    [
        1757237, 1757237, 1757237, 1757237, 1757237, 1757237, 1757237, 1757237,
    ],
    [
        -19422, -19422, -19422, -19422, -19422, -19422, -19422, -19422,
    ],
    [
        4010497, 4010497, 4010497, 4010497, 4010497, 4010497, 4010497, 4010497,
    ],
    [
        280005, 280005, 280005, 280005, 280005, 280005, 280005, 280005,
    ],
    [
        2706023, 2706023, 2706023, 2706023, 95776, 95776, 95776, 95776,
    ],
    [
        3077325, 3077325, 3077325, 3077325, 3530437, 3530437, 3530437, 3530437,
    ],
    [
        -1661693, -1661693, -1661693, -1661693, -3592148, -3592148, -3592148, -3592148,
    ],
    [
        -2537516, -2537516, -2537516, -2537516, 3915439, 3915439, 3915439, 3915439,
    ],
    [
        -3861115, -3861115, -3861115, -3861115, -3043716, -3043716, -3043716, -3043716,
    ],
    [
        3574422, 3574422, 3574422, 3574422, -2867647, -2867647, -2867647, -2867647,
    ],
    [
        3539968, 3539968, 3539968, 3539968, -300467, -300467, -300467, -300467,
    ],
    [
        2348700, 2348700, 2348700, 2348700, -539299, -539299, -539299, -539299,
    ],
    [
        -1699267, -1699267, -1699267, -1699267, -1643818, -1643818, -1643818, -1643818,
    ],
    [
        3505694, 3505694, 3505694, 3505694, -3821735, -3821735, -3821735, -3821735,
    ],
    [
        3507263, 3507263, 3507263, 3507263, -2140649, -2140649, -2140649, -2140649,
    ],
    [
        -1600420, -1600420, -1600420, -1600420, 3699596, 3699596, 3699596, 3699596,
    ],
    [
        811944, 811944, 811944, 811944, 531354, 531354, 531354, 531354,
    ],
    [
        954230, 954230, 954230, 954230, 3881043, 3881043, 3881043, 3881043,
    ],
    [
        3900724, 3900724, 3900724, 3900724, -2556880, -2556880, -2556880, -2556880,
    ],
    [
        2071892, 2071892, 2071892, 2071892, -2797779, -2797779, -2797779, -2797779,
    ],
    [
        -3930395, -3930395, -3677745, -3677745, -1528703, -1528703, -3041255, -3041255,
    ],
    [
        -1452451, -1452451, 2176455, 2176455, 3475950, 3475950, -1585221, -1585221,
    ],
    [
        -1257611, -1257611, -4083598, -4083598, 1939314, 1939314, -1000202, -1000202,
    ],
    [
        -3190144, -3190144, -3632928, -3632928, -3157330, -3157330, 126922, 126922,
    ],
    [
        3412210, 3412210, 2147896, 2147896, -983419, -983419, 2715295, 2715295,
    ],
    [
        -2967645, -2967645, -411027, -411027, -3693493, -3693493, -2477047, -2477047,
    ],
    [
        -671102, -671102, -22981, -22981, -1228525, -1228525, -1308169, -1308169,
    ],
    [
        -381987, -381987, 1852771, 1852771, 1349076, 1349076, -1430430, -1430430,
    ],
    [
        -3343383, -3343383, 508951, 508951, 264944, 264944, 3097992, 3097992,
    ],
    [
        44288, 44288, 904516, 904516, -1100098, -1100098, 3958618, 3958618,
    ],
    [
        -3724342, -3724342, 1653064, 1653064, -8578, -8578, -3249728, -3249728,
    ],
    [
        2389356, 2389356, 759969, 759969, -210977, -210977, -1316856, -1316856,
    ],
    [
        189548, 189548, 3159746, 3159746, -3553272, -3553272, -1851402, -1851402,
    ],
    [
        -2409325, -2409325, 1315589, 1315589, -177440, -177440, 1341330, 1341330,
    ],
    [
        1285669, 1285669, -812732, -812732, -1584928, -1584928, -1439742, -1439742,
    ],
    [
        -3019102, -3019102, -3628969, -3628969, -3881060, -3881060, 3839961, 3839961,
    ],
    [
        2091667, -3342478, 3407706, 2244091, 2316500, -2446433, 3817976, -3562462,
    ],
    [
        -3342478, -3342478, 2244091, 2244091, -2446433, -2446433, -3562462, -3562462,
    ],
    [
        266997, -3520352, 2434439, -3759364, -1235728, -1197226, 3513181, -3193378,
    ],
    [
        -3520352, -3520352, -3759364, -3759364, -1197226, -1197226, -3193378, -3193378,
    ],
    [
        900702, 495491, 1859098, -1613174, 909542, -43260, 819034, -522500,
    ],
    [
        495491, 495491, -1613174, -1613174, -43260, -43260, -522500, -522500,
    ],
    [
        -655327, -3556995, -3122442, -525098, 2031748, -768622, 3207046, -3595838,
    ],
    [
        -3556995, -3556995, -525098, -525098, -768622, -768622, -3595838, -3595838,
    ],
    [
        342297, 3437287, 286988, -3342277, -2437823, 1735879, 4108315, 203044,
    ],
    [
        3437287, 3437287, -3342277, -3342277, 1735879, 1735879, 203044, 203044,
    ],
    [
        2842341, 4055324, 2691481, 1247620, -2590150, 2486353, 1265009, 1595974,
    ],
    [
        4055324, 4055324, 1247620, 1247620, 2486353, 2486353, 1595974, 1595974,
    ],
    [
        -3767016, -2994039, 1250494, 1869119, 2635921, 1903435, -3548272, -1050970,
    ],
    [
        -2994039, -2994039, 1869119, 1869119, 1903435, 1903435, -1050970, -1050970,
    ],
    [
        -1333058, -451100, 1237275, 1312455, -3318210, 3306115, -1430225, -1962642,
    ],
    [
        -451100, -451100, 1312455, 1312455, 3306115, 3306115, -1962642, -1962642,
    ],
    [
        -1279661, 1500165, 1917081, 777191, -2546312, 2235880, -1374803, 3406031,
    ],
    [
        1500165, 1500165, 777191, 777191, 2235880, 2235880, 3406031, 3406031,
    ],
    [
        -542412, -2584293, -2831860, -3724270, -1671176, 594136, -1846953, -3776993,
    ],
    [
        -2584293, -2584293, -3724270, -3724270, 594136, 594136, -3776993, -3776993,
    ],
    [
        -2013608, 1957272, 2432395, 3369112, 2454455, 185531, -164721, -1207385,
    ],
    [
        1957272, 1957272, 3369112, 3369112, 185531, 185531, -1207385, -1207385,
    ],
    [
        -3183426, 810149, 162844, 1652634, 1616392, -3694233, 3014001, -1799107,
    ],
    [
        810149, 810149, 1652634, 1652634, -3694233, -3694233, -1799107, -1799107,
    ],
    [
        -3038916, 2213111, 3523897, -975884, 3866901, 1717735, 269760, 472078,
    ],
    [
        2213111, 2213111, -975884, -975884, 1717735, 1717735, 472078, 472078,
    ],
    [
        -426683, -1667432, 1723600, -1104333, -1803090, -260646, 1910376, -3833893,
    ],
    [
        -1667432, -1667432, -1104333, -1104333, -260646, -260646, -3833893, -3833893,
    ],
    [
        -2939036, 183443, -2235985, -976891, -420899, 1612842, -2286327, -3545687,
    ],
    [
        183443, 183443, -976891, -976891, 1612842, 1612842, -3545687, -3545687,
    ],
    [
        -554416, 3937738, 3919660, 1400424, -48306, -846154, -1362209, 1976782,
    ],
    [
        3937738, 3937738, 1400424, 1400424, -846154, -846154, 1976782, 1976782,
    ],
];

/// Precomputed table of ζ * q⁻¹ vectors for all rounds in all layers.
const ZETAS_QINV: [[i32; 8]; 95] = [
    [
        1830765815, 353, 1830765815, 353, 1830765815, 353, 1830765815, 353,
    ],
    [
        -1929875198,
        -35674,
        -1929875198,
        -35674,
        -1929875198,
        -35674,
        -1929875198,
        -35674,
    ],
    [
        -1927777021,
        -7096,
        -1927777021,
        -7096,
        -1927777021,
        -7096,
        -1927777021,
        -7096,
    ],
    [
        1640767044, 3242, 1640767044, 3242, 1640767044, 3242, 1640767044, 3242,
    ],
    [
        1477910808, -10638, 1477910808, -10638, 1477910808, -10638, 1477910808, -10638,
    ],
    [
        1612161320, -11982, 1612161320, -11982, 1612161320, -11982, 1612161320, -11982,
    ],
    [
        1640734244, 6378, 1640734244, 6378, 1640734244, 6378, 1640734244, 6378,
    ],
    [
        308362795, 24973, 308362795, 24973, 308362795, 24973, 308362795, 24973,
    ],
    [
        -1815525077,
        32180,
        -1815525077,
        32180,
        -1815525077,
        32180,
        -1815525077,
        32180,
    ],
    [
        -1374673747,
        -4913,
        -1374673747,
        -4913,
        -1374673747,
        -4913,
        -1374673747,
        -4913,
    ],
    [
        -1091570561,
        -28605,
        -1091570561,
        -28605,
        -1091570561,
        -28605,
        -1091570561,
        -28605,
    ],
    [
        -1929495947,
        42658,
        -1929495947,
        42658,
        -1929495947,
        42658,
        -1929495947,
        42658,
    ],
    [
        515185417, -39447, 515185417, -39447, 515185417, -39447, 515185417, -39447,
    ],
    [
        -285697463, 42545, -285697463, 42545, -285697463, 42545, -285697463, 42545,
    ],
    [
        625853735, 36647, 625853735, 36647, 625853735, 36647, 625853735, 36647,
    ],
    [
        1727305304, 37267, 1727305304, 37267, 1727305304, 37267, 1727305304, 37267,
    ],
    [
        2082316400, 14003, 2082316400, 14003, 2082316400, 14003, 2082316400, 14003,
    ],
    [
        -1364982364,
        -14767,
        -1364982364,
        -14767,
        -1364982364,
        -14767,
        -1364982364,
        -14767,
    ],
    [
        858240904, 49033, 858240904, 49033, 858240904, 49033, 858240904, 49033,
    ],
    [
        1806278032, -7514, 1806278032, -7514, 1806278032, -7514, 1806278032, -7514,
    ],
    [
        222489248, -15309, 222489248, -15309, 222489248, -15309, 222489248, -15309,
    ],
    [
        -346752664, 35821, -346752664, 35821, -346752664, 35821, -346752664, 35821,
    ],
    [
        684667771, -28832, 684667771, -28832, 684667771, -28832, 684667771, -28832,
    ],
    [
        1654287830, -28964, 1654287830, -28964, 1654287830, -28964, 1654287830, -28964,
    ],
    [
        -878576921, -52778, -878576921, -52778, -878576921, -52778, -878576921, -52778,
    ],
    [
        -1257667337,
        -19138,
        -1257667337,
        -19138,
        -1257667337,
        -19138,
        -1257667337,
        -19138,
    ],
    [
        -748618600, -44819, -748618600, -44819, -748618600, -44819, -748618600, -44819,
    ],
    [
        329347125, 24028, 329347125, 24028, 329347125, 24028, 329347125, 24028,
    ],
    [
        1837364258, -266, 1837364258, -266, 1837364258, -266, 1837364258, -266,
    ],
    [
        -1443016191,
        54838,
        -1443016191,
        54838,
        -1443016191,
        54838,
        -1443016191,
        54838,
    ],
    [
        -1170414139,
        3828,
        -1170414139,
        3828,
        -1170414139,
        3828,
        -1170414139,
        3828,
    ],
    [
        -1846138265,
        37001,
        -1846138265,
        37001,
        -1631226336,
        1309,
        -1631226336,
        1309,
    ],
    [
        -1404529459,
        42078,
        -1404529459,
        42078,
        1838055109,
        48274,
        1838055109,
        48274,
    ],
    [
        1594295555,
        -22722,
        1594295555,
        -22722,
        -1076973524,
        -49119,
        -1076973524,
        -49119,
    ],
    [
        -1898723372,
        -34698,
        -1898723372,
        -34698,
        -594436433,
        53538,
        -594436433,
        53538,
    ],
    [
        -202001019, -52797, -202001019, -52797, -475984260, -41620, -475984260, -41620,
    ],
    [
        -561427818, 48875, -561427818, 48875, 1797021249, -39212, 1797021249, -39212,
    ],
    [
        -1061813248,
        48404,
        -1061813248,
        48404,
        2059733581,
        -4109,
        2059733581,
        -4109,
    ],
    [
        -1661512036,
        32115,
        -1661512036,
        32115,
        -1104976547,
        -7375,
        -1104976547,
        -7375,
    ],
    [
        -1750224323,
        -23236,
        -1750224323,
        -23236,
        -901666090,
        -22478,
        -901666090,
        -22478,
    ],
    [
        418987550, 47936, 418987550, 47936, 1831915353, -52258, 1831915353, -52258,
    ],
    [
        -1925356481,
        47957,
        -1925356481,
        47957,
        992097815,
        -29271,
        992097815,
        -29271,
    ],
    [
        879957084, -21884, 879957084, -21884, 2024403852, 50587, 2024403852, 50587,
    ],
    [
        1484874664,
        11102,
        1484874664,
        11102,
        -1636082790,
        7265,
        -1636082790,
        7265,
    ],
    [
        -285388938,
        13047,
        -285388938,
        13047,
        -1983539117,
        53068,
        -1983539117,
        53068,
    ],
    [
        -1495136972,
        53337,
        -1495136972,
        53337,
        -950076368,
        -34963,
        -950076368,
        -34963,
    ],
    [
        -1714807468,
        28330,
        -1714807468,
        28330,
        -952438995,
        -38257,
        -952438995,
        -38257,
    ],
    [
        -1574918427,
        -53744,
        1350681039,
        -50289,
        -654783359,
        -20904,
        -1974159335,
        -41586,
    ],
    [
        -2143979939,
        -19861,
        1599739335,
        29760,
        1651689966,
        47529,
        140455867,
        -21676,
    ],
    [
        -1285853323,
        -17197,
        -993005454,
        -55839,
        -1039411342,
        26517,
        1955560694,
        -13677,
    ],
    [
        -1440787840,
        -43622,
        568627424,
        -49676,
        1529189038,
        -43173,
        -2131021878,
        1735,
    ],
    [
        -783134478, 46657, -588790216, 29369, -247357819, -13448, 1518161567, 37128,
    ],
    [
        289871779,
        -40579,
        -1262003603,
        -5621,
        -86965173,
        -50505,
        1708872713,
        -33871,
    ],
    [
        2135294594,
        -9177,
        -1018755525,
        -315,
        1787797779,
        -16799,
        1638590967,
        -17888,
    ],
    [
        -889861155,
        -5224,
        1665705315,
        25334,
        -120646188,
        18446,
        -1669960606,
        -19560,
    ],
    [
        1321868265, -45717, 1225434135, 6959, -916321552, 3622, 1155548552, 42361,
    ],
    [
        -1784632064,
        605,
        666258756,
        12368,
        2143745726,
        -15043,
        1210558298,
        54129,
    ],
    [
        675310538,
        -50926,
        -1555941048,
        22603,
        -1261461890,
        -118,
        -318346816,
        -44437,
    ],
    [
        -1999506068,
        32671,
        -1499481951,
        10391,
        628664287,
        -2885,
        -1729304568,
        -18007,
    ],
    [
        -695180180,
        2591,
        -1375177022,
        43205,
        1422575624,
        -48587,
        1424130038,
        -25316,
    ],
    [
        1777179795,
        -32945,
        334803717,
        17989,
        -1185330464,
        -2427,
        235321234,
        18341,
    ],
    [
        -178766299, 17579, -518252220, -11114, 168022240, -21672, 1206536194, -19687,
    ],
    [
        1957047970, -41283, 1146323031, -49622, 985155484, -53069, -894060583, 52506,
    ],
    [
        -898413, 28600, 991903578, 46596, 1363007700, 31675, 746144248, 52206,
    ],
    [
        -1363460238,
        -45705,
        912367099,
        30685,
        30313375,
        -33452,
        -1420958686,
        -48713,
    ],
    [
        -605900043, 3650, -44694137, 33287, -326425360, -16898, 2032221021, 48038,
    ],
    [
        2027833504, -48137, 1176904444, -51405, 1683520342, -16371, 1904936414, -43666,
    ],
    [
        14253662, 12316, -421552614, 25420, -517299994, 12436, 1257750362, 11199,
    ],
    [
        1014493059, 6775, -818371958, -22059, 2027935492, -592, 1926727420, -7145,
    ],
    [
        863641633,
        -8961,
        1747917558,
        -42696,
        -1372618620,
        27781,
        1931587462,
        43852,
    ],
    [
        1819892093, -48638, -325927722, -7181, 128353682, -10510, 1258381762, -49169,
    ],
    [
        2124962073,
        4680,
        908452108,
        3924,
        -1123881663,
        -33335,
        885133339,
        56176,
    ],
    [
        -1223601433,
        47000,
        1851023419,
        -45702,
        137583815,
        23736,
        1629985060,
        2776,
    ],
    [
        -1920467227,
        38865,
        -1176751719,
        36802,
        -635454918,
        -35418,
        1967222129,
        17297,
    ],
    [
        -1637785316,
        55451,
        -1354528380,
        17059,
        -642772911,
        33997,
        6363718,
        21823,
    ],
    [
        -1536588520,
        -51510,
        -72690498,
        17098,
        45766801,
        36043,
        -1287922800,
        -48519,
    ],
    [
        694382729, -40940, -314284737, 25557, 671509323, 26027, 1136965286, -14371,
    ],
    [
        235104446,
        -18228,
        985022747,
        16918,
        -2070602178,
        -45373,
        1779436847,
        -19557,
    ],
    [
        -1045062172,
        -6169,
        963438279,
        17946,
        419615363,
        45207,
        1116720494,
        -26837,
    ],
    [
        831969619,
        -17498,
        -1078959975,
        26213,
        1216882040,
        -34818,
        1042326957,
        -18799,
    ],
    [
        -300448763, 20512, 604552167, 10627, -270590488, 30572, 1405999311, 46573,
    ],
    [
        756955444,
        -7417,
        -1021949428,
        -38723,
        -1276805128,
        -22852,
        713994583,
        -25255,
    ],
    [
        -260312805, -35338, 608791570, -50925, 371462360, 8124, 940195359, -51646,
    ],
    [
        1554794072,
        -27534,
        173440395,
        33260,
        -1357098057,
        33561,
        -1542497137,
        -2253,
    ],
    [
        1339088280,
        26763,
        -2126092136,
        46068,
        -384158533,
        2536,
        2061661095,
        -16510,
    ],
    [
        -2040058690,
        -43530,
        -1316619236,
        2226,
        827959816,
        22102,
        -883155599,
        41212,
    ],
    [
        -853476187,
        11077,
        -1039370342,
        22597,
        -596344473,
        -50515,
        1726753853,
        -24601,
    ],
    [
        -2047270596,
        -41554,
        6087993,
        48185,
        702390549,
        52875,
        -1547952704,
        3688,
    ],
    [
        -1723816713,
        30261,
        -110126092,
        -13345,
        -279505433,
        23487,
        394851342,
        6455,
    ],
    [
        -1591599803,
        -5835,
        565464272,
        23568,
        -260424530,
        -24656,
        283780712,
        26122,
    ],
    [
        -440824168,
        -22801,
        -1758099917,
        -15101,
        -71875110,
        -3565,
        776003547,
        -52424,
    ],
    [
        1119856484,
        -40188,
        -1600929361,
        -30575,
        -1208667171,
        -5756,
        1123958025,
        -31263,
    ],
    [
        1544891539,
        2508,
        879867909,
        -13358,
        -1499603926,
        22053,
        201262505,
        -48483,
    ],
    [
        155290192,
        -7581,
        -1809756372,
        53596,
        2036925262,
        -661,
        1934038751,
        -18627,
    ],
    [
        -973777462, 53843, 400711272, 19149, -540420426, -11571, 374860238, 27030,
    ],
];
