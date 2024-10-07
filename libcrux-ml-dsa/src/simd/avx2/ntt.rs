use super::arithmetic;
use crate::simd::traits::{
    COEFFICIENTS_IN_SIMD_UNIT, FIELD_MODULUS, INVERSE_OF_MODULUS_MOD_MONTGOMERY_R,
    SIMD_UNITS_IN_RING_ELEMENT, ZETAS_TIMES_MONTGOMERY_R,
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
    // std::println!("butterfly_2");
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
    // std::println!("butterfly_4");
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
    // std::println!("butterfly_8");
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

// XXX: NTT experiments
// montgomery_multiply is called for 65 in layer 3-7:
// (note that this is calling into the ntt many times!)
// - key gen: 2400
// - sign:    6320
// - verify:  2960
//
// pqclean ntt
// 4 * levels0t1 (0 1 2 3)
//   - 4 * butterfly @ level 0
//   - 4 * butterfly @ level 1
// 4 * levels2t7 (0 1 2 3)
//   - 4 * butterfly @ level 2 + 4 * shuffle4
//   - 4 * butterfly @ level 3 + 4 * shuffle2
//   - 4 * butterfly @ level 5
//   - 4 * butterfly @ level 6
//   - 4 * butterfly @ level 7
//
// In both versions, each multiply/butterfly has 6 multiplications (mm256_mul_epi32) each
//
// Multiplications in sign
// libcrux: 768 | montogmery: 128
// pqclean: 672 | montogmery: 112

/// This is equivalent to the pqclean 0 and 1
///
/// This does 32 montgomery multiplications (192 multiplications).
/// This is the same as in pqclean. The only difference is locality of registers.
#[inline(always)]
fn ntt_at_layer_7_and_6(zeta_i: &mut usize, re: &mut [Vec256; SIMD_UNITS_IN_RING_ELEMENT]) {
    // std::println!("7&6");
    let field_modulus = mm256_set1_epi32(FIELD_MODULUS);
    let inverse_of_modulus_mod_montgomery_r =
        mm256_set1_epi32(INVERSE_OF_MODULUS_MOD_MONTGOMERY_R as i32);

    macro_rules! mul {
        ($i:expr, $zeta:expr, $step_by:expr) => {
            // std::eprintln!("mull");
            let prod02 = mm256_mul_epi32(re[$i + $step_by], $zeta);
            let prod13 = mm256_mul_epi32(
                mm256_shuffle_epi32::<0b11_11_01_01>(re[$i + $step_by]), // 0xF5
                mm256_shuffle_epi32::<0b11_11_01_01>($zeta),             // 0xF5
            );
            let k02 = mm256_mul_epi32(prod02, inverse_of_modulus_mod_montgomery_r);
            let k13 = mm256_mul_epi32(prod13, inverse_of_modulus_mod_montgomery_r);

            let c02 = mm256_mul_epi32(k02, field_modulus);
            let c13 = mm256_mul_epi32(k13, field_modulus);

            let res02 = mm256_sub_epi32(prod02, c02);
            let res13 = mm256_sub_epi32(prod13, c13);
            let res02_shifted = mm256_shuffle_epi32::<0b11_11_01_01>(res02); // 0xF5
            let t = mm256_blend_epi32::<0b10101010>(res02_shifted, res13); // 0xAA

            re[$i + $step_by] = arithmetic::subtract(re[$i], t);
            re[$i] = arithmetic::add(re[$i], t);
        };
    }

    macro_rules! layer {
        ($start:literal, $zeta:expr, $step_by:expr) => {{
            mul!($start, $zeta, $step_by);
            mul!($start + 1, $zeta, $step_by);
            mul!($start + 2, $zeta, $step_by);
            mul!($start + 3, $zeta, $step_by);
        }};
    }

    const STEP_BY_7: usize = 2 * COEFFICIENTS_IN_SIMD_UNIT;
    const STEP_BY_6: usize = (1 << 6) / COEFFICIENTS_IN_SIMD_UNIT;

    let zeta7 = mm256_set1_epi32(25847);
    let zeta60 = mm256_set1_epi32(-2608894);
    let zeta61 = mm256_set1_epi32(-518909);

    layer!(0, zeta7, STEP_BY_7);
    layer!(8, zeta7, STEP_BY_7);
    layer!(0, zeta60, STEP_BY_6);
    layer!(16, zeta61, STEP_BY_6);

    layer!(4, zeta7, STEP_BY_7);
    layer!(12, zeta7, STEP_BY_7);
    layer!(4, zeta60, STEP_BY_6);
    layer!(20, zeta61, STEP_BY_6);

    // Unused here.
    *zeta_i += 3;
}

#[inline(always)]
fn ntt_at_layer_5_to_3(zeta_i: &mut usize, re: &mut [Vec256; SIMD_UNITS_IN_RING_ELEMENT]) {
    let field_modulus = mm256_set1_epi32(FIELD_MODULUS);
    let inverse_of_modulus_mod_montgomery_r =
        mm256_set1_epi32(INVERSE_OF_MODULUS_MOD_MONTGOMERY_R as i32);

    // Layer 5
    {
        const STEP: usize = 1 << 5;
        const STEP_BY: usize = STEP / COEFFICIENTS_IN_SIMD_UNIT;

        for round in 0..(128 >> 5) {
            *zeta_i += 1;
            let rhs = mm256_set1_epi32(ZETAS_TIMES_MONTGOMERY_R[*zeta_i]);

            let offset = (round * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT;

            for j in offset..offset + STEP_BY {
                let t = arithmetic::montgomery_multiply2(
                    re[j + STEP_BY],
                    rhs,
                    field_modulus,
                    inverse_of_modulus_mod_montgomery_r,
                );

                re[j + STEP_BY] = arithmetic::subtract(re[j], t);
                re[j] = arithmetic::add(re[j], t);
            }
        }
    }

    // Layer 4
    {
        const STEP: usize = 1 << 4;
        const STEP_BY: usize = STEP / COEFFICIENTS_IN_SIMD_UNIT;

        for round in 0..(128 >> 4) {
            *zeta_i += 1;
            let rhs = mm256_set1_epi32(ZETAS_TIMES_MONTGOMERY_R[*zeta_i]);

            let offset = (round * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT;

            for j in offset..offset + STEP_BY {
                let t = arithmetic::montgomery_multiply2(
                    re[j + STEP_BY],
                    rhs,
                    field_modulus,
                    inverse_of_modulus_mod_montgomery_r,
                );

                re[j + STEP_BY] = arithmetic::subtract(re[j], t);
                re[j] = arithmetic::add(re[j], t);
            }
        }
    }

    // Layer 3
    {
        const STEP: usize = 1 << 3;
        const STEP_BY: usize = STEP / COEFFICIENTS_IN_SIMD_UNIT;

        for round in 0..(128 >> 3) {
            *zeta_i += 1;
            let rhs = mm256_set1_epi32(ZETAS_TIMES_MONTGOMERY_R[*zeta_i]);

            let offset = (round * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT;

            let t = arithmetic::montgomery_multiply2(
                re[offset + STEP_BY],
                rhs,
                field_modulus,
                inverse_of_modulus_mod_montgomery_r,
            );

            re[offset + STEP_BY] = arithmetic::subtract(re[offset], t);
            re[offset] = arithmetic::add(re[offset], t);
        }
    }
}

#[inline(always)]
pub(crate) fn ntt(
    mut re: [Vec256; SIMD_UNITS_IN_RING_ELEMENT],
) -> [Vec256; SIMD_UNITS_IN_RING_ELEMENT] {
    // std::println!("ntt");
    let mut zeta_i = 0;
    ntt_at_layer_7_and_6(&mut zeta_i, &mut re);
    ntt_at_layer_5_to_3(&mut zeta_i, &mut re);
    ntt_at_layer_2(&mut zeta_i, &mut re);
    ntt_at_layer_1(&mut zeta_i, &mut re);
    ntt_at_layer_0(&mut zeta_i, &mut re);

    re
}
