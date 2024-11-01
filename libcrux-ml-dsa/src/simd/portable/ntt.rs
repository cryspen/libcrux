use super::arithmetic::{self, montgomery_multiply_fe_by_fer};
use crate::simd::{
    portable::PortableSIMDUnit,
    traits::{
        montgomery_multiply_by_fer, COEFFICIENTS_IN_SIMD_UNIT, SIMD_UNITS_IN_RING_ELEMENT,
        ZETAS_TIMES_MONTGOMERY_R,
    },
};

#[inline(always)]
pub fn simd_unit_ntt_at_layer_0(
    mut simd_unit: PortableSIMDUnit,
    zeta0: i32,
    zeta1: i32,
    zeta2: i32,
    zeta3: i32,
) -> PortableSIMDUnit {
    let t = montgomery_multiply_fe_by_fer(simd_unit.coefficients[1], zeta0);
    simd_unit.coefficients[1] = simd_unit.coefficients[0] - t;
    simd_unit.coefficients[0] = simd_unit.coefficients[0] + t;

    let t = montgomery_multiply_fe_by_fer(simd_unit.coefficients[3], zeta1);
    simd_unit.coefficients[3] = simd_unit.coefficients[2] - t;
    simd_unit.coefficients[2] = simd_unit.coefficients[2] + t;

    let t = montgomery_multiply_fe_by_fer(simd_unit.coefficients[5], zeta2);
    simd_unit.coefficients[5] = simd_unit.coefficients[4] - t;
    simd_unit.coefficients[4] = simd_unit.coefficients[4] + t;

    let t = montgomery_multiply_fe_by_fer(simd_unit.coefficients[7], zeta3);
    simd_unit.coefficients[7] = simd_unit.coefficients[6] - t;
    simd_unit.coefficients[6] = simd_unit.coefficients[6] + t;

    simd_unit
}
#[inline(always)]
pub fn simd_unit_ntt_at_layer_1(
    mut simd_unit: PortableSIMDUnit,
    zeta1: i32,
    zeta2: i32,
) -> PortableSIMDUnit {
    let t = montgomery_multiply_fe_by_fer(simd_unit.coefficients[2], zeta1);
    simd_unit.coefficients[2] = simd_unit.coefficients[0] - t;
    simd_unit.coefficients[0] = simd_unit.coefficients[0] + t;

    let t = montgomery_multiply_fe_by_fer(simd_unit.coefficients[3], zeta1);
    simd_unit.coefficients[3] = simd_unit.coefficients[1] - t;
    simd_unit.coefficients[1] = simd_unit.coefficients[1] + t;

    let t = montgomery_multiply_fe_by_fer(simd_unit.coefficients[6], zeta2);
    simd_unit.coefficients[6] = simd_unit.coefficients[4] - t;
    simd_unit.coefficients[4] = simd_unit.coefficients[4] + t;

    let t = montgomery_multiply_fe_by_fer(simd_unit.coefficients[7], zeta2);
    simd_unit.coefficients[7] = simd_unit.coefficients[5] - t;
    simd_unit.coefficients[5] = simd_unit.coefficients[5] + t;

    simd_unit
}
#[inline(always)]
pub fn simd_unit_ntt_at_layer_2(mut simd_unit: PortableSIMDUnit, zeta: i32) -> PortableSIMDUnit {
    let t = montgomery_multiply_fe_by_fer(simd_unit.coefficients[4], zeta);
    simd_unit.coefficients[4] = simd_unit.coefficients[0] - t;
    simd_unit.coefficients[0] = simd_unit.coefficients[0] + t;

    let t = montgomery_multiply_fe_by_fer(simd_unit.coefficients[5], zeta);
    simd_unit.coefficients[5] = simd_unit.coefficients[1] - t;
    simd_unit.coefficients[1] = simd_unit.coefficients[1] + t;

    let t = montgomery_multiply_fe_by_fer(simd_unit.coefficients[6], zeta);
    simd_unit.coefficients[6] = simd_unit.coefficients[2] - t;
    simd_unit.coefficients[2] = simd_unit.coefficients[2] + t;

    let t = montgomery_multiply_fe_by_fer(simd_unit.coefficients[7], zeta);
    simd_unit.coefficients[7] = simd_unit.coefficients[3] - t;
    simd_unit.coefficients[3] = simd_unit.coefficients[3] + t;

    simd_unit
}

#[inline(always)]
pub fn invert_ntt_at_layer_0(
    mut simd_unit: PortableSIMDUnit,
    zeta0: i32,
    zeta1: i32,
    zeta2: i32,
    zeta3: i32,
) -> PortableSIMDUnit {
    let a_minus_b = simd_unit.coefficients[1] - simd_unit.coefficients[0];
    simd_unit.coefficients[0] = simd_unit.coefficients[0] + simd_unit.coefficients[1];
    simd_unit.coefficients[1] = montgomery_multiply_fe_by_fer(a_minus_b, zeta0);

    let a_minus_b = simd_unit.coefficients[3] - simd_unit.coefficients[2];
    simd_unit.coefficients[2] = simd_unit.coefficients[2] + simd_unit.coefficients[3];
    simd_unit.coefficients[3] = montgomery_multiply_fe_by_fer(a_minus_b, zeta1);

    let a_minus_b = simd_unit.coefficients[5] - simd_unit.coefficients[4];
    simd_unit.coefficients[4] = simd_unit.coefficients[4] + simd_unit.coefficients[5];
    simd_unit.coefficients[5] = montgomery_multiply_fe_by_fer(a_minus_b, zeta2);

    let a_minus_b = simd_unit.coefficients[7] - simd_unit.coefficients[6];
    simd_unit.coefficients[6] = simd_unit.coefficients[6] + simd_unit.coefficients[7];
    simd_unit.coefficients[7] = montgomery_multiply_fe_by_fer(a_minus_b, zeta3);

    simd_unit
}
#[inline(always)]
pub fn invert_ntt_at_layer_1(
    mut simd_unit: PortableSIMDUnit,
    zeta0: i32,
    zeta1: i32,
) -> PortableSIMDUnit {
    let a_minus_b = simd_unit.coefficients[2] - simd_unit.coefficients[0];
    simd_unit.coefficients[0] = simd_unit.coefficients[0] + simd_unit.coefficients[2];
    simd_unit.coefficients[2] = montgomery_multiply_fe_by_fer(a_minus_b, zeta0);

    let a_minus_b = simd_unit.coefficients[3] - simd_unit.coefficients[1];
    simd_unit.coefficients[1] = simd_unit.coefficients[1] + simd_unit.coefficients[3];
    simd_unit.coefficients[3] = montgomery_multiply_fe_by_fer(a_minus_b, zeta0);

    let a_minus_b = simd_unit.coefficients[6] - simd_unit.coefficients[4];
    simd_unit.coefficients[4] = simd_unit.coefficients[4] + simd_unit.coefficients[6];
    simd_unit.coefficients[6] = montgomery_multiply_fe_by_fer(a_minus_b, zeta1);

    let a_minus_b = simd_unit.coefficients[7] - simd_unit.coefficients[5];
    simd_unit.coefficients[5] = simd_unit.coefficients[5] + simd_unit.coefficients[7];
    simd_unit.coefficients[7] = montgomery_multiply_fe_by_fer(a_minus_b, zeta1);

    simd_unit
}
#[inline(always)]
pub fn invert_ntt_at_layer_2(mut simd_unit: PortableSIMDUnit, zeta: i32) -> PortableSIMDUnit {
    let a_minus_b = simd_unit.coefficients[4] - simd_unit.coefficients[0];
    simd_unit.coefficients[0] = simd_unit.coefficients[0] + simd_unit.coefficients[4];
    simd_unit.coefficients[4] = montgomery_multiply_fe_by_fer(a_minus_b, zeta);

    let a_minus_b = simd_unit.coefficients[5] - simd_unit.coefficients[1];
    simd_unit.coefficients[1] = simd_unit.coefficients[1] + simd_unit.coefficients[5];
    simd_unit.coefficients[5] = montgomery_multiply_fe_by_fer(a_minus_b, zeta);

    let a_minus_b = simd_unit.coefficients[6] - simd_unit.coefficients[2];
    simd_unit.coefficients[2] = simd_unit.coefficients[2] + simd_unit.coefficients[6];
    simd_unit.coefficients[6] = montgomery_multiply_fe_by_fer(a_minus_b, zeta);

    let a_minus_b = simd_unit.coefficients[7] - simd_unit.coefficients[3];
    simd_unit.coefficients[3] = simd_unit.coefficients[3] + simd_unit.coefficients[7];
    simd_unit.coefficients[7] = montgomery_multiply_fe_by_fer(a_minus_b, zeta);

    simd_unit
}

#[inline(always)]
fn ntt_at_layer_0(zeta_i: &mut usize, re: &mut [PortableSIMDUnit; SIMD_UNITS_IN_RING_ELEMENT]) {
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
fn ntt_at_layer_1(zeta_i: &mut usize, re: &mut [PortableSIMDUnit; SIMD_UNITS_IN_RING_ELEMENT]) {
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
#[inline(always)]
fn ntt_at_layer_2(zeta_i: &mut usize, re: &mut [PortableSIMDUnit; SIMD_UNITS_IN_RING_ELEMENT]) {
    for round in 0..re.len() {
        *zeta_i += 1;
        re[round] = simd_unit_ntt_at_layer_2(re[round], ZETAS_TIMES_MONTGOMERY_R[*zeta_i]);
    }
}
#[inline(always)]
fn ntt_at_layer_3_plus<const LAYER: usize>(
    zeta_i: &mut usize,
    re: &mut [PortableSIMDUnit; SIMD_UNITS_IN_RING_ELEMENT],
) {
    let step = 1 << LAYER;

    for round in 0..(128 >> LAYER) {
        *zeta_i += 1;

        let offset = (round * step * 2) / COEFFICIENTS_IN_SIMD_UNIT;
        let step_by = step / COEFFICIENTS_IN_SIMD_UNIT;

        for j in offset..offset + step_by {
            let t = montgomery_multiply_by_fer(re[j + step_by], ZETAS_TIMES_MONTGOMERY_R[*zeta_i]);

            re[j + step_by] = arithmetic::subtract(&re[j], &t);
            re[j] = arithmetic::add(&re[j], &t);
        }
    }
}

#[inline(always)]
pub(crate) fn ntt(
    mut re: [PortableSIMDUnit; SIMD_UNITS_IN_RING_ELEMENT],
) -> [PortableSIMDUnit; SIMD_UNITS_IN_RING_ELEMENT] {
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
