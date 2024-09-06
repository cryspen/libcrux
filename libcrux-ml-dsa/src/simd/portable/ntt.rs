use super::arithmetic::*;
use crate::simd::portable::PortableSIMDUnit;

#[inline(always)]
pub(crate) fn ntt_at_layer_0(
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
pub(crate) fn ntt_at_layer_1(
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
pub(crate) fn ntt_at_layer_2_2(
    simd_unit1: PortableSIMDUnit,
    simd_unit2: PortableSIMDUnit,
    zeta1: i32,
    zeta2: i32,
) -> (PortableSIMDUnit, PortableSIMDUnit) {
    (
        ntt_at_layer_2(simd_unit1, zeta1),
        ntt_at_layer_2(simd_unit2, zeta2),
    )
}

#[inline(always)]
pub(crate) fn ntt_at_layer_2(mut simd_unit: PortableSIMDUnit, zeta: i32) -> PortableSIMDUnit {
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
pub(crate) fn invert_ntt_at_layer_0(
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
pub(crate) fn invert_ntt_at_layer_1(
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
pub(crate) fn invert_ntt_at_layer_2(
    mut simd_unit: PortableSIMDUnit,
    zeta: i32,
) -> PortableSIMDUnit {
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
pub(crate) fn invert_ntt_at_layer_2_2(
    simd_unit1: PortableSIMDUnit,
    simd_unit2: PortableSIMDUnit,
    zeta1: i32,
    zeta2: i32,
) -> (PortableSIMDUnit, PortableSIMDUnit) {
    (
        invert_ntt_at_layer_2(simd_unit1, zeta1),
        invert_ntt_at_layer_2(simd_unit2, zeta2),
    )
}
