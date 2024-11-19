use super::arithmetic::{self, montgomery_multiply_by_constant, montgomery_multiply_fe_by_fer};
use super::vector_type::PortableSIMDUnit;
use crate::simd::traits::{COEFFICIENTS_IN_SIMD_UNIT, SIMD_UNITS_IN_RING_ELEMENT};

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
fn ntt_at_layer_0(re: &mut [PortableSIMDUnit; SIMD_UNITS_IN_RING_ELEMENT]) {
    #[inline(always)]
    fn round(
        re: &mut [PortableSIMDUnit; SIMD_UNITS_IN_RING_ELEMENT],
        index: usize,
        zeta_0: i32,
        zeta_1: i32,
        zeta_2: i32,
        zeta_3: i32,
    ) {
        re[index] = simd_unit_ntt_at_layer_0(re[index], zeta_0, zeta_1, zeta_2, zeta_3);
    }

    round(re, 0, 2091667, 3407706, 2316500, 3817976);
    round(re, 1, -3342478, 2244091, -2446433, -3562462);
    round(re, 2, 266997, 2434439, -1235728, 3513181);
    round(re, 3, -3520352, -3759364, -1197226, -3193378);
    round(re, 4, 900702, 1859098, 909542, 819034);
    round(re, 5, 495491, -1613174, -43260, -522500);
    round(re, 6, -655327, -3122442, 2031748, 3207046);
    round(re, 7, -3556995, -525098, -768622, -3595838);
    round(re, 8, 342297, 286988, -2437823, 4108315);
    round(re, 9, 3437287, -3342277, 1735879, 203044);
    round(re, 10, 2842341, 2691481, -2590150, 1265009);
    round(re, 11, 4055324, 1247620, 2486353, 1595974);
    round(re, 12, -3767016, 1250494, 2635921, -3548272);
    round(re, 13, -2994039, 1869119, 1903435, -1050970);
    round(re, 14, -1333058, 1237275, -3318210, -1430225);
    round(re, 15, -451100, 1312455, 3306115, -1962642);
    round(re, 16, -1279661, 1917081, -2546312, -1374803);
    round(re, 17, 1500165, 777191, 2235880, 3406031);
    round(re, 18, -542412, -2831860, -1671176, -1846953);
    round(re, 19, -2584293, -3724270, 594136, -3776993);
    round(re, 20, -2013608, 2432395, 2454455, -164721);
    round(re, 21, 1957272, 3369112, 185531, -1207385);
    round(re, 22, -3183426, 162844, 1616392, 3014001);
    round(re, 23, 810149, 1652634, -3694233, -1799107);
    round(re, 24, -3038916, 3523897, 3866901, 269760);
    round(re, 25, 2213111, -975884, 1717735, 472078);
    round(re, 26, -426683, 1723600, -1803090, 1910376);
    round(re, 27, -1667432, -1104333, -260646, -3833893);
    round(re, 28, -2939036, -2235985, -420899, -2286327);
    round(re, 29, 183443, -976891, 1612842, -3545687);
    round(re, 30, -554416, 3919660, -48306, -1362209);
    round(re, 31, 3937738, 1400424, -846154, 1976782);
}

#[inline(always)]
fn ntt_at_layer_1(re: &mut [PortableSIMDUnit; SIMD_UNITS_IN_RING_ELEMENT]) {
    #[inline(always)]
    fn round(
        re: &mut [PortableSIMDUnit; SIMD_UNITS_IN_RING_ELEMENT],
        index: usize,
        zeta_0: i32,
        zeta_1: i32,
    ) {
        re[index] = simd_unit_ntt_at_layer_1(re[index], zeta_0, zeta_1);
    }

    round(re, 0, -3930395, -1528703);
    round(re, 1, -3677745, -3041255);
    round(re, 2, -1452451, 3475950);
    round(re, 3, 2176455, -1585221);
    round(re, 4, -1257611, 1939314);
    round(re, 5, -4083598, -1000202);
    round(re, 6, -3190144, -3157330);
    round(re, 7, -3632928, 126922);
    round(re, 8, 3412210, -983419);
    round(re, 9, 2147896, 2715295);
    round(re, 10, -2967645, -3693493);
    round(re, 11, -411027, -2477047);
    round(re, 12, -671102, -1228525);
    round(re, 13, -22981, -1308169);
    round(re, 14, -381987, 1349076);
    round(re, 15, 1852771, -1430430);
    round(re, 16, -3343383, 264944);
    round(re, 17, 508951, 3097992);
    round(re, 18, 44288, -1100098);
    round(re, 19, 904516, 3958618);
    round(re, 20, -3724342, -8578);
    round(re, 21, 1653064, -3249728);
    round(re, 22, 2389356, -210977);
    round(re, 23, 759969, -1316856);
    round(re, 24, 189548, -3553272);
    round(re, 25, 3159746, -1851402);
    round(re, 26, -2409325, -177440);
    round(re, 27, 1315589, 1341330);
    round(re, 28, 1285669, -1584928);
    round(re, 29, -812732, -1439742);
    round(re, 30, -3019102, -3881060);
    round(re, 31, -3628969, 3839961);
}

#[inline(always)]
fn ntt_at_layer_2(re: &mut [PortableSIMDUnit; SIMD_UNITS_IN_RING_ELEMENT]) {
    #[inline(always)]
    fn round(re: &mut [PortableSIMDUnit; SIMD_UNITS_IN_RING_ELEMENT], index: usize, zeta: i32) {
        re[index] = simd_unit_ntt_at_layer_2(re[index], zeta);
    }

    round(re, 0, 2706023);
    round(re, 1, 95776);
    round(re, 2, 3077325);
    round(re, 3, 3530437);
    round(re, 4, -1661693);
    round(re, 5, -3592148);
    round(re, 6, -2537516);
    round(re, 7, 3915439);
    round(re, 8, -3861115);
    round(re, 9, -3043716);
    round(re, 10, 3574422);
    round(re, 11, -2867647);
    round(re, 12, 3539968);
    round(re, 13, -300467);
    round(re, 14, 2348700);
    round(re, 15, -539299);
    round(re, 16, -1699267);
    round(re, 17, -1643818);
    round(re, 18, 3505694);
    round(re, 19, -3821735);
    round(re, 20, 3507263);
    round(re, 21, -2140649);
    round(re, 22, -1600420);
    round(re, 23, 3699596);
    round(re, 24, 811944);
    round(re, 25, 531354);
    round(re, 26, 954230);
    round(re, 27, 3881043);
    round(re, 28, 3900724);
    round(re, 29, -2556880);
    round(re, 30, 2071892);
    round(re, 31, -2797779);
}

#[inline(always)]
fn outer_3_plus<const OFFSET: usize, const STEP_BY: usize, const ZETA: i32>(
    re: &mut [PortableSIMDUnit; SIMD_UNITS_IN_RING_ELEMENT],
) {
    for j in OFFSET..OFFSET + STEP_BY {
        let t = montgomery_multiply_by_constant(re[j + STEP_BY], ZETA);

        re[j + STEP_BY] = arithmetic::subtract(&re[j], &t);
        re[j] = arithmetic::add(&re[j], &t);
    }
    () // Needed because of https://github.com/hacspec/hax/issues/720
}

#[inline(always)]
fn ntt_at_layer_3(re: &mut [PortableSIMDUnit; SIMD_UNITS_IN_RING_ELEMENT]) {
    const STEP: usize = 8; // 1 << LAYER;
    const STEP_BY: usize = 1; // step / COEFFICIENTS_IN_SIMD_UNIT;

    outer_3_plus::<{ (0 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, 2725464>(re);
    outer_3_plus::<{ (1 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, 1024112>(re);
    outer_3_plus::<{ (2 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, -1079900>(re);
    outer_3_plus::<{ (3 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, 3585928>(re);
    outer_3_plus::<{ (4 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, -549488>(re);
    outer_3_plus::<{ (5 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, -1119584>(re);
    outer_3_plus::<{ (6 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, 2619752>(re);
    outer_3_plus::<{ (7 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, -2108549>(re);
    outer_3_plus::<{ (8 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, -2118186>(re);
    outer_3_plus::<{ (9 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, -3859737>(re);
    outer_3_plus::<{ (10 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, -1399561>(re);
    outer_3_plus::<{ (11 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, -3277672>(re);
    outer_3_plus::<{ (12 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, 1757237>(re);
    outer_3_plus::<{ (13 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, -19422>(re);
    outer_3_plus::<{ (14 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, 4010497>(re);
    outer_3_plus::<{ (15 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, 280005>(re);
}

#[inline(always)]
fn ntt_at_layer_4(re: &mut [PortableSIMDUnit; SIMD_UNITS_IN_RING_ELEMENT]) {
    const STEP: usize = 16; // 1 << LAYER;
    const STEP_BY: usize = 2; // step / COEFFICIENTS_IN_SIMD_UNIT;

    outer_3_plus::<{ (0 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, 1826347>(re);
    outer_3_plus::<{ (1 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, 2353451>(re);
    outer_3_plus::<{ (2 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, -359251>(re);
    outer_3_plus::<{ (3 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, -2091905>(re);
    outer_3_plus::<{ (4 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, 3119733>(re);
    outer_3_plus::<{ (5 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, -2884855>(re);
    outer_3_plus::<{ (6 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, 3111497>(re);
    outer_3_plus::<{ (7 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, 2680103>(re);
}

#[inline(always)]
fn ntt_at_layer_5(re: &mut [PortableSIMDUnit; SIMD_UNITS_IN_RING_ELEMENT]) {
    const STEP: usize = 32; // 1 << LAYER;
    const STEP_BY: usize = 4; // step / COEFFICIENTS_IN_SIMD_UNIT;

    outer_3_plus::<{ (0 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, 237124>(re);
    outer_3_plus::<{ (1 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, -777960>(re);
    outer_3_plus::<{ (2 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, -876248>(re);
    outer_3_plus::<{ (3 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, 466468>(re);
}

#[inline(always)]
fn ntt_at_layer_6(re: &mut [PortableSIMDUnit; SIMD_UNITS_IN_RING_ELEMENT]) {
    const STEP: usize = 64; // 1 << LAYER;
    const STEP_BY: usize = 8; // step / COEFFICIENTS_IN_SIMD_UNIT;

    outer_3_plus::<{ (0 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, -2608894>(re);
    outer_3_plus::<{ (1 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, -518909>(re);
}

#[inline(always)]
fn ntt_at_layer_7(re: &mut [PortableSIMDUnit; SIMD_UNITS_IN_RING_ELEMENT]) {
    const STEP: usize = 128; // 1 << LAYER;
    const STEP_BY: usize = 16; // step / COEFFICIENTS_IN_SIMD_UNIT;

    outer_3_plus::<{ (0 * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT }, STEP_BY, 25847>(re);
}

#[inline(always)]
pub(crate) fn ntt(
    mut re: [PortableSIMDUnit; SIMD_UNITS_IN_RING_ELEMENT],
) -> [PortableSIMDUnit; SIMD_UNITS_IN_RING_ELEMENT] {
    ntt_at_layer_7(&mut re);
    ntt_at_layer_6(&mut re);
    ntt_at_layer_5(&mut re);
    ntt_at_layer_4(&mut re);
    ntt_at_layer_3(&mut re);
    ntt_at_layer_2(&mut re);
    ntt_at_layer_1(&mut re);
    ntt_at_layer_0(&mut re);

    re
}
