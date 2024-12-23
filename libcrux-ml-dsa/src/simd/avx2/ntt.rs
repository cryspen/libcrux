use super::{arithmetic, AVX2RingElement};
use crate::simd::traits::{COEFFICIENTS_IN_SIMD_UNIT, SIMD_UNITS_IN_RING_ELEMENT};

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
    let mut zeta_products = mm256_unpackhi_epi64(a_shuffled, b_shuffled);
    let zetas = mm256_set_epi32(
        zeta_b3, zeta_b2, zeta_a3, zeta_a2, zeta_b1, zeta_b0, zeta_a1, zeta_a0,
    );

    arithmetic::montgomery_multiply(&mut zeta_products, &zetas);

    let add_terms = arithmetic::add(&summands, &zeta_products);
    let sub_terms = arithmetic::subtract(&summands, &zeta_products);

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
    let mut zeta_products = mm256_unpackhi_epi64(a, b);

    let zetas = mm256_set_epi32(
        zeta_b1, zeta_b1, zeta_a1, zeta_a1, zeta_b0, zeta_b0, zeta_a0, zeta_a0,
    );
    arithmetic::montgomery_multiply(&mut zeta_products, &zetas);

    let add_terms = arithmetic::add(&summands, &zeta_products);
    let sub_terms = arithmetic::subtract(&summands, &zeta_products);

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
    let mut zeta_products = mm256_permute2x128_si256::<0b0001_0011>(b, a);

    let zetas = mm256_set_epi32(zeta1, zeta1, zeta1, zeta1, zeta0, zeta0, zeta0, zeta0);
    arithmetic::montgomery_multiply(&mut zeta_products, &zetas);

    let add_terms = arithmetic::add(&summands, &zeta_products);
    let sub_terms = arithmetic::subtract(&summands, &zeta_products);

    let a_out = mm256_set_m128i(
        mm256_castsi256_si128(sub_terms),
        mm256_castsi256_si128(add_terms),
    );
    let b_out = mm256_permute2x128_si256::<0b0001_0011>(sub_terms, add_terms);

    (a_out, b_out)
}

#[cfg_attr(not(hax), target_feature(enable = "avx2"))]
#[allow(unsafe_code)]
unsafe fn ntt_at_layer_0(re: &mut [Vec256; SIMD_UNITS_IN_RING_ELEMENT]) {
    #[inline(always)]
    fn round(
        re: &mut [Vec256; SIMD_UNITS_IN_RING_ELEMENT],
        index: usize,
        zeta_0: i32,
        zeta_1: i32,
        zeta_2: i32,
        zeta_3: i32,
        zeta_4: i32,
        zeta_5: i32,
        zeta_6: i32,
        zeta_7: i32,
    ) {
        let (a, b) = butterfly_2(
            re[index],
            re[index + 1],
            zeta_0,
            zeta_1,
            zeta_2,
            zeta_3,
            zeta_4,
            zeta_5,
            zeta_6,
            zeta_7,
        );
        re[index] = a;
        re[index + 1] = b;
    }

    round(
        re, 0, 2091667, 3407706, 2316500, 3817976, -3342478, 2244091, -2446433, -3562462,
    );
    round(
        re, 2, 266997, 2434439, -1235728, 3513181, -3520352, -3759364, -1197226, -3193378,
    );
    round(
        re, 4, 900702, 1859098, 909542, 819034, 495491, -1613174, -43260, -522500,
    );
    round(
        re, 6, -655327, -3122442, 2031748, 3207046, -3556995, -525098, -768622, -3595838,
    );
    round(
        re, 8, 342297, 286988, -2437823, 4108315, 3437287, -3342277, 1735879, 203044,
    );
    round(
        re, 10, 2842341, 2691481, -2590150, 1265009, 4055324, 1247620, 2486353, 1595974,
    );
    round(
        re, 12, -3767016, 1250494, 2635921, -3548272, -2994039, 1869119, 1903435, -1050970,
    );
    round(
        re, 14, -1333058, 1237275, -3318210, -1430225, -451100, 1312455, 3306115, -1962642,
    );
    round(
        re, 16, -1279661, 1917081, -2546312, -1374803, 1500165, 777191, 2235880, 3406031,
    );
    round(
        re, 18, -542412, -2831860, -1671176, -1846953, -2584293, -3724270, 594136, -3776993,
    );
    round(
        re, 20, -2013608, 2432395, 2454455, -164721, 1957272, 3369112, 185531, -1207385,
    );
    round(
        re, 22, -3183426, 162844, 1616392, 3014001, 810149, 1652634, -3694233, -1799107,
    );
    round(
        re, 24, -3038916, 3523897, 3866901, 269760, 2213111, -975884, 1717735, 472078,
    );
    round(
        re, 26, -426683, 1723600, -1803090, 1910376, -1667432, -1104333, -260646, -3833893,
    );
    round(
        re, 28, -2939036, -2235985, -420899, -2286327, 183443, -976891, 1612842, -3545687,
    );
    round(
        re, 30, -554416, 3919660, -48306, -1362209, 3937738, 1400424, -846154, 1976782,
    );
}

#[cfg_attr(not(hax), target_feature(enable = "avx2"))]
#[allow(unsafe_code)]
unsafe fn ntt_at_layer_1(re: &mut [Vec256; SIMD_UNITS_IN_RING_ELEMENT]) {
    #[inline(always)]
    fn round(
        re: &mut [Vec256; SIMD_UNITS_IN_RING_ELEMENT],
        index: usize,
        zeta_0: i32,
        zeta_1: i32,
        zeta_2: i32,
        zeta_3: i32,
    ) {
        let (a, b) = butterfly_4(re[index], re[index + 1], zeta_0, zeta_1, zeta_2, zeta_3);
        re[index] = a;
        re[index + 1] = b;
    }

    round(re, 0, -3930395, -1528703, -3677745, -3041255);
    round(re, 2, -1452451, 3475950, 2176455, -1585221);
    round(re, 4, -1257611, 1939314, -4083598, -1000202);
    round(re, 6, -3190144, -3157330, -3632928, 126922);
    round(re, 8, 3412210, -983419, 2147896, 2715295);
    round(re, 10, -2967645, -3693493, -411027, -2477047);
    round(re, 12, -671102, -1228525, -22981, -1308169);
    round(re, 14, -381987, 1349076, 1852771, -1430430);
    round(re, 16, -3343383, 264944, 508951, 3097992);
    round(re, 18, 44288, -1100098, 904516, 3958618);
    round(re, 20, -3724342, -8578, 1653064, -3249728);
    round(re, 22, 2389356, -210977, 759969, -1316856);
    round(re, 24, 189548, -3553272, 3159746, -1851402);
    round(re, 26, -2409325, -177440, 1315589, 1341330);
    round(re, 28, 1285669, -1584928, -812732, -1439742);
    round(re, 30, -3019102, -3881060, -3628969, 3839961);
}

#[cfg_attr(not(hax), target_feature(enable = "avx2"))]
#[allow(unsafe_code)]
unsafe fn ntt_at_layer_2(re: &mut [Vec256; SIMD_UNITS_IN_RING_ELEMENT]) {
    #[inline(always)]
    fn round(
        re: &mut [Vec256; SIMD_UNITS_IN_RING_ELEMENT],
        index: usize,
        zeta_0: i32,
        zeta_1: i32,
    ) {
        let (a, b) = butterfly_8(re[index], re[index + 1], zeta_0, zeta_1);
        re[index] = a;
        re[index + 1] = b;
    }

    round(re, 0, 2706023, 95776);
    round(re, 2, 3077325, 3530437);
    round(re, 4, -1661693, -3592148);
    round(re, 6, -2537516, 3915439);
    round(re, 8, -3861115, -3043716);
    round(re, 10, 3574422, -2867647);
    round(re, 12, 3539968, -300467);
    round(re, 14, 2348700, -539299);
    round(re, 16, -1699267, -1643818);
    round(re, 18, 3505694, -3821735);
    round(re, 20, 3507263, -2140649);
    round(re, 22, -1600420, 3699596);
    round(re, 24, 811944, 531354);
    round(re, 26, 954230, 3881043);
    round(re, 28, 3900724, -2556880);
    round(re, 30, 2071892, -2797779);
}

/// This is equivalent to the pqclean 0 and 1
///
/// This does 32 Montgomery multiplications (192 multiplications).
/// This is the same as in pqclean. The only difference is locality of registers.
#[cfg_attr(not(hax), target_feature(enable = "avx2"))]
#[allow(unsafe_code)]
unsafe fn ntt_at_layer_7_and_6(re: &mut [Vec256; SIMD_UNITS_IN_RING_ELEMENT]) {
    let field_modulus = mm256_set1_epi32(crate::simd::traits::FIELD_MODULUS);
    let inverse_of_modulus_mod_montgomery_r =
        mm256_set1_epi32(crate::simd::traits::INVERSE_OF_MODULUS_MOD_MONTGOMERY_R as i32);

    #[inline(always)]
    fn mul(
        re: &mut [Vec256; SIMD_UNITS_IN_RING_ELEMENT],
        index: usize,
        zeta: Vec256,
        step_by: usize,
        field_modulus: Vec256,
        inverse_of_modulus_mod_montgomery_r: Vec256,
    ) {
        let prod02 = mm256_mul_epi32(re[index + step_by], zeta);
        let prod13 = mm256_mul_epi32(
            mm256_shuffle_epi32::<0b11_11_01_01>(re[index + step_by]), // 0xF5
            mm256_shuffle_epi32::<0b11_11_01_01>(zeta),                // 0xF5
        );
        let k02 = mm256_mul_epi32(prod02, inverse_of_modulus_mod_montgomery_r);
        let k13 = mm256_mul_epi32(prod13, inverse_of_modulus_mod_montgomery_r);

        let c02 = mm256_mul_epi32(k02, field_modulus);
        let c13 = mm256_mul_epi32(k13, field_modulus);

        let res02 = mm256_sub_epi32(prod02, c02);
        let res13 = mm256_sub_epi32(prod13, c13);
        let res02_shifted = mm256_shuffle_epi32::<0b11_11_01_01>(res02); // 0xF5
        let t = mm256_blend_epi32::<0b10101010>(res02_shifted, res13); // 0xAA

        re[index + step_by] = arithmetic::subtract(&re[index], &t);
        re[index] = arithmetic::add(&re[index], &t);
    }

    macro_rules! layer {
        ($start:literal, $zeta:expr, $step_by:expr) => {{
            mul(
                re,
                $start,
                $zeta,
                $step_by,
                field_modulus,
                inverse_of_modulus_mod_montgomery_r,
            );
            mul(
                re,
                $start + 1,
                $zeta,
                $step_by,
                field_modulus,
                inverse_of_modulus_mod_montgomery_r,
            );
            mul(
                re,
                $start + 2,
                $zeta,
                $step_by,
                field_modulus,
                inverse_of_modulus_mod_montgomery_r,
            );
            mul(
                re,
                $start + 3,
                $zeta,
                $step_by,
                field_modulus,
                inverse_of_modulus_mod_montgomery_r,
            );
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
}

/// Layer 5, 4, 3
///
/// Each layer does 16 Montgomery multiplications -> 3*16 = 48 total
/// pqclean does 4 * 4 on each layer -> 48 total | plus 4 * 4 shuffles every time (48)
#[cfg_attr(not(hax), target_feature(enable = "avx2"))]
#[allow(unsafe_code)]
unsafe fn ntt_at_layer_5_to_3(re: &mut [Vec256; SIMD_UNITS_IN_RING_ELEMENT]) {
    #[inline(always)]
    fn round<const STEP: usize, const STEP_BY: usize>(
        re: &mut [Vec256; SIMD_UNITS_IN_RING_ELEMENT],
        index: usize,
        zeta: i32,
    ) {
        let rhs = mm256_set1_epi32(zeta);
        let offset = (index * STEP * 2) / COEFFICIENTS_IN_SIMD_UNIT;

        for j in offset..offset + STEP_BY {
            let mut t = re[j + STEP_BY];
            arithmetic::montgomery_multiply(&mut t, &rhs);

            re[j + STEP_BY] = arithmetic::subtract(&re[j], &t);
            re[j] = arithmetic::add(&re[j], &t);
        }
        () // Needed because of https://github.com/hacspec/hax/issues/720
    }

    // Layer 5
    {
        // 0: 0, 1, 2, 3
        // 1: 8, 9, 10, 11
        // 2: 16, 17, 18, 19
        // 3: 24, 25, 26, 27
        const STEP: usize = 1 << 5;
        const STEP_BY: usize = STEP / COEFFICIENTS_IN_SIMD_UNIT;

        round::<STEP, STEP_BY>(re, 0, 237124);
        round::<STEP, STEP_BY>(re, 1, -777960);
        round::<STEP, STEP_BY>(re, 2, -876248);
        round::<STEP, STEP_BY>(re, 3, 466468);
    }

    // Layer 4
    {
        // 0: 0, 1
        // 1: 4, 5
        // 2: 8, 9
        // 3: 12, 13
        // 4: 16, 17
        // 5: 20, 21
        // 6: 24, 25
        // 7: 28, 29
        const STEP: usize = 1 << 4;
        const STEP_BY: usize = STEP / COEFFICIENTS_IN_SIMD_UNIT;

        round::<STEP, STEP_BY>(re, 0, 1826347);
        round::<STEP, STEP_BY>(re, 1, 2353451);
        round::<STEP, STEP_BY>(re, 2, -359251);
        round::<STEP, STEP_BY>(re, 3, -2091905);
        round::<STEP, STEP_BY>(re, 4, 3119733);
        round::<STEP, STEP_BY>(re, 5, -2884855);
        round::<STEP, STEP_BY>(re, 6, 3111497);
        round::<STEP, STEP_BY>(re, 7, 2680103);
    }

    // Layer 3
    {
        // 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15
        const STEP: usize = 1 << 3;
        const STEP_BY: usize = STEP / COEFFICIENTS_IN_SIMD_UNIT;

        round::<STEP, STEP_BY>(re, 0, 2725464);
        round::<STEP, STEP_BY>(re, 1, 1024112);
        round::<STEP, STEP_BY>(re, 2, -1079900);
        round::<STEP, STEP_BY>(re, 3, 3585928);
        round::<STEP, STEP_BY>(re, 4, -549488);
        round::<STEP, STEP_BY>(re, 5, -1119584);
        round::<STEP, STEP_BY>(re, 6, 2619752);
        round::<STEP, STEP_BY>(re, 7, -2108549);
        round::<STEP, STEP_BY>(re, 8, -2118186);
        round::<STEP, STEP_BY>(re, 9, -3859737);
        round::<STEP, STEP_BY>(re, 10, -1399561);
        round::<STEP, STEP_BY>(re, 11, -3277672);
        round::<STEP, STEP_BY>(re, 12, 1757237);
        round::<STEP, STEP_BY>(re, 13, -19422);
        round::<STEP, STEP_BY>(re, 14, 4010497);
        round::<STEP, STEP_BY>(re, 15, 280005);
    }
    ()
}

#[allow(unsafe_code)]
#[inline(always)]
pub(crate) fn ntt(re: &mut AVX2RingElement) {
    unsafe {
        ntt_at_layer_7_and_6(re);
        ntt_at_layer_5_to_3(re);
        ntt_at_layer_2(re);
        ntt_at_layer_1(re);
        ntt_at_layer_0(re);
    }
}
