//use crate::hax_utils::hax_debug_assert;
use super::arithmetic::*;
use super::intvec::*;

pub(crate) const VECS_IN_RING_ELEMENT: usize =
    super::constants::COEFFICIENTS_IN_RING_ELEMENT / SIZE_VEC;

#[derive(Clone, Copy)]
pub struct PolynomialRingElement {
    pub(crate) coefficients: [IntVec; VECS_IN_RING_ELEMENT],
}

impl PolynomialRingElement {
    pub(crate) fn ZERO() -> Self {
        Self {
            // FIXME:  The THIR body of item DefId(0:415 ~ libcrux_ml_kem[9000]::polynomial::{impl#0}::ZERO::{constant#0}) was stolen.
            coefficients: [intvec::ZERO_VEC(); 32],
        }
    }
}

#[inline(always)]
pub(crate) fn to_i32_array(a: PolynomialRingElement) -> [i32; 256] {
    let mut result = [0i32; 256];
    for i in 0..VECS_IN_RING_ELEMENT {
        let result_i = int_vec_to_i32_array(a.coefficients[i]);
        // XXX: this should be `copy_from_slice`
        for j in 0..SIZE_VEC {
            result[i * SIZE_VEC + j] = result_i[j];
        }
    }
    result
}

#[inline(always)]
pub(crate) fn from_i32_array(a: [i32; 256]) -> PolynomialRingElement {
    let mut result = PolynomialRingElement::ZERO();
    for i in 0..VECS_IN_RING_ELEMENT {
        result.coefficients[i] =
            int_vec_from_i32_array(a[i * SIZE_VEC..(i + 1) * SIZE_VEC].try_into().unwrap());
    }
    result
}

/// Given two polynomial ring elements `lhs` and `rhs`, compute the pointwise
/// sum of their constituent coefficients.
#[inline(always)]
pub(crate) fn add_to_ring_element<const K: usize>(
    mut lhs: PolynomialRingElement,
    rhs: &PolynomialRingElement,
) -> PolynomialRingElement {
    for i in 0..VECS_IN_RING_ELEMENT {
        lhs.coefficients[i] = add_int_vec(lhs.coefficients[i], &rhs.coefficients[i]);
    }
    lhs
}

#[inline(always)]
pub(crate) fn poly_barrett_reduce(mut a: PolynomialRingElement) -> PolynomialRingElement {
    // XXX: Use `map` when extraction is happy with that.
    for i in 0..VECS_IN_RING_ELEMENT {
        a.coefficients[i] = barrett_reduce_int_vec(a.coefficients[i]);
    }
    a
}

#[inline(always)]
pub(crate) fn subtract_reduce(
    a: &PolynomialRingElement,
    mut b: PolynomialRingElement,
) -> PolynomialRingElement {
    for i in 0..VECS_IN_RING_ELEMENT {
        let coefficient_normal_form =
            montgomery_reduce_int_vec(mul_int_vec_constant(b.coefficients[i], 1441));
        b.coefficients[i] =
            barrett_reduce_int_vec(sub_int_vec(a.coefficients[i], &coefficient_normal_form));
    }
    b
}

#[inline(always)]
pub(crate) fn add_message_error_reduce(
    err: &PolynomialRingElement,
    message: &PolynomialRingElement,
    mut result: PolynomialRingElement,
) -> PolynomialRingElement {
    for i in 0..VECS_IN_RING_ELEMENT {
        let coefficient_normal_form =
            montgomery_reduce_int_vec(mul_int_vec_constant(result.coefficients[i], 1441));
        result.coefficients[i] = barrett_reduce_int_vec(add_int_vec(
            coefficient_normal_form,
            &add_int_vec(err.coefficients[i], &message.coefficients[i]),
        ));
    }
    result
}

#[inline(always)]
pub(crate) fn add_error_reduce(
    err: &PolynomialRingElement,
    mut result: PolynomialRingElement,
) -> PolynomialRingElement {
    for j in 0..VECS_IN_RING_ELEMENT {
        let coefficient_normal_form =
            montgomery_reduce_int_vec(mul_int_vec_constant(result.coefficients[j], 1441));

        result.coefficients[j] =
            barrett_reduce_int_vec(add_int_vec(coefficient_normal_form, &err.coefficients[j]));
    }
    result
}

#[inline(always)]
pub(crate) fn add_standard_error_reduce(
    err: &PolynomialRingElement,
    mut result: PolynomialRingElement,
) -> PolynomialRingElement {
    for j in 0..VECS_IN_RING_ELEMENT {
        // The coefficients are of the form aR^{-1} mod q, which means
        // calling to_montgomery_domain() on them should return a mod q.
        let coefficient_normal_form = to_standard_domain_int_vec(result.coefficients[j]);

        result.coefficients[j] =
            barrett_reduce_int_vec(add_int_vec(coefficient_normal_form, &err.coefficients[j]));
    }
    result
}

const ZETAS_TIMES_MONTGOMERY_R: [FieldElementTimesMontgomeryR; 128] = [
    -1044, -758, -359, -1517, 1493, 1422, 287, 202, -171, 622, 1577, 182, 962, -1202, -1474, 1468,
    573, -1325, 264, 383, -829, 1458, -1602, -130, -681, 1017, 732, 608, -1542, 411, -205, -1571,
    1223, 652, -552, 1015, -1293, 1491, -282, -1544, 516, -8, -320, -666, -1618, -1162, 126, 1469,
    -853, -90, -271, 830, 107, -1421, -247, -951, -398, 961, -1508, -725, 448, -1065, 677, -1275,
    -1103, 430, 555, 843, -1251, 871, 1550, 105, 422, 587, 177, -235, -291, -460, 1574, 1653, -246,
    778, 1159, -147, -777, 1483, -602, 1119, -1590, 644, -872, 349, 418, 329, -156, -75, 817, 1097,
    603, 610, 1322, -1285, -1465, 384, -1215, -136, 1218, -1335, -874, 220, -1187, -1659, -1185,
    -1530, -1278, 794, -1510, -854, -870, 478, -108, -308, 996, 991, 958, -1460, 1522, 1628,
];

/// Represents an intermediate polynomial splitting step in the NTT. All
/// resulting coefficients are in the normal domain since the zetas have been
/// multiplied by MONTGOMERY_R.
#[inline(always)]
pub(crate) fn ntt_at_layer_1(
    zeta_i: &mut usize,
    mut re: PolynomialRingElement,
    _layer: usize,
    _initial_coefficient_bound: usize,
) -> PolynomialRingElement {
    *zeta_i += 1;
    for round in 0..32 {
        re.coefficients[round] = ntt_layer_1_int_vec_step(
            re.coefficients[round],
            ZETAS_TIMES_MONTGOMERY_R[*zeta_i],
            ZETAS_TIMES_MONTGOMERY_R[*zeta_i + 1],
        );
        *zeta_i += 2;
    }
    *zeta_i -= 1;
    re
}

#[inline(always)]
pub(crate) fn ntt_at_layer_2(
    zeta_i: &mut usize,
    mut re: PolynomialRingElement,
    _layer: usize,
    _initial_coefficient_bound: usize,
) -> PolynomialRingElement {
    for round in 0..32 {
        *zeta_i += 1;
        re.coefficients[round] =
            ntt_layer_2_int_vec_step(re.coefficients[round], ZETAS_TIMES_MONTGOMERY_R[*zeta_i]);
    }
    re
}

#[inline(always)]
pub(crate) fn ntt_layer_int_vec_step(
    mut a: IntVec,
    mut b: IntVec,
    zeta_r: i32,
) -> (IntVec, IntVec) {
    let t = montgomery_multiply_fe_by_fer_int_vec(b, zeta_r);
    b = sub_int_vec(a, &t);
    a = add_int_vec(a, &t);
    (a, b)
}

#[inline(always)]
pub(crate) fn ntt_at_layer_3_plus(
    zeta_i: &mut usize,
    mut re: PolynomialRingElement,
    layer: usize,
    _initial_coefficient_bound: usize,
) -> PolynomialRingElement {
    debug_assert!(layer >= 3);
    let step = 1 << layer;

    for round in 0..(128 >> layer) {
        *zeta_i += 1;

        let offset = round * step * 2;
        let offset_vec = offset / SIZE_VEC;
        let step_vec = step / SIZE_VEC;

        for j in offset_vec..offset_vec + step_vec {
            let (x, y) = ntt_layer_int_vec_step(
                re.coefficients[j],
                re.coefficients[j + step_vec],
                ZETAS_TIMES_MONTGOMERY_R[*zeta_i],
            );
            re.coefficients[j] = x;
            re.coefficients[j + step_vec] = y;
        }
    }
    re
}

#[inline(always)]
pub(crate) fn ntt_layer_7_int_vec_step(mut a: IntVec, mut b: IntVec) -> (IntVec, IntVec) {
    let t = mul_int_vec_constant(b, -1600);
    b = sub_int_vec(a, &t);
    a = add_int_vec(a, &t);
    (a, b)
}

#[inline(always)]
pub(crate) fn ntt_at_layer_7(mut re: PolynomialRingElement) -> PolynomialRingElement {
    let step = VECS_IN_RING_ELEMENT / 2;
    for j in 0..step {
        let (x, y) = ntt_layer_7_int_vec_step(re.coefficients[j], re.coefficients[j + step]);
        re.coefficients[j] = x;
        re.coefficients[j + step] = y;
    }
    re
}

#[inline(always)]
pub(crate) fn invert_ntt_at_layer_1(
    zeta_i: &mut usize,
    mut re: PolynomialRingElement,
    _layer: usize,
) -> PolynomialRingElement {
    *zeta_i -= 1;
    for round in 0..32 {
        re.coefficients[round] = inv_ntt_layer_1_int_vec_step(
            re.coefficients[round],
            ZETAS_TIMES_MONTGOMERY_R[*zeta_i],
            ZETAS_TIMES_MONTGOMERY_R[*zeta_i - 1],
        );
        *zeta_i -= 2;
    }
    *zeta_i += 1;
    re
}

#[inline(always)]
pub(crate) fn invert_ntt_at_layer_2(
    zeta_i: &mut usize,
    mut re: PolynomialRingElement,
    _layer: usize,
) -> PolynomialRingElement {
    for round in 0..32 {
        *zeta_i -= 1;
        re.coefficients[round] =
            inv_ntt_layer_2_int_vec_step(re.coefficients[round], ZETAS_TIMES_MONTGOMERY_R[*zeta_i]);
    }
    re
}

#[inline(always)]
pub(crate) fn inv_ntt_layer_int_vec_step(
    mut a: IntVec,
    mut b: IntVec,
    zeta_r: i32,
) -> (IntVec, IntVec) {
    let a_minus_b = sub_int_vec(b, &a);
    a = add_int_vec(a, &b);
    b = montgomery_multiply_fe_by_fer_int_vec(a_minus_b, zeta_r);
    (a, b)
}

#[inline(always)]
pub(crate) fn invert_ntt_at_layer_3_plus(
    zeta_i: &mut usize,
    mut re: PolynomialRingElement,
    layer: usize,
) -> PolynomialRingElement {
    let step = 1 << layer;

    for round in 0..(128 >> layer) {
        *zeta_i -= 1;

        let offset = round * step * 2;
        let offset_vec = offset / SIZE_VEC;
        let step_vec = step / SIZE_VEC;

        for j in offset_vec..offset_vec + step_vec {
            let (x, y) = inv_ntt_layer_int_vec_step(
                re.coefficients[j],
                re.coefficients[j + step_vec],
                ZETAS_TIMES_MONTGOMERY_R[*zeta_i],
            );
            re.coefficients[j] = x;
            re.coefficients[j + step_vec] = y;
        }
    }
    re
}

/// Given two `KyberPolynomialRingElement`s in their NTT representations,
/// compute their product. Given two polynomials in the NTT domain `f^` and `ĵ`,
/// the `iᵗʰ` coefficient of the product `k̂` is determined by the calculation:
///
/// ```plaintext
/// ĥ[2·i] + ĥ[2·i + 1]X = (f^[2·i] + f^[2·i + 1]X)·(ĝ[2·i] + ĝ[2·i + 1]X) mod (X² - ζ^(2·BitRev₇(i) + 1))
/// ```
///
/// This function almost implements <strong>Algorithm 10</strong> of the
/// NIST FIPS 203 standard, which is reproduced below:
///
/// ```plaintext
/// Input: Two arrays fˆ ∈ ℤ₂₅₆ and ĝ ∈ ℤ₂₅₆.
/// Output: An array ĥ ∈ ℤq.
///
/// for(i ← 0; i < 128; i++)
///     (ĥ[2i], ĥ[2i+1]) ← BaseCaseMultiply(fˆ[2i], fˆ[2i+1], ĝ[2i], ĝ[2i+1], ζ^(2·BitRev₇(i) + 1))
/// end for
/// return ĥ
/// ```
/// We say "almost" because the coefficients of the ring element output by
/// this function are in the Montgomery domain.
///
/// The NIST FIPS 203 standard can be found at
/// <https://csrc.nist.gov/pubs/fips/203/ipd>.
// TODO: Remove or replace with something that works and is useful for the proof.
// #[cfg_attr(hax, hax_lib::requires(
//     hax_lib::forall(|i:usize|
//         hax_lib::implies(i < COEFFICIENTS_IN_RING_ELEMENT, ||
//             (lhs.coefficients[i] >= 0 && lhs.coefficients[i] < 4096) &&
//             (rhs.coefficients[i].abs() <= FIELD_MODULUS)

// ))))]
// #[cfg_attr(hax, hax_lib::ensures(|result|
//     hax_lib::forall(|i:usize|
//         hax_lib::implies(i < result.coefficients.len(), ||
//                 result.coefficients[i].abs() <= FIELD_MODULUS
// ))))]
#[inline(always)]
pub(crate) fn ntt_multiply(
    lhs: &PolynomialRingElement,
    rhs: &PolynomialRingElement,
) -> PolynomialRingElement {
    // hax_debug_debug_assert!(lhs
    //     .coefficients
    //     .into_iter()
    //     .all(|coefficient| coefficient >= 0 && coefficient < 4096));

    let mut out = PolynomialRingElement::ZERO();

    for i in 0..VECS_IN_RING_ELEMENT {
        out.coefficients[i] = ntt_multiply_int_vec(
            &lhs.coefficients[i],
            &rhs.coefficients[i],
            ZETAS_TIMES_MONTGOMERY_R[64 + 2 * i],
            ZETAS_TIMES_MONTGOMERY_R[64 + 2 * i + 1],
        );
    }

    out
}
