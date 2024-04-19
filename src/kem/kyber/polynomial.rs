use crate::hax_utils::hax_debug_assert;
use super::arithmetic::*;
use super::constants::{COEFFICIENTS_IN_RING_ELEMENT, FIELD_MODULUS};

#[derive(Clone, Copy)]
pub struct PolynomialRingElement {
    coefficients: [FieldElement; COEFFICIENTS_IN_RING_ELEMENT],
}

impl PolynomialRingElement {
    pub(crate) const ZERO: Self = Self {
        coefficients: [0i32; 256], // FIXME: hax issue, this is COEFFICIENTS_IN_RING_ELEMENT
    };
}

/// Given two polynomial ring elements `lhs` and `rhs`, compute the pointwise
/// sum of their constituent coefficients.
#[cfg_attr(hax, hax_lib_macros::requires(
    hax_lib::forall(|i:usize|
        hax_lib::implies(i < COEFFICIENTS_IN_RING_ELEMENT, ||
            (lhs.coefficients[i].abs() <= ((K as i32) - 1) * FIELD_MODULUS) &&
            (rhs.coefficients[i].abs() <= FIELD_MODULUS)

))))]
#[cfg_attr(hax, hax_lib_macros::ensures(|result|
    hax_lib::forall(|i:usize|
        hax_lib::implies(i < result.coefficients.len(), ||
                result.coefficients[i].abs() <= (K as i32) * FIELD_MODULUS
))))]
pub(crate) fn add_to_ring_element<const K: usize>(
    mut lhs: PolynomialRingElement,
    rhs: &PolynomialRingElement,
) -> PolynomialRingElement {
    hax_debug_assert!(lhs
        .coefficients
        .into_iter()
        .all(|coefficient| coefficient.abs() <= ((K as i32) - 1) * FIELD_MODULUS));
    hax_debug_assert!(rhs
        .coefficients
        .into_iter()
        .all(|coefficient| coefficient.abs() < FIELD_MODULUS));

    for i in 0..lhs.coefficients.len() {
        lhs.coefficients[i] += rhs.coefficients[i];
    }

    hax_debug_assert!(lhs
        .coefficients
        .into_iter()
        .all(|coefficient| coefficient.abs() <= (K as i32) * FIELD_MODULUS));

    lhs
}

pub(crate) fn poly_barrett_reduce(mut a:PolynomialRingElement) -> PolynomialRingElement {
    for i in 0..COEFFICIENTS_IN_RING_ELEMENT {
        a.coefficients[i] = barrett_reduce(a.coefficients[i]);
    }
    a
}

pub(crate) fn subtract_reduce(a:&PolynomialRingElement, mut b:PolynomialRingElement) -> PolynomialRingElement {
    for i in 0..COEFFICIENTS_IN_RING_ELEMENT {
        let coefficient_normal_form = montgomery_reduce(b.coefficients[i] * 1441);
        b.coefficients[i] = barrett_reduce(a.coefficients[i] - coefficient_normal_form);
    }
    b
}

pub(crate) fn add_message_error_reduce(err:&PolynomialRingElement, message:&PolynomialRingElement, mut result:PolynomialRingElement) -> PolynomialRingElement {
    for i in 0..COEFFICIENTS_IN_RING_ELEMENT {
        let coefficient_normal_form = montgomery_reduce(result.coefficients[i] * 1441);
        result.coefficients[i] = barrett_reduce(
            coefficient_normal_form + err.coefficients[i] + message.coefficients[i],
        );
    }
    result
}

pub(crate) fn add_error_reduce(err:&PolynomialRingElement, mut result:PolynomialRingElement) -> PolynomialRingElement {
    for j in 0..COEFFICIENTS_IN_RING_ELEMENT {
        let coefficient_normal_form = montgomery_reduce(result.coefficients[j] * 1441);

        result.coefficients[j] =
            barrett_reduce(coefficient_normal_form + err.coefficients[j]);
    }
    result
}

pub(crate) fn add_standard_error_reduce(err:&PolynomialRingElement, mut result:PolynomialRingElement) -> PolynomialRingElement {
    for j in 0..COEFFICIENTS_IN_RING_ELEMENT {
        // The coefficients are of the form aR^{-1} mod q, which means
        // calling to_montgomery_domain() on them should return a mod q.
        let coefficient_normal_form = to_standard_domain(result.coefficients[j]);

        result.coefficients[j] =
            barrett_reduce(coefficient_normal_form + err.coefficients[j])
    }
    result
}

pub(crate) fn to_i32_array(a:PolynomialRingElement) -> [i32;256] {
    a.coefficients
}


pub(crate) fn from_i32_array(a:[i32;256]) -> PolynomialRingElement {
    PolynomialRingElement {coefficients: a}
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
pub(crate) fn ntt_at_layer(
    zeta_i: &mut usize,
    mut re: PolynomialRingElement,
    layer: usize,
    _initial_coefficient_bound: usize,
) -> PolynomialRingElement {
    let step = 1 << layer;

    for round in 0..(128 >> layer) {
        *zeta_i += 1;

        let offset = round * step * 2;

        for j in offset..offset + step {
            let t = montgomery_multiply_fe_by_fer(
                re.coefficients[j + step],
                ZETAS_TIMES_MONTGOMERY_R[*zeta_i],
            );
            re.coefficients[j + step] = re.coefficients[j] - t;
            re.coefficients[j] = re.coefficients[j] + t;
        }
    }

    hax_debug_assert!(re.coefficients.into_iter().all(|coefficient| {
        coefficient.abs()
            < _initial_coefficient_bound as i32 + ((8 - layer as i32) * ((3 * FIELD_MODULUS) / 2))
    }));

    re
}

#[inline(always)]
pub(crate) fn ntt_at_layer_7(
    zeta_i: &mut usize,
    mut re: PolynomialRingElement,
) -> PolynomialRingElement {
    hax_debug_assert!(re
        .coefficients
        .into_iter()
        .all(|coefficient| coefficient.abs() <= 3));


    for j in 0..128 {
        // Multiply by the appropriate zeta in the normal domain.
        let t = re.coefficients[j + 128] * -1600;

        re.coefficients[j + 128] = re.coefficients[j] - t;
        re.coefficients[j] = re.coefficients[j] + t;
    }

    hax_debug_assert!(re
        .coefficients
        .into_iter()
        .all(|coefficient| { coefficient.abs() < 3 + ((3 * FIELD_MODULUS) / 2) }));

    re
}

#[inline(always)]
pub(crate) fn invert_ntt_at_layer(
    zeta_i: &mut usize,
    mut re: PolynomialRingElement,
    layer: usize,
) -> PolynomialRingElement {
    let step = 1 << layer;

    for round in 0..(128 >> layer) {
        *zeta_i -= 1;

        let offset = round * step * 2;

        for j in offset..offset + step {
            let a_minus_b = re.coefficients[j + step] - re.coefficients[j];

            // Instead of dividing by 2 here, we just divide by
            // 2^7 in one go in the end.
            re.coefficients[j] = re.coefficients[j] + re.coefficients[j + step];
            re.coefficients[j + step] =
                montgomery_reduce(a_minus_b * ZETAS_TIMES_MONTGOMERY_R[*zeta_i]);
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
#[cfg_attr(hax, hax_lib_macros::requires(
    hax_lib::forall(|i:usize|
        hax_lib::implies(i < COEFFICIENTS_IN_RING_ELEMENT, ||
            (lhs.coefficients[i] >= 0 && lhs.coefficients[i] < 4096) &&
            (rhs.coefficients[i].abs() <= FIELD_MODULUS)

))))]
#[cfg_attr(hax, hax_lib_macros::ensures(|result|
    hax_lib::forall(|i:usize|
        hax_lib::implies(i < result.coefficients.len(), ||
                result.coefficients[i].abs() <= FIELD_MODULUS
))))]
#[inline(always)]
pub(crate) fn ntt_multiply(
    lhs: &PolynomialRingElement,
    rhs: &PolynomialRingElement,
) -> PolynomialRingElement {
    hax_debug_assert!(lhs
        .coefficients
        .into_iter()
        .all(|coefficient| coefficient >= 0 && coefficient < 4096));

    let mut out = PolynomialRingElement::ZERO;

    for i in 0..(COEFFICIENTS_IN_RING_ELEMENT / 4) {
        let product = ntt_multiply_binomials(
            (lhs.coefficients[4 * i], lhs.coefficients[4 * i + 1]),
            (rhs.coefficients[4 * i], rhs.coefficients[4 * i + 1]),
            ZETAS_TIMES_MONTGOMERY_R[64 + i],
        );
        out.coefficients[4 * i] = product.0;
        out.coefficients[4 * i + 1] = product.1;

        let product = ntt_multiply_binomials(
            (lhs.coefficients[4 * i + 2], lhs.coefficients[4 * i + 3]),
            (rhs.coefficients[4 * i + 2], rhs.coefficients[4 * i + 3]),
            -ZETAS_TIMES_MONTGOMERY_R[64 + i],
        );
        out.coefficients[4 * i + 2] = product.0;
        out.coefficients[4 * i + 3] = product.1;
    }

    out
}
