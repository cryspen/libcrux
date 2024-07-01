use crate::hax_utils::hax_debug_assert;

use super::{
    arithmetic::{
        barrett_reduce, montgomery_multiply_fe_by_fer, montgomery_reduce, FieldElement,
        FieldElementTimesMontgomeryR, MontgomeryFieldElement, PolynomialRingElement,
    },
    constants::COEFFICIENTS_IN_RING_ELEMENT,
};
#[cfg(hax)]
use crate::kem::kyber::constants::FIELD_MODULUS;

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
fn ntt_at_layer(
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

/// See [`ntt_at_layer`].
#[inline(always)]
fn ntt_at_layer_3(
    zeta_i: &mut usize,
    re: PolynomialRingElement,
    layer: usize,
) -> PolynomialRingElement {
    ntt_at_layer(zeta_i, re, layer, 3)
}

/// See [`ntt_at_layer`].
#[inline(always)]
fn ntt_at_layer_3328(
    zeta_i: &mut usize,
    re: PolynomialRingElement,
    layer: usize,
) -> PolynomialRingElement {
    ntt_at_layer(zeta_i, re, layer, 3328)
}

/// Use the Cooley–Tukey butterfly to compute an in-place NTT representation
/// of a `KyberPolynomialRingElement`.
///
/// This function operates only on those which were produced by binomial
/// sampling, and thus those which have small coefficients. The small
/// coefficients let us skip the first round of Montgomery reductions.
#[cfg_attr(hax, hax_lib::requires(
    hax_lib::forall(|i:usize|
        hax_lib::implies(i < re.coefficients.len(), || re.coefficients[i].abs() <= 3
))))]
#[cfg_attr(hax, hax_lib::ensures(|result|
    hax_lib::forall(|i:usize|
        hax_lib::implies(i < result.coefficients.len(), ||
            result.coefficients[i].abs() < FIELD_MODULUS
))))]
#[inline(always)]
pub(in crate::kem::kyber) fn ntt_binomially_sampled_ring_element(
    mut re: PolynomialRingElement,
) -> PolynomialRingElement {
    hax_debug_assert!(re
        .coefficients
        .into_iter()
        .all(|coefficient| coefficient.abs() <= 3));

    // Due to the small coefficient bound, we can skip the first round of
    // Montgomery reductions.
    let mut zeta_i = 1;

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

    re = ntt_at_layer_3(&mut zeta_i, re, 6);
    re = ntt_at_layer_3(&mut zeta_i, re, 5);
    re = ntt_at_layer_3(&mut zeta_i, re, 4);
    re = ntt_at_layer_3(&mut zeta_i, re, 3);
    re = ntt_at_layer_3(&mut zeta_i, re, 2);
    re = ntt_at_layer_3(&mut zeta_i, re, 1);

    for i in 0..COEFFICIENTS_IN_RING_ELEMENT {
        re.coefficients[i] = barrett_reduce(re.coefficients[i]);
    }

    re
}

/// Use the Cooley–Tukey butterfly to compute an in-place NTT representation
/// of a `KyberPolynomialRingElement`.
///
/// This function operates on the ring element that partly constitutes
/// the ciphertext.
#[cfg_attr(hax, hax_lib::requires(
    hax_lib::forall(|i:usize|
        hax_lib::implies(i < re.coefficients.len(), || re.coefficients[i].abs() <= 3328
))))]
#[cfg_attr(hax, hax_lib::ensures(|result|
    hax_lib::forall(|i:usize|
        hax_lib::implies(i < result.coefficients.len(), ||
            result.coefficients[i].abs() < FIELD_MODULUS
))))]
#[inline(always)]
pub(in crate::kem::kyber) fn ntt_vector_u<const VECTOR_U_COMPRESSION_FACTOR: usize>(
    mut re: PolynomialRingElement,
) -> PolynomialRingElement {
    hax_debug_assert!(re
        .coefficients
        .into_iter()
        .all(|coefficient| coefficient.abs() <= 3328));

    let mut zeta_i = 0;

    re = ntt_at_layer_3328(&mut zeta_i, re, 7);
    re = ntt_at_layer_3328(&mut zeta_i, re, 6);
    re = ntt_at_layer_3328(&mut zeta_i, re, 5);
    re = ntt_at_layer_3328(&mut zeta_i, re, 4);
    re = ntt_at_layer_3328(&mut zeta_i, re, 3);
    re = ntt_at_layer_3328(&mut zeta_i, re, 2);
    re = ntt_at_layer_3328(&mut zeta_i, re, 1);

    for i in 0..COEFFICIENTS_IN_RING_ELEMENT {
        re.coefficients[i] = barrett_reduce(re.coefficients[i]);
    }

    re
}

#[inline(always)]
fn invert_ntt_at_layer(
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

/// Use the Gentleman-Sande butterfly to invert, in-place, the NTT representation
/// of a `KyberPolynomialRingElement`. The coefficients of the output
/// ring element are in the Montgomery domain.
#[inline(always)]
pub(crate) fn invert_ntt_montgomery<const K: usize>(
    mut re: PolynomialRingElement,
) -> PolynomialRingElement {
    // We only ever call this function after matrix/vector multiplication
    hax_debug_assert!(re
        .coefficients
        .into_iter()
        .all(|coefficient| coefficient.abs() < (K as i32) * FIELD_MODULUS));

    let mut zeta_i = COEFFICIENTS_IN_RING_ELEMENT / 2;

    re = invert_ntt_at_layer(&mut zeta_i, re, 1);
    re = invert_ntt_at_layer(&mut zeta_i, re, 2);
    re = invert_ntt_at_layer(&mut zeta_i, re, 3);
    re = invert_ntt_at_layer(&mut zeta_i, re, 4);
    re = invert_ntt_at_layer(&mut zeta_i, re, 5);
    re = invert_ntt_at_layer(&mut zeta_i, re, 6);
    re = invert_ntt_at_layer(&mut zeta_i, re, 7);

    hax_debug_assert!(
        re.coefficients[0].abs() < 128 * (K as i32) * FIELD_MODULUS
            && re.coefficients[1].abs() < 128 * (K as i32) * FIELD_MODULUS
    );
    hax_debug_assert!(re
        .coefficients
        .into_iter()
        .enumerate()
        .skip(2)
        .all(|(i, coefficient)| coefficient.abs() < (128 / (1 << i.ilog2())) * FIELD_MODULUS));

    for i in 0..2 {
        re.coefficients[i] = barrett_reduce(re.coefficients[i]);
    }
    re
}

/// Compute the product of two Kyber binomials with respect to the
/// modulus `X² - zeta`.
///
/// This function almost implements <strong>Algorithm 11</strong> of the
/// NIST FIPS 203 standard, which is reproduced below:
///
/// ```plaintext
/// Input:  a₀, a₁, b₀, b₁ ∈ ℤq.
/// Input: γ ∈ ℤq.
/// Output: c₀, c₁ ∈ ℤq.
///
/// c₀ ← a₀·b₀ + a₁·b₁·γ
/// c₁ ← a₀·b₁ + a₁·b₀
/// return c₀, c₁
/// ```
/// We say "almost" because the coefficients output by this function are in
/// the Montgomery domain (unlike in the specification).
///
/// The NIST FIPS 203 standard can be found at
/// <https://csrc.nist.gov/pubs/fips/203/ipd>.
#[inline(always)]
fn ntt_multiply_binomials(
    (a0, a1): (FieldElement, FieldElement),
    (b0, b1): (FieldElement, FieldElement),
    zeta: FieldElementTimesMontgomeryR,
) -> (MontgomeryFieldElement, MontgomeryFieldElement) {
    (
        montgomery_reduce(a0 * b0 + montgomery_reduce(a1 * b1) * zeta),
        montgomery_reduce(a0 * b1 + a1 * b0),
    )
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
#[cfg_attr(hax, hax_lib::requires(
    hax_lib::forall(|i:usize|
        hax_lib::implies(i < COEFFICIENTS_IN_RING_ELEMENT, ||
            (lhs.coefficients[i] >= 0 && lhs.coefficients[i] < 4096) &&
            (rhs.coefficients[i].abs() <= FIELD_MODULUS)

))))]
#[cfg_attr(hax, hax_lib::ensures(|result|
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
