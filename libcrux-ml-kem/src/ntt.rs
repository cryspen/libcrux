//use crate::hax_utils::debug_assert;

use crate::{
    constants::{COEFFICIENTS_IN_RING_ELEMENT, FIELD_MODULUS},
    polynomial::{
        invert_ntt_at_layer_1, invert_ntt_at_layer_2, invert_ntt_at_layer_3_plus,
        invert_ntt_at_layer_3_plus_reduce, ntt_at_layer_1, ntt_at_layer_2, ntt_at_layer_3_plus,
        ntt_at_layer_7, poly_barrett_reduce, to_i16_array, PolynomialRingElement,
    },
};

/// Use the Cooley–Tukey butterfly to compute an in-place NTT representation
/// of a `KyberPolynomialRingElement`.
///
/// This function operates only on those which were produced by binomial
/// sampling, and thus those which have small coefficients. The small
/// coefficients let us skip the first round of Montgomery reductions.
// TODO: Remove or replace with something that works and is useful for the proof.
// #[cfg_attr(hax, hax_lib::requires(
//     hax_lib::forall(|i:usize|
//         hax_lib::implies(i < re.coefficients.len(), || re.coefficients[i].abs() <= 3
// ))))]
// #[cfg_attr(hax, hax_lib::ensures(|result|
//     hax_lib::forall(|i:usize|
//         hax_lib::implies(i < result.coefficients.len(), ||
//             result.coefficients[i].abs() < FIELD_MODULUS
// ))))]
#[inline(always)]
pub(crate) fn ntt_binomially_sampled_ring_element(
    mut re: PolynomialRingElement,
) -> PolynomialRingElement {
    // Due to the small coefficient bound, we can skip the first round of
    // Montgomery reductions.

    // re <= 3
    re = ntt_at_layer_7(re); // re <= 4803
    let mut zeta_i = 1;
    re = ntt_at_layer_3_plus(&mut zeta_i, re, 6, 3); // re <= 4803 + 3328
    re = ntt_at_layer_3_plus(&mut zeta_i, re, 5, 3); // re <= 4803 + 2*3328
    re = ntt_at_layer_3_plus(&mut zeta_i, re, 4, 3); // re <= 4803 + 3*3328
    re = ntt_at_layer_3_plus(&mut zeta_i, re, 3, 3); // re <= 4803 + 4*3328
    re = ntt_at_layer_2(&mut zeta_i, re, 2, 3); // re <= 4803 + 5*3328
    re = ntt_at_layer_1(&mut zeta_i, re, 1, 3); // re <= 4803 + 6*3328

    re = poly_barrett_reduce(re); // re <= 3328

    re
}

/// Use the Cooley–Tukey butterfly to compute an in-place NTT representation
/// of a `KyberPolynomialRingElement`.
///
/// This function operates on the ring element that partly constitutes
/// the ciphertext.
// TODO: Remove or replace with something that works and is useful for the proof.
// #[cfg_attr(hax, hax_lib::requires(
//     hax_lib::forall(|i:usize|
//         hax_lib::implies(i < re.coefficients.len(), || re.coefficients[i].abs() <= 3328
// ))))]
// #[cfg_attr(hax, hax_lib::ensures(|result|
//     hax_lib::forall(|i:usize|
//         hax_lib::implies(i < result.coefficients.len(), ||
//             result.coefficients[i].abs() < FIELD_MODULUS
// ))))]
#[inline(always)]
pub(crate) fn ntt_vector_u<const VECTOR_U_COMPRESSION_FACTOR: usize>(
    mut re: PolynomialRingElement,
) -> PolynomialRingElement {
    debug_assert!(to_i16_array(re)
        .into_iter()
        .all(|coefficient| coefficient.abs() <= 3328));

    let mut zeta_i = 0;

    // re <= 3328
    re = ntt_at_layer_3_plus(&mut zeta_i, re, 7, 3328); // re <= 2 * 3328
    re = ntt_at_layer_3_plus(&mut zeta_i, re, 6, 3328); // re <= 3 * 3328
    re = ntt_at_layer_3_plus(&mut zeta_i, re, 5, 3328); // re <= 4 * 3328
    re = ntt_at_layer_3_plus(&mut zeta_i, re, 4, 3328); // re <= 5 * 3328
    re = ntt_at_layer_3_plus(&mut zeta_i, re, 3, 3328); // re <= 6 * 3328
    re = ntt_at_layer_2(&mut zeta_i, re, 2, 3328); // re <= 7 * 3328
    re = ntt_at_layer_1(&mut zeta_i, re, 1, 3328); // re <= 8 * 3328

    re = poly_barrett_reduce(re); // re <= 3328
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
    debug_assert!(to_i16_array(re)
        .into_iter()
        .all(|coefficient| coefficient.abs() < (K as i16 * FIELD_MODULUS)));

    let mut zeta_i = COEFFICIENTS_IN_RING_ELEMENT / 2;

    // re <= K * 3328
    re = invert_ntt_at_layer_1(&mut zeta_i, re, 1); // re <= 3328  (reduces)
    re = invert_ntt_at_layer_2(&mut zeta_i, re, 2); // re <= 2 * 3328 (does not reduce)
    re = invert_ntt_at_layer_3_plus_reduce(&mut zeta_i, re, 3); // re <= 4 * 3328 (need not reduce)
    re = invert_ntt_at_layer_3_plus_reduce(&mut zeta_i, re, 4); // re <= 3328 (should reduce)
    re = invert_ntt_at_layer_3_plus(&mut zeta_i, re, 5); // re <= 2*3328 (need not reduce)
    re = invert_ntt_at_layer_3_plus(&mut zeta_i, re, 6); // re <= 4*3328 (need not reduce)
    re = invert_ntt_at_layer_3_plus(&mut zeta_i, re, 7); // re <= 8*3328 (need not reduce)

    re = poly_barrett_reduce(re); // re <= 3328 (reduces)
    re
}
