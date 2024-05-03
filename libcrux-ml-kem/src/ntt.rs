use libcrux_polynomials::Operations;

use crate::hax_utils::hax_debug_assert;

use crate::{
    constants::COEFFICIENTS_IN_RING_ELEMENT,
    polynomial::{
        invert_ntt_at_layer_1, invert_ntt_at_layer_2, invert_ntt_at_layer_3_plus, ntt_at_layer_1,
        ntt_at_layer_2, ntt_at_layer_3_plus, ntt_at_layer_7, 
        PolynomialRingElement,
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
pub(crate) fn ntt_binomially_sampled_ring_element<Vector: Operations>(
    mut re: PolynomialRingElement<Vector>,
) -> PolynomialRingElement<Vector> {
    // Due to the small coefficient bound, we can skip the first round of
    // Montgomery reductions.
    re = ntt_at_layer_7(re);
    let mut zeta_i = 1;
    re = ntt_at_layer_3_plus(&mut zeta_i, re, 6, 3);
    re = ntt_at_layer_3_plus(&mut zeta_i, re, 5, 3);
    re = ntt_at_layer_3_plus(&mut zeta_i, re, 4, 3);
    re = ntt_at_layer_3_plus(&mut zeta_i, re, 3, 3);
    re = ntt_at_layer_2(&mut zeta_i, re, 2, 3);
    re = ntt_at_layer_1(&mut zeta_i, re, 1, 3);

    re.poly_barrett_reduce()
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
pub(crate) fn ntt_vector_u<const VECTOR_U_COMPRESSION_FACTOR: usize, Vector: Operations>(
    mut re: PolynomialRingElement<Vector>,
) -> PolynomialRingElement<Vector> {
    hax_debug_assert!(to_i32_array(re)
        .into_iter()
        .all(|coefficient| coefficient.abs() <= 3328));

    let mut zeta_i = 0;

    re = ntt_at_layer_3_plus(&mut zeta_i, re, 7, 3328);
    re = ntt_at_layer_3_plus(&mut zeta_i, re, 6, 3328);
    re = ntt_at_layer_3_plus(&mut zeta_i, re, 5, 3328);
    re = ntt_at_layer_3_plus(&mut zeta_i, re, 4, 3328);
    re = ntt_at_layer_3_plus(&mut zeta_i, re, 3, 3328);
    re = ntt_at_layer_2(&mut zeta_i, re, 2, 3328);
    re = ntt_at_layer_1(&mut zeta_i, re, 1, 3328);

    re.poly_barrett_reduce()
}

/// Use the Gentleman-Sande butterfly to invert, in-place, the NTT representation
/// of a `KyberPolynomialRingElement`. The coefficients of the output
/// ring element are in the Montgomery domain.
#[inline(always)]
pub(crate) fn invert_ntt_montgomery<const K: usize, Vector: Operations>(
    mut re: PolynomialRingElement<Vector>,
) -> PolynomialRingElement<Vector> {
    // We only ever call this function after matrix/vector multiplication
    hax_debug_assert!(to_i32_array(re)
        .into_iter()
        .all(|coefficient| coefficient.abs() < (K as i32) * FIELD_MODULUS));

    let mut zeta_i = COEFFICIENTS_IN_RING_ELEMENT / 2;

    re = invert_ntt_at_layer_1(&mut zeta_i, re, 1);
    re = invert_ntt_at_layer_2(&mut zeta_i, re, 2);
    re = invert_ntt_at_layer_3_plus(&mut zeta_i, re, 3);
    re = invert_ntt_at_layer_3_plus(&mut zeta_i, re, 4);
    re = invert_ntt_at_layer_3_plus(&mut zeta_i, re, 5);
    re = invert_ntt_at_layer_3_plus(&mut zeta_i, re, 6);
    re = invert_ntt_at_layer_3_plus(&mut zeta_i, re, 7);

    hax_debug_assert!(
        to_i32_array(re)[0].abs() < 128 * (K as i32) * FIELD_MODULUS
            && to_i32_array(re)[1].abs() < 128 * (K as i32) * FIELD_MODULUS
    );
    hax_debug_assert!(to_i32_array(re)
        .into_iter()
        .enumerate()
        .skip(2)
        .all(|(i, coefficient)| coefficient.abs() < (128 / (1 << i.ilog2())) * FIELD_MODULUS));

    re.poly_barrett_reduce()
}
