use crate::*;

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
pub fn ntt_binomially_sampled_ring_element(mut re: PolynomialRingElement) -> PolynomialRingElement {
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

    re = poly_barrett_reduce(re);

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
pub fn ntt_vector_u<const VECTOR_U_COMPRESSION_FACTOR: usize>(
    mut re: PolynomialRingElement,
) -> PolynomialRingElement {
    let mut zeta_i = 0;

    re = ntt_at_layer_3_plus(&mut zeta_i, re, 7, 3328);
    re = ntt_at_layer_3_plus(&mut zeta_i, re, 6, 3328);
    re = ntt_at_layer_3_plus(&mut zeta_i, re, 5, 3328);
    re = ntt_at_layer_3_plus(&mut zeta_i, re, 4, 3328);
    re = ntt_at_layer_3_plus(&mut zeta_i, re, 3, 3328);
    re = ntt_at_layer_2(&mut zeta_i, re, 2, 3328);
    re = ntt_at_layer_1(&mut zeta_i, re, 1, 3328);

    re = poly_barrett_reduce(re);
    re
}

/// Use the Gentleman-Sande butterfly to invert, in-place, the NTT representation
/// of a `KyberPolynomialRingElement`. The coefficients of the output
/// ring element are in the Montgomery domain.
#[inline(always)]
pub fn invert_ntt_montgomery<const K: usize>(
    mut re: PolynomialRingElement,
) -> PolynomialRingElement {
    // We only ever call this function after matrix/vector multiplication

    let mut zeta_i = COEFFICIENTS_IN_RING_ELEMENT / 2;

    re = invert_ntt_at_layer_1(&mut zeta_i, re, 1);
    re = invert_ntt_at_layer_2(&mut zeta_i, re, 2);
    re = invert_ntt_at_layer_3_plus(&mut zeta_i, re, 3);
    re = invert_ntt_at_layer_3_plus(&mut zeta_i, re, 4);
    re = invert_ntt_at_layer_3_plus(&mut zeta_i, re, 5);
    re = invert_ntt_at_layer_3_plus(&mut zeta_i, re, 6);
    re = invert_ntt_at_layer_3_plus(&mut zeta_i, re, 7);

    re = poly_barrett_reduce(re);
    re
}
