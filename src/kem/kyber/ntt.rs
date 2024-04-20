use crate::hax_utils::hax_debug_assert;

use super::{
    polynomial::{
        poly_barrett_reduce, to_i32_array, ntt_at_layer, ntt_at_layer_7, invert_ntt_at_layer, PolynomialRingElement,
    },
    constants::{COEFFICIENTS_IN_RING_ELEMENT, FIELD_MODULUS},
};

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
#[cfg_attr(hax, hax_lib_macros::requires(
    hax_lib::forall(|i:usize|
        hax_lib::implies(i < re.coefficients.len(), || re.coefficients[i].abs() <= 3
))))]
#[cfg_attr(hax, hax_lib_macros::ensures(|result|
    hax_lib::forall(|i:usize|
        hax_lib::implies(i < result.coefficients.len(), ||
            result.coefficients[i].abs() < FIELD_MODULUS
))))]
#[inline(always)]
pub(in crate::kem::kyber) fn ntt_binomially_sampled_ring_element(
    mut re: PolynomialRingElement,
) -> PolynomialRingElement {
    // Due to the small coefficient bound, we can skip the first round of
    // Montgomery reductions.
    re = ntt_at_layer_7(re);
    let mut zeta_i = 1;
    re = ntt_at_layer_3(&mut zeta_i, re, 6);
    re = ntt_at_layer_3(&mut zeta_i, re, 5);
    re = ntt_at_layer_3(&mut zeta_i, re, 4);
    re = ntt_at_layer_3(&mut zeta_i, re, 3);
    re = ntt_at_layer_3(&mut zeta_i, re, 2);
    re = ntt_at_layer_3(&mut zeta_i, re, 1);

    re = poly_barrett_reduce(re);

    re
}

/// Use the Cooley–Tukey butterfly to compute an in-place NTT representation
/// of a `KyberPolynomialRingElement`.
///
/// This function operates on the ring element that partly constitutes
/// the ciphertext.
#[cfg_attr(hax, hax_lib_macros::requires(
    hax_lib::forall(|i:usize|
        hax_lib::implies(i < re.coefficients.len(), || re.coefficients[i].abs() <= 3328
))))]
#[cfg_attr(hax, hax_lib_macros::ensures(|result|
    hax_lib::forall(|i:usize|
        hax_lib::implies(i < result.coefficients.len(), ||
            result.coefficients[i].abs() < FIELD_MODULUS
))))]
#[inline(always)]
pub(in crate::kem::kyber) fn ntt_vector_u<const VECTOR_U_COMPRESSION_FACTOR: usize>(
    mut re: PolynomialRingElement,
) -> PolynomialRingElement {
    hax_debug_assert!(to_i32_array(re)
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

    re = poly_barrett_reduce(re);
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
    hax_debug_assert!(to_i32_array(re)
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
        to_i32_array(re)[0].abs() < 128 * (K as i32) * FIELD_MODULUS
            && to_i32_array(re)[1].abs() < 128 * (K as i32) * FIELD_MODULUS
    );
    hax_debug_assert!(to_i32_array(re)
        .into_iter()
        .enumerate()
        .skip(2)
        .all(|(i, coefficient)| coefficient.abs() < (128 / (1 << i.ilog2())) * FIELD_MODULUS));

    re = poly_barrett_reduce(re);
    re
}
