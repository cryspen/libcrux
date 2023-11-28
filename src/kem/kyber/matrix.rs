use super::{
    arithmetic::{
        add_to_ring_element, barrett_reduce, montgomery_reduce, to_standard_domain,
        PolynomialRingElement,
    },
    constants::COEFFICIENTS_IN_RING_ELEMENT,
    ntt::{invert_ntt_montgomery, ntt_multiply},
};

/// This file contains functions that compute various expressions involving
/// vectors and matrices. The computation of these expressions has been
/// abstracted away into these functions in order to save on loop iterations.

/// Compute v − NTT^{−1}(sˆT ◦ NTT(u))
#[inline(always)]
pub(in crate::kem::kyber) fn compute_message<const K: usize>(
    v: &PolynomialRingElement,
    secret_as_ntt: &[PolynomialRingElement; K],
    u_as_ntt: &[PolynomialRingElement; K],
) -> PolynomialRingElement {
    let mut result = PolynomialRingElement::ZERO;

    for i in 0..K {
        let product = ntt_multiply(&secret_as_ntt[i], &u_as_ntt[i]);
        add_to_ring_element::<K>(&mut result, &product);
    }

    invert_ntt_montgomery::<K>(&mut result);

    for i in 0..COEFFICIENTS_IN_RING_ELEMENT {
        let coefficient_normal_form = montgomery_reduce(result.coefficients[i] * 1441);
        result.coefficients[i] = barrett_reduce(v.coefficients[i] - coefficient_normal_form);
    }

    result
}

/// Compute NTT^{−1}(tˆT ◦ rˆ) + e_2 + Decompress_q(Decode_1(m),1)
#[inline(always)]
pub(in crate::kem::kyber) fn compute_ring_element_v<const K: usize>(
    t_as_ntt: &[PolynomialRingElement; K],
    r_as_ntt: &[PolynomialRingElement; K],
    error_2: &PolynomialRingElement,
    message: &PolynomialRingElement,
) -> PolynomialRingElement {
    let mut result = PolynomialRingElement::ZERO;

    for i in 0..K {
        let product = ntt_multiply(&t_as_ntt[i], &r_as_ntt[i]);
        add_to_ring_element::<K>(&mut result, &product);
    }

    invert_ntt_montgomery::<K>(&mut result);

    for i in 0..COEFFICIENTS_IN_RING_ELEMENT {
        let coefficient_normal_form = montgomery_reduce(result.coefficients[i] * 1441);
        result.coefficients[i] = barrett_reduce(
            coefficient_normal_form + error_2.coefficients[i] + message.coefficients[i],
        );
    }

    result
}

/// Compute u := NTT^{-1}(AˆT ◦ rˆ) + e_1
#[inline(always)]
pub(in crate::kem::kyber) fn compute_vector_u<const K: usize>(
    a_as_ntt: &[[PolynomialRingElement; K]; K],
    r_as_ntt: &[PolynomialRingElement; K],
    error_1: &[PolynomialRingElement; K],
) -> [PolynomialRingElement; K] {
    let mut result = [PolynomialRingElement::ZERO; K];

    // for (i, row) in a_as_ntt.iter().enumerate() {
    for i in 0..a_as_ntt.len() {
        let row = &a_as_ntt[i];
        // for (j, a_element) in row.iter().enumerate() {
        for j in 0..row.len() {
            let a_element = &row[j];
            let product = ntt_multiply(a_element, &r_as_ntt[j]);
            add_to_ring_element::<K>(&mut result[i], &product);
        }

        invert_ntt_montgomery::<K>(&mut result[i]);

        for j in 0..COEFFICIENTS_IN_RING_ELEMENT {
            let result_i = &result[i];
            let error_1_i = &error_1[i];

            let coefficient_normal_form = montgomery_reduce(result_i.coefficients[j] * 1441);

            result[i].coefficients[j] =
                barrett_reduce(coefficient_normal_form + error_1_i.coefficients[j]);
        }
    }

    result
}

/// compute Aˆ ◦ sˆ + eˆ
#[inline(always)]
#[allow(non_snake_case)]
pub(in crate::kem::kyber) fn compute_As_plus_e<const K: usize>(
    matrix_A: &[[PolynomialRingElement; K]; K],
    s_as_ntt: &[PolynomialRingElement; K],
    error_as_ntt: &[PolynomialRingElement; K],
) -> [PolynomialRingElement; K] {
    let mut result = [PolynomialRingElement::ZERO; K];

    // for (i, row) in matrix_A.iter().enumerate() {
    for i in 0..matrix_A.len() {
        let row = &matrix_A[i];
        // for (j, matrix_element) in row.iter().enumerate() {
        for j in 0..row.len() {
            let matrix_element = &row[j];
            let product = ntt_multiply(matrix_element, &s_as_ntt[j]);
            add_to_ring_element::<K>(&mut result[i], &product);
        }

        for j in 0..COEFFICIENTS_IN_RING_ELEMENT {
            let result_i = &result[i];
            let error_as_ntt_i = &error_as_ntt[i];

            // The coefficients are of the form aR^{-1} mod q, which means
            // calling to_montgomery_domain() on them should return a mod q.
            let coefficient_normal_form = to_standard_domain(result_i.coefficients[j]);

            result[i].coefficients[j] =
                barrett_reduce(coefficient_normal_form + error_as_ntt_i.coefficients[j])
        }
    }

    result
}
