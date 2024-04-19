use super::{
    polynomial::{
        add_to_ring_element, 
        subtract_reduce,
        add_error_reduce,
        add_message_error_reduce,
        add_standard_error_reduce,
        ntt_multiply,
        PolynomialRingElement,
    },
    constants::COEFFICIENTS_IN_RING_ELEMENT,
    ntt::{invert_ntt_montgomery},
    sampling::sample_from_xof,
};
use crate::cloop;

#[inline(always)]
#[allow(non_snake_case)]
pub(in crate::kem::kyber) fn sample_matrix_A<const K: usize>(
    seed: [u8; 34],
    transpose: bool,
) -> [[PolynomialRingElement; K]; K] {
    let mut A_transpose = [[PolynomialRingElement::ZERO; K]; K];

    for i in 0..K {
        let mut seeds = [seed; K];
        for j in 0..K {
            seeds[j][32] = i as u8;
            seeds[j][33] = j as u8;
        }
        let sampled = sample_from_xof(seeds);
        for j in 0..K {
            // A[i][j] = A_transpose[j][i]
            if transpose {
                A_transpose[j][i] = sampled[j];
            } else {
                A_transpose[i][j] = sampled[j];
            }
        }
    }

    A_transpose
}

/// The following functions compute various expressions involving
/// vectors and matrices. The computation of these expressions has been
/// abstracted away into these functions in order to save on loop iterations.

/// Compute v − InverseNTT(sᵀ ◦ NTT(u))
#[inline(always)]
pub(in crate::kem::kyber) fn compute_message<const K: usize>(
    v: &PolynomialRingElement,
    secret_as_ntt: &[PolynomialRingElement; K],
    u_as_ntt: &[PolynomialRingElement; K],
) -> PolynomialRingElement {
    let mut result = PolynomialRingElement::ZERO;

    for i in 0..K {
        let product = ntt_multiply(&secret_as_ntt[i], &u_as_ntt[i]);
        result = add_to_ring_element::<K>(result, &product);
    }

    result = invert_ntt_montgomery::<K>(result);
    result = subtract_reduce(v,result);

    result
}

/// Compute InverseNTT(tᵀ ◦ r̂) + e₂ + message
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
        result = add_to_ring_element::<K>(result, &product);
    }

    result = invert_ntt_montgomery::<K>(result);
    result = add_message_error_reduce(error_2,message,result);
    
    result
} 

/// Compute u := InvertNTT(Aᵀ ◦ r̂) + e₁
#[inline(always)]
pub(in crate::kem::kyber) fn compute_vector_u<const K: usize>(
    a_as_ntt: &[[PolynomialRingElement; K]; K],
    r_as_ntt: &[PolynomialRingElement; K],
    error_1: &[PolynomialRingElement; K],
) -> [PolynomialRingElement; K] {
    let mut result = [PolynomialRingElement::ZERO; K];

    cloop! {
        for (i, row) in a_as_ntt.iter().enumerate() {
            cloop! {
                for (j, a_element) in row.iter().enumerate() {
                    let product = ntt_multiply(a_element, &r_as_ntt[j]);
                    result[i] = add_to_ring_element::<K>(result[i], &product);
                }
            }

            result[i] = invert_ntt_montgomery::<K>(result[i]);
            result[i] = add_error_reduce(&error_1[i],result[i]);
        }
    }

    result
}

/// Compute Â ◦ ŝ + ê
#[inline(always)]
#[allow(non_snake_case)]
pub(in crate::kem::kyber) fn compute_As_plus_e<const K: usize>(
    matrix_A: &[[PolynomialRingElement; K]; K],
    s_as_ntt: &[PolynomialRingElement; K],
    error_as_ntt: &[PolynomialRingElement; K],
) -> [PolynomialRingElement; K] {
    let mut result = [PolynomialRingElement::ZERO; K];

    cloop! {
        for (i, row) in matrix_A.iter().enumerate() {
            cloop! {
                for (j, matrix_element) in row.iter().enumerate() {
                    let product = ntt_multiply(matrix_element, &s_as_ntt[j]);
                    result[i] = add_to_ring_element::<K>(result[i], &product);
                }
            }
            result[i] = add_standard_error_reduce(&error_as_ntt[i], result[i]);
        }
    }

    result
}
