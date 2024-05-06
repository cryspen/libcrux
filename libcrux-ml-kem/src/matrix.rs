use libcrux_polynomials::Operations;

use crate::{
    helper::cloop, polynomial::invert_ntt_montgomery, polynomial::PolynomialRingElement,
    sampling::sample_from_xof,
};

#[inline(always)]
#[allow(non_snake_case)]
pub(crate) fn sample_matrix_A<const K: usize, Vector: Operations>(
    seed: [u8; 34],
    transpose: bool,
) -> [[PolynomialRingElement<Vector>; K]; K] {
    let mut A_transpose = [[PolynomialRingElement::<Vector>::ZERO(); K]; K];

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
pub(crate) fn compute_message<const K: usize, Vector: Operations>(
    v: &PolynomialRingElement<Vector>,
    secret_as_ntt: &[PolynomialRingElement<Vector>; K],
    u_as_ntt: &[PolynomialRingElement<Vector>; K],
) -> PolynomialRingElement<Vector> {
    let mut result = PolynomialRingElement::<Vector>::ZERO();

    for i in 0..K {
        let product = secret_as_ntt[i].ntt_multiply(&u_as_ntt[i]);
        result = result.add_to_ring_element::<K>(&product);
    }

    result = invert_ntt_montgomery::<K, Vector>(result);
    result = v.subtract_reduce(result);

    result
}

/// Compute InverseNTT(tᵀ ◦ r̂) + e₂ + message
#[inline(always)]
pub(crate) fn compute_ring_element_v<const K: usize, Vector: Operations>(
    t_as_ntt: &[PolynomialRingElement<Vector>; K],
    r_as_ntt: &[PolynomialRingElement<Vector>; K],
    error_2: &PolynomialRingElement<Vector>,
    message: &PolynomialRingElement<Vector>,
) -> PolynomialRingElement<Vector> {
    let mut result = PolynomialRingElement::<Vector>::ZERO();

    for i in 0..K {
        let product = t_as_ntt[i].ntt_multiply(&r_as_ntt[i]);
        result = result.add_to_ring_element::<K>(&product);
    }

    result = invert_ntt_montgomery::<K, Vector>(result);
    result = error_2.add_message_error_reduce(message, result);

    result
}

/// Compute u := InvertNTT(Aᵀ ◦ r̂) + e₁
#[inline(always)]
pub(crate) fn compute_vector_u<const K: usize, Vector: Operations>(
    a_as_ntt: &[[PolynomialRingElement<Vector>; K]; K],
    r_as_ntt: &[PolynomialRingElement<Vector>; K],
    error_1: &[PolynomialRingElement<Vector>; K],
) -> [PolynomialRingElement<Vector>; K] {
    let mut result = [PolynomialRingElement::<Vector>::ZERO(); K];

    cloop! {
        for (i, row) in a_as_ntt.iter().enumerate() {
            cloop! {
                for (j, a_element) in row.iter().enumerate() {
                    let product = a_element.ntt_multiply(&r_as_ntt[j]);
                    result[i] = result[i].add_to_ring_element::<K>(&product);
                }
            }

            result[i] = invert_ntt_montgomery::<K, Vector>(result[i]);
            result[i] = error_1[i].add_error_reduce(result[i]);
        }
    }

    result
}

/// Compute Â ◦ ŝ + ê
#[inline(always)]
#[allow(non_snake_case)]
pub(crate) fn compute_As_plus_e<const K: usize, Vector: Operations>(
    matrix_A: &[[PolynomialRingElement<Vector>; K]; K],
    s_as_ntt: &[PolynomialRingElement<Vector>; K],
    error_as_ntt: &[PolynomialRingElement<Vector>; K],
) -> [PolynomialRingElement<Vector>; K] {
    let mut result = [PolynomialRingElement::<Vector>::ZERO(); K];

    cloop! {
        for (i, row) in matrix_A.iter().enumerate() {
            cloop! {
                for (j, matrix_element) in row.iter().enumerate() {
                    let product = matrix_element.ntt_multiply(&s_as_ntt[j]);
                    result[i] = result[i].add_to_ring_element::<K>(&product);
                }
            }
            result[i] = error_as_ntt[i].add_standard_error_reduce(result[i]);
        }
    }

    result
}
