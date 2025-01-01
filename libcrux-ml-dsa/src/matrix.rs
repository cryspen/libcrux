use crate::{
    arithmetic::shift_left_then_reduce,
    constants::BITS_IN_LOWER_PART_OF_T,
    ntt::{invert_ntt_montgomery, ntt, ntt_multiply_montgomery},
    polynomial::PolynomialRingElement,
    simd::traits::Operations,
};

/// Compute InvertNTT(Â ◦ ŝ₁) + s₂
pub(crate) fn compute_as1_plus_s2<SIMDUnit: Operations>(
    rows_in_a: usize,
    columns_in_a: usize,
    a_as_ntt: &[PolynomialRingElement<SIMDUnit>],
    s1_ntt: &[PolynomialRingElement<SIMDUnit>],
    s1_s2: &[PolynomialRingElement<SIMDUnit>],
    result: &mut [PolynomialRingElement<SIMDUnit>],
) {
    for i in 0..rows_in_a {
        for j in 0..columns_in_a {
            let mut product = a_as_ntt[i * columns_in_a + j];
            ntt_multiply_montgomery::<SIMDUnit>(&mut product, &s1_ntt[j]);
            PolynomialRingElement::add(&mut result[i], &product);
        }
    }

    for i in 0..result.len() {
        invert_ntt_montgomery::<SIMDUnit>(&mut result[i]);
        PolynomialRingElement::add(&mut result[i], &s1_s2[columns_in_a + i]);
    }
}

/// Compute InvertNTT(Â ◦ ŷ)
#[inline(always)]
pub(crate) fn compute_matrix_x_mask<SIMDUnit: Operations>(
    rows_in_a: usize,
    columns_in_a: usize,
    matrix: &[PolynomialRingElement<SIMDUnit>],
    mask: &[PolynomialRingElement<SIMDUnit>],
    result: &mut [PolynomialRingElement<SIMDUnit>],
) {
    for i in 0..rows_in_a {
        for j in 0..columns_in_a {
            let mut product = mask[j];
            ntt_multiply_montgomery(&mut product, &matrix[i * columns_in_a + j]);
            PolynomialRingElement::<SIMDUnit>::add(&mut result[i], &product);
        }
        invert_ntt_montgomery(&mut result[i]);
    }
}

#[inline(always)]
pub(crate) fn vector_times_ring_element<SIMDUnit: Operations, const DIMENSION: usize>(
    vector: &mut [PolynomialRingElement<SIMDUnit>; DIMENSION],
    ring_element: &PolynomialRingElement<SIMDUnit>,
) {
    for i in 0..vector.len() {
        ntt_multiply_montgomery(&mut vector[i], ring_element);
        invert_ntt_montgomery(&mut vector[i]);
    }
}

#[inline(always)]
pub(crate) fn add_vectors<SIMDUnit: Operations, const DIMENSION: usize>(
    lhs: &mut [PolynomialRingElement<SIMDUnit>; DIMENSION],
    rhs: &[PolynomialRingElement<SIMDUnit>; DIMENSION],
) {
    for i in 0..DIMENSION {
        PolynomialRingElement::<SIMDUnit>::add(&mut lhs[i], &rhs[i]);
    }
}

#[inline(always)]
pub(crate) fn subtract_vectors<SIMDUnit: Operations, const DIMENSION: usize>(
    lhs: &mut [PolynomialRingElement<SIMDUnit>; DIMENSION],
    rhs: &[PolynomialRingElement<SIMDUnit>; DIMENSION],
) {
    for i in 0..DIMENSION {
        PolynomialRingElement::<SIMDUnit>::subtract(&mut lhs[i], &rhs[i]);
    }
}

/// Compute InvertNTT(Â ◦ ẑ - ĉ ◦ NTT(t₁2ᵈ))
#[inline(always)]
pub(crate) fn compute_w_approx<SIMDUnit: Operations>(
    rows_in_a: usize,
    columns_in_a: usize,
    matrix: &[PolynomialRingElement<SIMDUnit>],
    signer_response: &[PolynomialRingElement<SIMDUnit>],
    verifier_challenge_as_ntt: &PolynomialRingElement<SIMDUnit>,
    t1: &mut [PolynomialRingElement<SIMDUnit>],
) {
    for i in 0..rows_in_a {
        let mut inner_result = PolynomialRingElement::<SIMDUnit>::zero();
        for j in 0..columns_in_a {
            let mut product = matrix[i * columns_in_a + j];
            ntt_multiply_montgomery(&mut product, &signer_response[j]);
            PolynomialRingElement::<SIMDUnit>::add(&mut inner_result, &product);
        }

        shift_left_then_reduce::<SIMDUnit, { BITS_IN_LOWER_PART_OF_T as i32 }>(&mut t1[i]);
        ntt(&mut t1[i]);
        ntt_multiply_montgomery(&mut t1[i], verifier_challenge_as_ntt);
        PolynomialRingElement::<SIMDUnit>::subtract(&mut inner_result, &t1[i]);
        t1[i] = inner_result;
        invert_ntt_montgomery(&mut t1[i]);
    }
}
