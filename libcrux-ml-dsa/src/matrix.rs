use crate::{
    arithmetic::PolynomialRingElement,
    ntt::{invert_ntt_montgomery, ntt, ntt_multiply_montgomery},
    sample::sample_ring_element_uniform,
};

#[allow(non_snake_case)]
#[inline(always)]
pub(crate) fn expand_to_A<const ROWS_IN_A: usize, const COLUMNS_IN_A: usize>(
    mut seed: [u8; 34],
) -> [[PolynomialRingElement; COLUMNS_IN_A]; ROWS_IN_A] {
    let mut A = [[PolynomialRingElement::ZERO; COLUMNS_IN_A]; ROWS_IN_A];

    for i in 0..ROWS_IN_A {
        for j in 0..COLUMNS_IN_A {
            seed[32] = j as u8;
            seed[33] = i as u8;

            A[i][j] = sample_ring_element_uniform(seed);
        }
    }

    A
}

/// Compute InvertNTT(Â ◦ ŝ₁) + s₂
#[inline(always)]
#[allow(non_snake_case)]
pub(crate) fn compute_As1_plus_s2<const ROWS_IN_A: usize, const COLUMNS_IN_A: usize>(
    A_as_ntt: &[[PolynomialRingElement; COLUMNS_IN_A]; ROWS_IN_A],
    s1: &[PolynomialRingElement; COLUMNS_IN_A],
    s2: &[PolynomialRingElement; ROWS_IN_A],
) -> [PolynomialRingElement; ROWS_IN_A] {
    let mut result = [PolynomialRingElement::ZERO; ROWS_IN_A];

    for (i, row) in A_as_ntt.iter().enumerate() {
        for (j, ring_element) in row.iter().enumerate() {
            let product = ntt_multiply_montgomery(ring_element, &ntt(s1[j]));
            result[i] = result[i].add(&product);
        }

        result[i] = invert_ntt_montgomery(result[i]);
        result[i] = result[i].add(&s2[i]);
    }

    result
}

/// Compute InvertNTT(Â ◦ ŷ)
#[inline(always)]
#[allow(non_snake_case)]
pub(crate) fn compute_A_times_mask<const ROWS_IN_A: usize, const COLUMNS_IN_A: usize>(
    A_as_ntt: &[[PolynomialRingElement; COLUMNS_IN_A]; ROWS_IN_A],
    mask: &[PolynomialRingElement; COLUMNS_IN_A],
) -> [PolynomialRingElement; ROWS_IN_A] {
    let mut result = [PolynomialRingElement::ZERO; ROWS_IN_A];

    for (i, row) in A_as_ntt.iter().enumerate() {
        for (j, ring_element) in row.iter().enumerate() {
            let product = ntt_multiply_montgomery(ring_element, &ntt(mask[j]));
            result[i] = result[i].add(&product);
        }

        result[i] = invert_ntt_montgomery(result[i]);
    }

    result
}

#[inline(always)]
#[allow(non_snake_case)]
pub(crate) fn vector_times_ring_element<const DIMENSION: usize>(
    vector: &[PolynomialRingElement; DIMENSION],
    ring_element: &PolynomialRingElement,
) -> [PolynomialRingElement; DIMENSION] {
    let mut result = [PolynomialRingElement::ZERO; DIMENSION];

    for (i, vector_element) in vector.iter().enumerate() {
        result[i] = invert_ntt_montgomery(ntt_multiply_montgomery(&vector_element, ring_element));
    }

    result
}

#[inline(always)]
#[allow(non_snake_case)]
pub(crate) fn add_vectors<const DIMENSION: usize>(
    lhs: &[PolynomialRingElement; DIMENSION],
    rhs: &[PolynomialRingElement; DIMENSION],
) -> [PolynomialRingElement; DIMENSION] {
    let mut result = [PolynomialRingElement::ZERO; DIMENSION];

    for i in 0..DIMENSION {
        result[i] = lhs[i].add(&rhs[i]);
    }

    result
}

#[inline(always)]
#[allow(non_snake_case)]
pub(crate) fn subtract_vectors<const DIMENSION: usize>(
    lhs: &[PolynomialRingElement; DIMENSION],
    rhs: &[PolynomialRingElement; DIMENSION],
) -> [PolynomialRingElement; DIMENSION] {
    let mut result = [PolynomialRingElement::ZERO; DIMENSION];

    for i in 0..DIMENSION {
        result[i] = lhs[i].sub(&rhs[i]);
    }

    result
}
