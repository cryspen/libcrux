use crate::{
    arithmetic::shift_coefficients_left_then_reduce,
    constants::BITS_IN_LOWER_PART_OF_T,
    ntt::{invert_ntt_montgomery, ntt, ntt_multiply_montgomery},
    polynomial::{PolynomialRingElement, SIMDPolynomialRingElement},
    sample::sample_ring_element_uniform,
    simd::portable::PortableSIMDUnit,
};

#[allow(non_snake_case)]
#[inline(always)]
pub(crate) fn expand_to_A<const ROWS_IN_A: usize, const COLUMNS_IN_A: usize>(
    mut seed: [u8; 34],
) -> [[PolynomialRingElement; COLUMNS_IN_A]; ROWS_IN_A] {
    let mut A = [[PolynomialRingElement::ZERO; COLUMNS_IN_A]; ROWS_IN_A];

    // Mutable iterators won't go through hax, so we need these range loops.
    #[allow(clippy::needless_range_loop)]
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
#[allow(non_snake_case)]
#[inline(always)]
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
#[allow(non_snake_case)]
#[inline(always)]
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

#[allow(non_snake_case)]
#[inline(always)]
pub(crate) fn vector_times_ring_element<const DIMENSION: usize>(
    vector: &[PolynomialRingElement; DIMENSION],
    ring_element: &PolynomialRingElement,
) -> [PolynomialRingElement; DIMENSION] {
    let mut result = [PolynomialRingElement::ZERO; DIMENSION];

    for (i, vector_ring_element) in vector.iter().enumerate() {
        result[i] =
            invert_ntt_montgomery(ntt_multiply_montgomery(vector_ring_element, ring_element));
    }

    result
}

#[allow(non_snake_case)]
#[inline(always)]
pub(crate) fn add_vectors<const DIMENSION: usize>(
    lhs: &[PolynomialRingElement; DIMENSION],
    rhs: &[PolynomialRingElement; DIMENSION],
) -> [PolynomialRingElement; DIMENSION] {
    let mut result = [PolynomialRingElement::ZERO; DIMENSION];

    for i in 0..DIMENSION {
        let lhs_vectorized =
            SIMDPolynomialRingElement::<PortableSIMDUnit>::from_polynomial_ring_element(lhs[i]);
        let rhs_vectorized =
            SIMDPolynomialRingElement::<PortableSIMDUnit>::from_polynomial_ring_element(rhs[i]);

        result[i] = lhs_vectorized
            .add(&rhs_vectorized)
            .to_polynomial_ring_element();
    }

    result
}

#[allow(non_snake_case)]
#[inline(always)]
pub(crate) fn subtract_vectors<const DIMENSION: usize>(
    lhs: &[PolynomialRingElement; DIMENSION],
    rhs: &[PolynomialRingElement; DIMENSION],
) -> [PolynomialRingElement; DIMENSION] {
    let mut result = [PolynomialRingElement::ZERO; DIMENSION];

    for i in 0..DIMENSION {
        let lhs_vectorized =
            SIMDPolynomialRingElement::<PortableSIMDUnit>::from_polynomial_ring_element(lhs[i]);
        let rhs_vectorized =
            SIMDPolynomialRingElement::<PortableSIMDUnit>::from_polynomial_ring_element(rhs[i]);

        result[i] = lhs_vectorized
            .subtract(&rhs_vectorized)
            .to_polynomial_ring_element();
    }

    result
}

/// Compute InvertNTT(Â ◦ ẑ - ĉ ◦ NTT(t₁2ᵈ))
#[allow(non_snake_case)]
#[inline(always)]
pub(crate) fn compute_w_approx<const ROWS_IN_A: usize, const COLUMNS_IN_A: usize>(
    A_as_ntt: &[[PolynomialRingElement; COLUMNS_IN_A]; ROWS_IN_A],
    signer_response: [PolynomialRingElement; COLUMNS_IN_A],
    verifier_challenge_as_ntt: PolynomialRingElement,
    t1: [PolynomialRingElement; ROWS_IN_A],
) -> [PolynomialRingElement; ROWS_IN_A] {
    let mut result = [PolynomialRingElement::ZERO; ROWS_IN_A];

    for (i, row) in A_as_ntt.iter().enumerate() {
        for (j, ring_element) in row.iter().enumerate() {
            let product = ntt_multiply_montgomery(ring_element, &ntt(signer_response[j]));

            result[i] = result[i].add(&product);
        }

        let t1_shifted = shift_coefficients_left_then_reduce(t1[i], BITS_IN_LOWER_PART_OF_T);
        let challenge_times_t1_shifted =
            ntt_multiply_montgomery(&verifier_challenge_as_ntt, &ntt(t1_shifted));
        result[i] = invert_ntt_montgomery(result[i].sub(&challenge_times_t1_shifted));
    }

    result
}
