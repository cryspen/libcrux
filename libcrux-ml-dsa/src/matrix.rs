use crate::{
    arithmetic::shift_left_then_reduce,
    constants::BITS_IN_LOWER_PART_OF_T,
    helper::cloop,
    ntt::{invert_ntt_montgomery, ntt, ntt_multiply_montgomery},
    polynomial::PolynomialRingElement,
    simd::traits::Operations,
};

/// Compute InvertNTT(Â ◦ ŝ₁) + s₂
#[allow(non_snake_case)]
#[inline(always)]
pub(crate) fn compute_As1_plus_s2<
    SIMDUnit: Operations,
    const ROWS_IN_A: usize,
    const COLUMNS_IN_A: usize,
>(
    a_as_ntt: &[[PolynomialRingElement<SIMDUnit>; COLUMNS_IN_A]; ROWS_IN_A],
    s1_s2: &[PolynomialRingElement<SIMDUnit>],
    result: &mut [PolynomialRingElement<SIMDUnit>; ROWS_IN_A],
) {
    // XXX: Make this better
    let mut s1_ntt = [PolynomialRingElement::<SIMDUnit>::ZERO(); COLUMNS_IN_A];
    for i in 0..s1_ntt.len() {
        s1_ntt[i] = s1_s2[i];
        ntt(&mut s1_ntt[i]);
    }

    for i in 0..ROWS_IN_A {
        for j in 0..COLUMNS_IN_A {
            // XXX: Make this better
            let mut product = a_as_ntt[i][j];
            ntt_multiply_montgomery::<SIMDUnit>(&mut product, &s1_ntt[j]);
            result[i] = PolynomialRingElement::add(&result[i], &product);
        }
    }

    for i in 0..result.len() {
        invert_ntt_montgomery::<SIMDUnit>(&mut result[i]);
        result[i] = PolynomialRingElement::add(&result[i], &s1_s2[COLUMNS_IN_A + i]);
    }
}

/// Compute InvertNTT(Â ◦ ŷ)
#[inline(always)]
pub(crate) fn compute_matrix_x_mask<
    SIMDUnit: Operations,
    const ROWS_IN_A: usize,
    const COLUMNS_IN_A: usize,
>(
    matrix: &[[PolynomialRingElement<SIMDUnit>; COLUMNS_IN_A]; ROWS_IN_A],
    mask: &[PolynomialRingElement<SIMDUnit>; COLUMNS_IN_A],
    result: &mut [PolynomialRingElement<SIMDUnit>; ROWS_IN_A],
) {
    // XXX: Make this better
    let mut mask_ntt = mask.clone();
    for i in 0..mask_ntt.len() {
        ntt(&mut mask_ntt[i]);
    }

    cloop! {
        for (i, row) in matrix.iter().enumerate() {
            cloop! {
                for (j, ring_element) in row.iter().enumerate() {
                    // XXX: Make this better
                    let mut product = mask_ntt[j];
                    ntt_multiply_montgomery(&mut product, &ring_element);
                    result[i] = PolynomialRingElement::<SIMDUnit>::add(&result[i], &product);
                }
            }

            invert_ntt_montgomery(&mut result[i]);
        }
    }
}

#[allow(non_snake_case)]
#[inline(always)]
pub(crate) fn vector_times_ring_element<SIMDUnit: Operations, const DIMENSION: usize>(
    vector: &[PolynomialRingElement<SIMDUnit>; DIMENSION],
    ring_element: &PolynomialRingElement<SIMDUnit>,
) -> [PolynomialRingElement<SIMDUnit>; DIMENSION] {
    // XXX: pull out the result to dsa generic
    let mut result = vector.clone();

    for i in 0..vector.len() {
        ntt_multiply_montgomery(&mut result[i], ring_element);
        invert_ntt_montgomery(&mut result[i]);
    }

    result
}

#[allow(non_snake_case)]
#[inline(always)]
pub(crate) fn add_vectors<SIMDUnit: Operations, const DIMENSION: usize>(
    lhs: &[PolynomialRingElement<SIMDUnit>; DIMENSION],
    rhs: &[PolynomialRingElement<SIMDUnit>; DIMENSION],
) -> [PolynomialRingElement<SIMDUnit>; DIMENSION] {
    let mut result = [PolynomialRingElement::<SIMDUnit>::ZERO(); DIMENSION];

    for i in 0..DIMENSION {
        result[i] = PolynomialRingElement::<SIMDUnit>::add(&lhs[i], &rhs[i]);
    }

    result
}

#[allow(non_snake_case)]
#[inline(always)]
pub(crate) fn subtract_vectors<SIMDUnit: Operations, const DIMENSION: usize>(
    lhs: &[PolynomialRingElement<SIMDUnit>; DIMENSION],
    rhs: &[PolynomialRingElement<SIMDUnit>; DIMENSION],
) -> [PolynomialRingElement<SIMDUnit>; DIMENSION] {
    let mut result = [PolynomialRingElement::<SIMDUnit>::ZERO(); DIMENSION];

    for i in 0..DIMENSION {
        result[i] = PolynomialRingElement::<SIMDUnit>::subtract(&lhs[i], &rhs[i]);
    }

    result
}

/// Compute InvertNTT(Â ◦ ẑ - ĉ ◦ NTT(t₁2ᵈ))
#[allow(non_snake_case)]
#[inline(always)]
pub(crate) fn compute_w_approx<
    SIMDUnit: Operations,
    const ROWS_IN_A: usize,
    const COLUMNS_IN_A: usize,
>(
    A_as_ntt: &[[PolynomialRingElement<SIMDUnit>; COLUMNS_IN_A]; ROWS_IN_A],
    mut signer_response: [PolynomialRingElement<SIMDUnit>; COLUMNS_IN_A],
    verifier_challenge_as_ntt: &PolynomialRingElement<SIMDUnit>,
    t1: &mut [PolynomialRingElement<SIMDUnit>; ROWS_IN_A],
) {
    // Move signer response into NTT
    for i in 0..signer_response.len() {
        ntt(&mut signer_response[i]);
    }

    cloop! {
        for (i, row) in A_as_ntt.iter().enumerate() {
            let mut inner_result = PolynomialRingElement::<SIMDUnit>::ZERO();
            cloop! {
                for (j, ring_element) in row.iter().enumerate() {
                    // XXX: make nicer
                    let mut product = ring_element.clone();
                    ntt_multiply_montgomery(&mut product, &signer_response[j]);

                     PolynomialRingElement::<SIMDUnit>::add_mut(&mut inner_result, &product);
                }
            }

            shift_left_then_reduce::<SIMDUnit, { BITS_IN_LOWER_PART_OF_T as i32 }>(&mut t1[i]);
            ntt(&mut t1[i]);
            ntt_multiply_montgomery(&mut t1[i], verifier_challenge_as_ntt);
            t1[i] = PolynomialRingElement::<SIMDUnit>::subtract(
                &inner_result,
                &t1[i],
            );
            invert_ntt_montgomery(&mut t1[i]);
        }
    }
}
