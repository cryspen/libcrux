use core::array;

use crate::{
    arithmetic::shift_left_then_reduce,
    constants::BITS_IN_LOWER_PART_OF_T,
    helper::cloop,
    ntt::{
        invert_ntt_montgomery, invert_ntt_montgomery_mut, ntt, ntt_multiply_montgomery,
        ntt_multiply_montgomery_mut,
    },
    polynomial::PolynomialRingElement,
    sample::SampledRingElement,
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
    A_as_ntt: &[SampledRingElement<SIMDUnit>],
    // s1: &[PolynomialRingElement<SIMDUnit>; COLUMNS_IN_A],
    // s2: &[PolynomialRingElement<SIMDUnit>; ROWS_IN_A],
    s_elements: &[SampledRingElement<SIMDUnit>],
) -> [PolynomialRingElement<SIMDUnit>; ROWS_IN_A] {
    let mut result = [PolynomialRingElement::<SIMDUnit>::ZERO(); ROWS_IN_A];
    // let s1_ntt = s_elements.map(|s| ntt::<SIMDUnit>(s));
    let s1_ntt: [PolynomialRingElement<SIMDUnit>; COLUMNS_IN_A] =
        array::from_fn(|i| ntt::<SIMDUnit>(s_elements[i].into_ring_element()));

    for i in 0..ROWS_IN_A {
        for j in 0..COLUMNS_IN_A {
            let product = ntt_multiply_montgomery::<SIMDUnit>(
                &A_as_ntt[i * COLUMNS_IN_A + j].into_ring_element(),
                &s1_ntt[j],
            );
            result[i] = PolynomialRingElement::add(&result[i], &product);
        }
    }

    for i in 0..result.len() {
        result[i] = invert_ntt_montgomery::<SIMDUnit>(result[i]);
        result[i] = PolynomialRingElement::add(
            &result[i],
            &s_elements[COLUMNS_IN_A + i].into_ring_element(),
        );
    }

    result
}

/// Compute InvertNTT(Â ◦ ŷ)
#[allow(non_snake_case)]
#[inline(always)]
pub(crate) fn compute_A_times_mask<
    SIMDUnit: Operations,
    const ROWS_IN_A: usize,
    const COLUMNS_IN_A: usize,
>(
    A_as_ntt: &[SampledRingElement<SIMDUnit>],
    mask: &[PolynomialRingElement<SIMDUnit>; COLUMNS_IN_A],
) -> [PolynomialRingElement<SIMDUnit>; ROWS_IN_A] {
    let mut result = [PolynomialRingElement::<SIMDUnit>::ZERO(); ROWS_IN_A];
    let mask_ntt = mask.map(|s| ntt::<SIMDUnit>(s));

    for i in 0..ROWS_IN_A {
        for j in 0..COLUMNS_IN_A {
            let product = ntt_multiply_montgomery(
                &A_as_ntt[i * COLUMNS_IN_A + j].into_ring_element(),
                &mask_ntt[j],
            );
            result[i] = PolynomialRingElement::<SIMDUnit>::add(&result[i], &product);
        }
        result[i] = invert_ntt_montgomery(result[i]);
    }

    result
}

#[allow(non_snake_case)]
#[inline(always)]
pub(crate) fn vector_times_ring_element<SIMDUnit: Operations, const DIMENSION: usize>(
    vector: &[PolynomialRingElement<SIMDUnit>; DIMENSION],
    ring_element: &PolynomialRingElement<SIMDUnit>,
) -> [PolynomialRingElement<SIMDUnit>; DIMENSION] {
    let mut result = vector.clone();
    for i in 0..vector.len() {
        ntt_multiply_montgomery_mut(&mut result[i], ring_element);
    }
    for i in 0..vector.len() {
        invert_ntt_montgomery_mut(&mut result[i]);
    }
    result
}

#[allow(non_snake_case)]
#[inline(always)]
pub(crate) fn vector_times_ring_element_mut<SIMDUnit: Operations, const DIMENSION: usize>(
    vector: &mut [PolynomialRingElement<SIMDUnit>; DIMENSION],
    ring_element: &PolynomialRingElement<SIMDUnit>,
) {
    for i in 0..vector.len() {
        vector[i] = ntt_multiply_montgomery(&vector[i], ring_element);
    }
    for i in 0..vector.len() {
        vector[i] = invert_ntt_montgomery(vector[i]);
    }
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
pub(crate) fn add_vectors_mut<SIMDUnit: Operations, const DIMENSION: usize>(
    lhs: &mut [PolynomialRingElement<SIMDUnit>; DIMENSION],
    rhs: &[PolynomialRingElement<SIMDUnit>; DIMENSION],
) {
    for i in 0..DIMENSION {
        lhs[i] = PolynomialRingElement::<SIMDUnit>::add(&lhs[i], &rhs[i]);
    }
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

#[allow(non_snake_case)]
#[inline(always)]
pub(crate) fn subtract_vectors_mut<SIMDUnit: Operations, const DIMENSION: usize>(
    lhs: &mut [PolynomialRingElement<SIMDUnit>; DIMENSION],
    rhs: &[PolynomialRingElement<SIMDUnit>; DIMENSION],
) {
    for i in 0..DIMENSION {
        lhs[i] = PolynomialRingElement::<SIMDUnit>::subtract(&lhs[i], &rhs[i]);
    }
}

/// Compute InvertNTT(Â ◦ ẑ - ĉ ◦ NTT(t₁2ᵈ))
#[allow(non_snake_case)]
#[inline(always)]
pub(crate) fn compute_w_approx<
    SIMDUnit: Operations,
    const ROWS_IN_A: usize,
    const COLUMNS_IN_A: usize,
>(
    A_as_ntt: &[SampledRingElement<SIMDUnit>],
    mut signer_response: [PolynomialRingElement<SIMDUnit>; COLUMNS_IN_A],
    verifier_challenge_as_ntt: PolynomialRingElement<SIMDUnit>,
    t1: [PolynomialRingElement<SIMDUnit>; ROWS_IN_A],
) -> [PolynomialRingElement<SIMDUnit>; ROWS_IN_A] {
    let mut result = [PolynomialRingElement::<SIMDUnit>::ZERO(); ROWS_IN_A];

    // Move signer response into NTT
    for i in 0..signer_response.len() {
        signer_response[i] = ntt(signer_response[i]);
    }

    for i in 0..ROWS_IN_A {
        for j in 0..COLUMNS_IN_A {
            let product = ntt_multiply_montgomery(
                &A_as_ntt[i * COLUMNS_IN_A + j].into_ring_element(),
                &signer_response[j],
            );
            result[i] = PolynomialRingElement::<SIMDUnit>::add(&result[i], &product);
        }
        let t1_shifted =
            shift_left_then_reduce::<SIMDUnit, { BITS_IN_LOWER_PART_OF_T as i32 }>(t1[i]);
        let t1_shifted = ntt(t1_shifted);
        let challenge_times_t1_shifted =
            ntt_multiply_montgomery(&verifier_challenge_as_ntt, &t1_shifted);
        result[i] = invert_ntt_montgomery(PolynomialRingElement::<SIMDUnit>::subtract(
            &result[i],
            &challenge_times_t1_shifted,
        ));
    }

    result
}
