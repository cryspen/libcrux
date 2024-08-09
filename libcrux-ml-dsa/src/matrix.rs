use crate::{
    arithmetic::shift_left_then_reduce,
    constants::BITS_IN_LOWER_PART_OF_T,
    hash_functions::shake128,
    ntt::{invert_ntt_montgomery, ntt, ntt_multiply_montgomery},
    polynomial::PolynomialRingElement,
    sample::{sample_four_ring_element_uniform, sample_ring_element_uniform},
    simd::traits::Operations,
};

#[allow(non_snake_case)]
#[inline(always)]
pub(crate) fn expand_to_A<
    SIMDUnit: Operations,
    Shake128: shake128::Xof,
    Shake128X4: shake128::XofX4,
    const ROWS_IN_A: usize,
    const COLUMNS_IN_A: usize,
>(
    mut seed: [u8; 34],
) -> [[PolynomialRingElement<SIMDUnit>; COLUMNS_IN_A]; ROWS_IN_A] {
    let mut A = core::array::from_fn(|_| {
        core::array::from_fn(|_| PolynomialRingElement::<SIMDUnit>::ZERO())
    });

    // Mutable iterators won't go through hax, so we need these range loops.

    // | Key size | ROWS_IN_A | COLUMNS_IN_A |
    // | -------- | --------- | ------------ |
    // | 44       | 4         | 4            |
    // | 65       | 6         | 5            |
    // | 87       | 8         | 7            |
    //
    // We always do 4 in parallel first and then one at a time.
    #[allow(clippy::needless_range_loop)]
    for i in 0..ROWS_IN_A {
        let samples = sample_four_ring_element_uniform::<SIMDUnit, Shake128X4>(seed, i);
        A[i][0] = samples.0;
        A[i][1] = samples.1;
        A[i][2] = samples.2;
        A[i][3] = samples.3;

        // TODO: We could do more in parallel if we think that may speed
        //       things up.
        for j in 4..COLUMNS_IN_A {
            seed[32] = j as u8;
            seed[33] = i as u8;

            A[i][j] = sample_ring_element_uniform::<SIMDUnit, Shake128>(seed);
        }
    }

    A
}

/// Compute InvertNTT(Â ◦ ŝ₁) + s₂
#[allow(non_snake_case)]
#[inline(always)]
pub(crate) fn compute_As1_plus_s2<
    SIMDUnit: Operations,
    const ROWS_IN_A: usize,
    const COLUMNS_IN_A: usize,
>(
    A_as_ntt: &[[PolynomialRingElement<SIMDUnit>; COLUMNS_IN_A]; ROWS_IN_A],
    s1: &[PolynomialRingElement<SIMDUnit>; COLUMNS_IN_A],
    s2: &[PolynomialRingElement<SIMDUnit>; ROWS_IN_A],
) -> [PolynomialRingElement<SIMDUnit>; ROWS_IN_A] {
    let mut result = core::array::from_fn(|_| PolynomialRingElement::<SIMDUnit>::ZERO());

    for (i, row) in A_as_ntt.iter().enumerate() {
        for (j, ring_element) in row.iter().enumerate() {
            let product =
                ntt_multiply_montgomery::<SIMDUnit>(ring_element, &ntt::<SIMDUnit>(s1[j]));
            PolynomialRingElement::add(&mut result[i], &product);
        }

        result[i] = invert_ntt_montgomery::<SIMDUnit>(result[i]);
        PolynomialRingElement::add(&mut result[i], &s2[i]);
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
    A_as_ntt: &[[PolynomialRingElement<SIMDUnit>; COLUMNS_IN_A]; ROWS_IN_A],
    mask: &[PolynomialRingElement<SIMDUnit>; COLUMNS_IN_A],
) -> [PolynomialRingElement<SIMDUnit>; ROWS_IN_A] {
    let mut result = core::array::from_fn(|_| PolynomialRingElement::<SIMDUnit>::ZERO());

    for (i, row) in A_as_ntt.iter().enumerate() {
        for (j, ring_element) in row.iter().enumerate() {
            let product = ntt_multiply_montgomery(&ring_element, &ntt(mask[j]));
            PolynomialRingElement::<SIMDUnit>::add(&mut result[i], &product);
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
    let mut result = core::array::from_fn(|_| PolynomialRingElement::<SIMDUnit>::ZERO());

    for (i, vector_ring_element) in vector.iter().enumerate() {
        result[i] =
            invert_ntt_montgomery(ntt_multiply_montgomery(vector_ring_element, ring_element));
    }

    result
}

#[allow(non_snake_case)]
#[inline(always)]
pub(crate) fn add_vectors<SIMDUnit: Operations, const DIMENSION: usize>(
    lhs: &mut [PolynomialRingElement<SIMDUnit>; DIMENSION],
    rhs: &[PolynomialRingElement<SIMDUnit>; DIMENSION],
) {
    for i in 0..DIMENSION {
        PolynomialRingElement::<SIMDUnit>::add(&mut lhs[i], &rhs[i]);
    }
}

#[allow(non_snake_case)]
#[inline(always)]
pub(crate) fn subtract_vectors<SIMDUnit: Operations, const DIMENSION: usize>(
    lhs: &[PolynomialRingElement<SIMDUnit>; DIMENSION],
    rhs: &[PolynomialRingElement<SIMDUnit>; DIMENSION],
) -> [PolynomialRingElement<SIMDUnit>; DIMENSION] {
    let mut result = core::array::from_fn(|_| PolynomialRingElement::<SIMDUnit>::ZERO());

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
    signer_response: [PolynomialRingElement<SIMDUnit>; COLUMNS_IN_A],
    verifier_challenge_as_ntt: PolynomialRingElement<SIMDUnit>,
    t1: [PolynomialRingElement<SIMDUnit>; ROWS_IN_A],
) -> [PolynomialRingElement<SIMDUnit>; ROWS_IN_A] {
    let mut result = core::array::from_fn(|_| PolynomialRingElement::<SIMDUnit>::ZERO());

    for (i, row) in A_as_ntt.iter().enumerate() {
        for (j, ring_element) in row.iter().enumerate() {
            let product = ntt_multiply_montgomery(&ring_element, &ntt(signer_response[j]));
            PolynomialRingElement::<SIMDUnit>::add(&mut result[i], &product);
        }

        let t1_shifted =
            shift_left_then_reduce::<SIMDUnit, { BITS_IN_LOWER_PART_OF_T as i32 }>(t1[i]);
        let challenge_times_t1_shifted =
            ntt_multiply_montgomery(&verifier_challenge_as_ntt, &ntt(t1_shifted));
        result[i] = invert_ntt_montgomery(PolynomialRingElement::<SIMDUnit>::subtract(
            &result[i],
            &challenge_times_t1_shifted,
        ));
    }

    result
}
