use crate::{
    arithmetic::{add_to_ring_element, PolynomialRingElement},
    ntt::{invert_ntt_montgomery, ntt, ntt_multiply_montgomery},
    sample::{sample_error_ring_element_uniform, sample_ring_element_uniform},
};

#[inline(always)]
pub(crate) fn sample_error_vector<const DIMENSION: usize, const ETA: usize>(
    mut seed: [u8; 66],
    domain_separator: &mut u16,
) -> [PolynomialRingElement; DIMENSION] {
    let mut error = [PolynomialRingElement::ZERO; DIMENSION];
    for i in 0..DIMENSION {
        seed[64] = *domain_separator as u8;
        seed[65] = (*domain_separator >> 8) as u8;
        *domain_separator += 1;

        error[i] = sample_error_ring_element_uniform::<ETA>(seed);
    }

    error
}

#[allow(non_snake_case)]
#[inline(always)]
pub(crate) fn expand_to_A<const ROWS_IN_A: usize, const COLUMNS_IN_A: usize>(
    mut seed: [u8; 34],
    transposed: bool,
) -> [[PolynomialRingElement; COLUMNS_IN_A]; ROWS_IN_A] {
    let mut A = [[PolynomialRingElement::ZERO; COLUMNS_IN_A]; ROWS_IN_A];

    for i in 0..ROWS_IN_A {
        for j in 0..COLUMNS_IN_A {
            seed[32] = j as u8;
            seed[33] = i as u8;

            let sampled = sample_ring_element_uniform(seed);

            if transposed {
                A[j][i] = sampled;
            } else {
                A[i][j] = sampled;
            }
        }
    }

    A
}

/// Compute InvertNTT(Â ◦ ŝ₁) + s₂
#[inline(always)]
#[allow(non_snake_case)]
pub(crate) fn compute_As1_plus_s2<const ROWS_IN_A: usize, const COLUMNS_IN_A: usize>(
    A: &[[PolynomialRingElement; COLUMNS_IN_A]; ROWS_IN_A],
    s1: &[PolynomialRingElement; COLUMNS_IN_A],
    s2: &[PolynomialRingElement; ROWS_IN_A],
) -> [PolynomialRingElement; ROWS_IN_A] {
    let mut result = [PolynomialRingElement::ZERO; ROWS_IN_A];

    for (i, row) in A.iter().enumerate() {
        for (j, ring_element) in row.iter().enumerate() {
            let product = ntt_multiply_montgomery(ring_element, &ntt(s1[j]));
            result[i] = add_to_ring_element(result[i], &product);
        }

        result[i] = invert_ntt_montgomery(result[i]);
        result[i] = add_to_ring_element(result[i], &s2[i]);
    }

    result
}
