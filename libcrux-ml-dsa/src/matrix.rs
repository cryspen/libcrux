use crate::{arithmetic::PolynomialRingElement, sample::sample_ring_element_for_A};

#[allow(non_snake_case)]
#[inline(always)]
pub(crate) fn expand_to_A<const ROWS_IN_A: usize, const COLUMNS_IN_A: usize>(
    mut seed: [u8; 34],
    transposed: bool,
) -> [[PolynomialRingElement; COLUMNS_IN_A]; ROWS_IN_A] {
    let mut A = [[PolynomialRingElement::ZERO; COLUMNS_IN_A]; ROWS_IN_A];

    for i in 0..ROWS_IN_A {
        for j in 0..COLUMNS_IN_A {
            seed[32] = i as u8;
            seed[33] = j as u8;

            let sampled = sample_ring_element_for_A(seed);

            if transposed {
                A[j][i] = sampled;
            } else {
                A[i][j] = sampled;
            }
        }
    }

    A
}
