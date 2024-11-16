use crate::{
    hash_functions::{shake128, shake256},
    polynomial::PolynomialRingElement,
    sample::{sample_four_error_ring_elements, sample_four_ring_elements},
    simd::traits::Operations,
};

#[inline(always)]
fn generate_domain_separator(row: u8, column: u8) -> u16 {
    (column as u16) | ((row as u16) << 8)
}

// Doing deep updates like `a[1][1] = 3` causes a memory blowup in F*
// https://github.com/hacspec/hax/issues/1098
// So we are instead using a matrix abstraction with a custom update function here.

type Matrix<SIMDUnit, const ROWS_IN_A: usize, const COLUMNS_IN_A: usize> =
    [[PolynomialRingElement<SIMDUnit>; COLUMNS_IN_A]; ROWS_IN_A];

fn update_matrix<SIMDUnit: Operations, const ROWS_IN_A: usize, const COLUMNS_IN_A: usize>(
    m: &mut Matrix<SIMDUnit, ROWS_IN_A, COLUMNS_IN_A>,
    i: usize,
    j: usize,
    v: PolynomialRingElement<SIMDUnit>,
) {
    m[i][j] = v;
}

#[inline(always)]
pub(crate) fn matrix_4_by_4<
    SIMDUnit: Operations,
    Shake128X4: shake128::XofX4,
    const ROWS_IN_A: usize,
    const COLUMNS_IN_A: usize,
>(
    seed: [u8; 34],
    matrix: &mut Matrix<SIMDUnit, ROWS_IN_A, COLUMNS_IN_A>,
) {
    sample_four_ring_elements::<SIMDUnit, Shake128X4, COLUMNS_IN_A, ROWS_IN_A>(
        seed,
        generate_domain_separator(0, 0),
        generate_domain_separator(0, 1),
        generate_domain_separator(0, 2),
        generate_domain_separator(0, 3),
        &[(0, 0), (0, 1), (0, 2), (0, 3)],
        matrix,
    );

    sample_four_ring_elements::<SIMDUnit, Shake128X4, COLUMNS_IN_A, ROWS_IN_A>(
        seed,
        generate_domain_separator(1, 0),
        generate_domain_separator(1, 1),
        generate_domain_separator(1, 2),
        generate_domain_separator(1, 3),
        &[(1, 0), (1, 1), (1, 2), (1, 3)],
        matrix,
    );

    sample_four_ring_elements::<SIMDUnit, Shake128X4, COLUMNS_IN_A, ROWS_IN_A>(
        seed,
        generate_domain_separator(2, 0),
        generate_domain_separator(2, 1),
        generate_domain_separator(2, 2),
        generate_domain_separator(2, 3),
        &[(2, 0), (2, 1), (2, 2), (2, 3)],
        matrix,
    );

    sample_four_ring_elements::<SIMDUnit, Shake128X4, COLUMNS_IN_A, ROWS_IN_A>(
        seed,
        generate_domain_separator(3, 0),
        generate_domain_separator(3, 1),
        generate_domain_separator(3, 2),
        generate_domain_separator(3, 3),
        &[(3, 0), (3, 1), (3, 2), (3, 3)],
        matrix,
    );
}

#[inline(always)]
pub(crate) fn matrix_6_by_5<
    SIMDUnit: Operations,
    Shake128X4: shake128::XofX4,
    const ROWS_IN_A: usize,
    const COLUMNS_IN_A: usize,
>(
    seed: [u8; 34],
    matrix: &mut Matrix<SIMDUnit, ROWS_IN_A, COLUMNS_IN_A>,
) {
    sample_four_ring_elements::<SIMDUnit, Shake128X4, COLUMNS_IN_A, ROWS_IN_A>(
        seed,
        generate_domain_separator(0, 0),
        generate_domain_separator(0, 1),
        generate_domain_separator(0, 2),
        generate_domain_separator(0, 3),
        &[(0, 0), (0, 1), (0, 2), (0, 3)],
        matrix,
    );

    sample_four_ring_elements::<SIMDUnit, Shake128X4, COLUMNS_IN_A, ROWS_IN_A>(
        seed,
        generate_domain_separator(0, 4),
        generate_domain_separator(1, 0),
        generate_domain_separator(1, 1),
        generate_domain_separator(1, 2),
        &[(0, 4), (1, 0), (1, 1), (1, 2)],
        matrix,
    );

    sample_four_ring_elements::<SIMDUnit, Shake128X4, COLUMNS_IN_A, ROWS_IN_A>(
        seed,
        generate_domain_separator(1, 3),
        generate_domain_separator(1, 4),
        generate_domain_separator(2, 0),
        generate_domain_separator(2, 1),
        &[(1, 3), (1, 4), (2, 0), (2, 1)],
        matrix,
    );

    sample_four_ring_elements::<SIMDUnit, Shake128X4, COLUMNS_IN_A, ROWS_IN_A>(
        seed,
        generate_domain_separator(2, 2),
        generate_domain_separator(2, 3),
        generate_domain_separator(2, 4),
        generate_domain_separator(3, 0),
        &[(2, 2), (2, 3), (2, 4), (3, 0)],
        matrix,
    );

    sample_four_ring_elements::<SIMDUnit, Shake128X4, COLUMNS_IN_A, ROWS_IN_A>(
        seed,
        generate_domain_separator(3, 1),
        generate_domain_separator(3, 2),
        generate_domain_separator(3, 3),
        generate_domain_separator(3, 4),
        &[(3, 1), (3, 2), (3, 3), (3, 4)],
        matrix,
    );

    sample_four_ring_elements::<SIMDUnit, Shake128X4, COLUMNS_IN_A, ROWS_IN_A>(
        seed,
        generate_domain_separator(4, 0),
        generate_domain_separator(4, 1),
        generate_domain_separator(4, 2),
        generate_domain_separator(4, 3),
        &[(4, 0), (4, 1), (4, 2), (4, 3)],
        matrix,
    );

    sample_four_ring_elements::<SIMDUnit, Shake128X4, COLUMNS_IN_A, ROWS_IN_A>(
        seed,
        generate_domain_separator(4, 4),
        generate_domain_separator(5, 0),
        generate_domain_separator(5, 1),
        generate_domain_separator(5, 2),
        &[(4, 4), (5, 0), (5, 1), (5, 2)],
        matrix,
    );

    // The the last 2 sampled ring elements are discarded here.
    sample_four_ring_elements::<SIMDUnit, Shake128X4, COLUMNS_IN_A, ROWS_IN_A>(
        seed,
        generate_domain_separator(5, 3),
        generate_domain_separator(5, 4),
        generate_domain_separator(5, 5),
        generate_domain_separator(5, 6),
        &[(5, 3), (5, 4)],
        matrix,
    );
}

#[inline(always)]
pub(crate) fn matrix_8_by_7<
    SIMDUnit: Operations,
    Shake128X4: shake128::XofX4,
    const ROWS_IN_A: usize,
    const COLUMNS_IN_A: usize,
>(
    seed: [u8; 34],
    matrix: &mut Matrix<SIMDUnit, ROWS_IN_A, COLUMNS_IN_A>,
) {
    sample_four_ring_elements::<SIMDUnit, Shake128X4, COLUMNS_IN_A, ROWS_IN_A>(
        seed,
        generate_domain_separator(0, 0),
        generate_domain_separator(0, 1),
        generate_domain_separator(0, 2),
        generate_domain_separator(0, 3),
        &[(0, 0), (0, 1), (0, 2), (0, 3)],
        matrix,
    );

    sample_four_ring_elements::<SIMDUnit, Shake128X4, COLUMNS_IN_A, ROWS_IN_A>(
        seed,
        generate_domain_separator(0, 4),
        generate_domain_separator(0, 5),
        generate_domain_separator(0, 6),
        generate_domain_separator(1, 0),
        &[(0, 4), (0, 5), (0, 6), (1, 0)],
        matrix,
    );

    sample_four_ring_elements::<SIMDUnit, Shake128X4, COLUMNS_IN_A, ROWS_IN_A>(
        seed,
        generate_domain_separator(1, 1),
        generate_domain_separator(1, 2),
        generate_domain_separator(1, 3),
        generate_domain_separator(1, 4),
        &[(1, 1), (1, 2), (1, 3), (1, 4)],
        matrix,
    );

    sample_four_ring_elements::<SIMDUnit, Shake128X4, COLUMNS_IN_A, ROWS_IN_A>(
        seed,
        generate_domain_separator(1, 5),
        generate_domain_separator(1, 6),
        generate_domain_separator(2, 0),
        generate_domain_separator(2, 1),
        &[(1, 5), (1, 6), (2, 0), (2, 1)],
        matrix,
    );

    sample_four_ring_elements::<SIMDUnit, Shake128X4, COLUMNS_IN_A, ROWS_IN_A>(
        seed,
        generate_domain_separator(2, 2),
        generate_domain_separator(2, 3),
        generate_domain_separator(2, 4),
        generate_domain_separator(2, 5),
        &[(2, 2), (2, 3), (2, 4), (2, 5)],
        matrix,
    );

    sample_four_ring_elements::<SIMDUnit, Shake128X4, COLUMNS_IN_A, ROWS_IN_A>(
        seed,
        generate_domain_separator(2, 6),
        generate_domain_separator(3, 0),
        generate_domain_separator(3, 1),
        generate_domain_separator(3, 2),
        &[(2, 6), (3, 0), (3, 1), (3, 2)],
        matrix,
    );

    sample_four_ring_elements::<SIMDUnit, Shake128X4, COLUMNS_IN_A, ROWS_IN_A>(
        seed,
        generate_domain_separator(3, 3),
        generate_domain_separator(3, 4),
        generate_domain_separator(3, 5),
        generate_domain_separator(3, 6),
        &[(3, 3), (3, 4), (3, 5), (3, 6)],
        matrix,
    );

    sample_four_ring_elements::<SIMDUnit, Shake128X4, COLUMNS_IN_A, ROWS_IN_A>(
        seed,
        generate_domain_separator(4, 0),
        generate_domain_separator(4, 1),
        generate_domain_separator(4, 2),
        generate_domain_separator(4, 3),
        &[(4, 0), (4, 1), (4, 2), (4, 3)],
        matrix,
    );

    sample_four_ring_elements::<SIMDUnit, Shake128X4, COLUMNS_IN_A, ROWS_IN_A>(
        seed,
        generate_domain_separator(4, 4),
        generate_domain_separator(4, 5),
        generate_domain_separator(4, 6),
        generate_domain_separator(5, 0),
        &[(4, 4), (4, 5), (4, 6), (5, 0)],
        matrix,
    );

    sample_four_ring_elements::<SIMDUnit, Shake128X4, COLUMNS_IN_A, ROWS_IN_A>(
        seed,
        generate_domain_separator(5, 1),
        generate_domain_separator(5, 2),
        generate_domain_separator(5, 3),
        generate_domain_separator(5, 4),
        &[(5, 1), (5, 2), (5, 3), (5, 4)],
        matrix,
    );

    sample_four_ring_elements::<SIMDUnit, Shake128X4, COLUMNS_IN_A, ROWS_IN_A>(
        seed,
        generate_domain_separator(5, 5),
        generate_domain_separator(5, 6),
        generate_domain_separator(6, 0),
        generate_domain_separator(6, 1),
        &[(5, 5), (5, 6), (6, 0), (6, 1)],
        matrix,
    );

    sample_four_ring_elements::<SIMDUnit, Shake128X4, COLUMNS_IN_A, ROWS_IN_A>(
        seed,
        generate_domain_separator(6, 2),
        generate_domain_separator(6, 3),
        generate_domain_separator(6, 4),
        generate_domain_separator(6, 5),
        &[(6, 2), (6, 3), (6, 4), (6, 5)],
        matrix,
    );

    sample_four_ring_elements::<SIMDUnit, Shake128X4, COLUMNS_IN_A, ROWS_IN_A>(
        seed,
        generate_domain_separator(6, 6),
        generate_domain_separator(7, 0),
        generate_domain_separator(7, 1),
        generate_domain_separator(7, 2),
        &[(6, 6), (7, 0), (7, 1), (7, 2)],
        matrix,
    );

    sample_four_ring_elements::<SIMDUnit, Shake128X4, COLUMNS_IN_A, ROWS_IN_A>(
        seed,
        generate_domain_separator(7, 3),
        generate_domain_separator(7, 4),
        generate_domain_separator(7, 5),
        generate_domain_separator(7, 6),
        &[(7, 3), (7, 4), (7, 5), (7, 6)],
        matrix,
    );
}

#[inline(always)]
pub(crate) fn matrix<
    SIMDUnit: Operations,
    Shake128X4: shake128::XofX4,
    const ROWS_IN_A: usize,
    const COLUMNS_IN_A: usize,
>(
    seed: [u8; 34],
    matrix: &mut Matrix<SIMDUnit, ROWS_IN_A, COLUMNS_IN_A>,
) {
    match (ROWS_IN_A as u8, COLUMNS_IN_A as u8) {
        (4, 4) => matrix_4_by_4::<SIMDUnit, Shake128X4, ROWS_IN_A, COLUMNS_IN_A>(seed, matrix),
        (6, 5) => matrix_6_by_5::<SIMDUnit, Shake128X4, ROWS_IN_A, COLUMNS_IN_A>(seed, matrix),
        (8, 7) => matrix_8_by_7::<SIMDUnit, Shake128X4, ROWS_IN_A, COLUMNS_IN_A>(seed, matrix),
        _ => unreachable!(),
    }
}

#[inline(always)]
fn sample_s1_and_s2_4_by_4<
    SIMDUnit: Operations,
    Shake256X4: shake256::XofX4,
    const ETA: usize,
    const S1_DIMENSION: usize,
    const S2_DIMENSION: usize,
>(
    seed_base: [u8; 66],
) -> (
    [PolynomialRingElement<SIMDUnit>; S1_DIMENSION],
    [PolynomialRingElement<SIMDUnit>; S2_DIMENSION],
) {
    let mut s1 = [PolynomialRingElement::<SIMDUnit>::ZERO(); S1_DIMENSION];
    let mut s2 = [PolynomialRingElement::<SIMDUnit>::ZERO(); S2_DIMENSION];

    sample_four_error_ring_elements::<SIMDUnit, Shake256X4, ETA, S1_DIMENSION, S2_DIMENSION>(
        seed_base,
        0,
        1,
        2,
        3,
        &[(0, 0), (0, 1), (0, 2), (0, 3)],
        &mut s1,
        &mut s2,
    );

    sample_four_error_ring_elements::<SIMDUnit, Shake256X4, ETA, S1_DIMENSION, S2_DIMENSION>(
        seed_base,
        4,
        5,
        6,
        7,
        &[(1, 0), (1, 1), (1, 2), (1, 3)],
        &mut s1,
        &mut s2,
    );

    (s1, s2)
}
#[inline(always)]
fn sample_s1_and_s2_5_by_6<
    SIMDUnit: Operations,
    Shake256X4: shake256::XofX4,
    const ETA: usize,
    const S1_DIMENSION: usize,
    const S2_DIMENSION: usize,
>(
    seed_base: [u8; 66],
) -> (
    [PolynomialRingElement<SIMDUnit>; S1_DIMENSION],
    [PolynomialRingElement<SIMDUnit>; S2_DIMENSION],
) {
    let mut s1 = [PolynomialRingElement::<SIMDUnit>::ZERO(); S1_DIMENSION];
    let mut s2 = [PolynomialRingElement::<SIMDUnit>::ZERO(); S2_DIMENSION];

    sample_four_error_ring_elements::<SIMDUnit, Shake256X4, ETA, S1_DIMENSION, S2_DIMENSION>(
        seed_base,
        0,
        1,
        2,
        3,
        &[(0, 0), (0, 1), (0, 2), (0, 3)],
        &mut s1,
        &mut s2,
    );

    sample_four_error_ring_elements::<SIMDUnit, Shake256X4, ETA, S1_DIMENSION, S2_DIMENSION>(
        seed_base,
        4,
        5,
        6,
        7,
        &[(0, 4), (1, 0), (1, 1), (1, 2)],
        &mut s1,
        &mut s2,
    );

    sample_four_error_ring_elements::<SIMDUnit, Shake256X4, ETA, S1_DIMENSION, S2_DIMENSION>(
        seed_base,
        8,
        9,
        10,
        11,
        &[(1, 3), (1, 4), (1, 5)],
        &mut s1,
        &mut s2,
    );

    (s1, s2)
}
#[inline(always)]
fn sample_s1_and_s2_7_by_8<
    SIMDUnit: Operations,
    Shake256X4: shake256::XofX4,
    const ETA: usize,
    const S1_DIMENSION: usize,
    const S2_DIMENSION: usize,
>(
    seed_base: [u8; 66],
) -> (
    [PolynomialRingElement<SIMDUnit>; S1_DIMENSION],
    [PolynomialRingElement<SIMDUnit>; S2_DIMENSION],
) {
    let mut s1 = [PolynomialRingElement::<SIMDUnit>::ZERO(); S1_DIMENSION];
    let mut s2 = [PolynomialRingElement::<SIMDUnit>::ZERO(); S2_DIMENSION];

    sample_four_error_ring_elements::<SIMDUnit, Shake256X4, ETA, S1_DIMENSION, S2_DIMENSION>(
        seed_base,
        0,
        1,
        2,
        3,
        &[(0, 0), (0, 1), (0, 2), (0, 3)],
        &mut s1,
        &mut s2,
    );

    sample_four_error_ring_elements::<SIMDUnit, Shake256X4, ETA, S1_DIMENSION, S2_DIMENSION>(
        seed_base,
        4,
        5,
        6,
        7,
        &[(0, 4), (0, 5), (0, 6), (1, 0)],
        &mut s1,
        &mut s2,
    );

    sample_four_error_ring_elements::<SIMDUnit, Shake256X4, ETA, S1_DIMENSION, S2_DIMENSION>(
        seed_base,
        8,
        9,
        10,
        11,
        &[(1, 1), (1, 2), (1, 3), (1, 4)],
        &mut s1,
        &mut s2,
    );

    sample_four_error_ring_elements::<SIMDUnit, Shake256X4, ETA, S1_DIMENSION, S2_DIMENSION>(
        seed_base,
        12,
        13,
        14,
        15,
        &[(1, 5), (1, 6), (1, 7)],
        &mut s1,
        &mut s2,
    );

    (s1, s2)
}

#[inline(always)]
pub(crate) fn sample_s1_and_s2<
    SIMDUnit: Operations,
    Shake256X4: shake256::XofX4,
    const ETA: usize,
    const S1_DIMENSION: usize,
    const S2_DIMENSION: usize,
>(
    seed: [u8; 66],
) -> (
    [PolynomialRingElement<SIMDUnit>; S1_DIMENSION],
    [PolynomialRingElement<SIMDUnit>; S2_DIMENSION],
) {
    match (S1_DIMENSION as u8, S2_DIMENSION as u8) {
        (4, 4) => {
            sample_s1_and_s2_4_by_4::<SIMDUnit, Shake256X4, ETA, S1_DIMENSION, S2_DIMENSION>(seed)
        }
        (5, 6) => {
            sample_s1_and_s2_5_by_6::<SIMDUnit, Shake256X4, ETA, S1_DIMENSION, S2_DIMENSION>(seed)
        }
        (7, 8) => {
            sample_s1_and_s2_7_by_8::<SIMDUnit, Shake256X4, ETA, S1_DIMENSION, S2_DIMENSION>(seed)
        }
        _ => unreachable!(),
    }
}
