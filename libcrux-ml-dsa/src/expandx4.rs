use crate::{
    hash_functions::shake128, polynomial::PolynomialRingElement, sample::sample_four_ring_elements,
    simd::traits::Operations,
};

#[inline(always)]
fn generate_domain_separator(row: u8, column: u8) -> u16 {
    (column as u16) | ((row as u16) << 8)
}

#[allow(non_snake_case)]
#[inline(always)]
pub(crate) fn matrix_A_4_by_4<
    SIMDUnit: Operations,
    Shake128X4: shake128::XofX4,
    const ROWS_IN_A: usize,
    const COLUMNS_IN_A: usize,
>(
    seed: [u8; 34],
) -> [[PolynomialRingElement<SIMDUnit>; COLUMNS_IN_A]; ROWS_IN_A] {
    let mut A = [[PolynomialRingElement::<SIMDUnit>::ZERO(); COLUMNS_IN_A]; ROWS_IN_A];

    let four_ring_elements = sample_four_ring_elements::<SIMDUnit, Shake128X4>(
        seed,
        generate_domain_separator(0, 0),
        generate_domain_separator(0, 1),
        generate_domain_separator(0, 2),
        generate_domain_separator(0, 3),
    );
    A[0][0] = four_ring_elements.0;
    A[0][1] = four_ring_elements.1;
    A[0][2] = four_ring_elements.2;
    A[0][3] = four_ring_elements.3;

    let four_ring_elements = sample_four_ring_elements::<SIMDUnit, Shake128X4>(
        seed,
        generate_domain_separator(1, 0),
        generate_domain_separator(1, 1),
        generate_domain_separator(1, 2),
        generate_domain_separator(1, 3),
    );
    A[1][0] = four_ring_elements.0;
    A[1][1] = four_ring_elements.1;
    A[1][2] = four_ring_elements.2;
    A[1][3] = four_ring_elements.3;

    let four_ring_elements = sample_four_ring_elements::<SIMDUnit, Shake128X4>(
        seed,
        generate_domain_separator(2, 0),
        generate_domain_separator(2, 1),
        generate_domain_separator(2, 2),
        generate_domain_separator(2, 3),
    );
    A[2][0] = four_ring_elements.0;
    A[2][1] = four_ring_elements.1;
    A[2][2] = four_ring_elements.2;
    A[2][3] = four_ring_elements.3;

    let four_ring_elements = sample_four_ring_elements::<SIMDUnit, Shake128X4>(
        seed,
        generate_domain_separator(3, 0),
        generate_domain_separator(3, 1),
        generate_domain_separator(3, 2),
        generate_domain_separator(3, 3),
    );
    A[3][0] = four_ring_elements.0;
    A[3][1] = four_ring_elements.1;
    A[3][2] = four_ring_elements.2;
    A[3][3] = four_ring_elements.3;

    A
}

#[allow(non_snake_case)]
#[inline(always)]
pub(crate) fn matrix_A_6_by_5<
    SIMDUnit: Operations,
    Shake128X4: shake128::XofX4,
    const ROWS_IN_A: usize,
    const COLUMNS_IN_A: usize,
>(
    seed: [u8; 34],
) -> [[PolynomialRingElement<SIMDUnit>; COLUMNS_IN_A]; ROWS_IN_A] {
    let mut A = [[PolynomialRingElement::<SIMDUnit>::ZERO(); COLUMNS_IN_A]; ROWS_IN_A];

    let four_ring_elements = sample_four_ring_elements::<SIMDUnit, Shake128X4>(
        seed,
        generate_domain_separator(0, 0),
        generate_domain_separator(0, 1),
        generate_domain_separator(0, 2),
        generate_domain_separator(0, 3),
    );
    A[0][0] = four_ring_elements.0;
    A[0][1] = four_ring_elements.1;
    A[0][2] = four_ring_elements.2;
    A[0][3] = four_ring_elements.3;

    let four_ring_elements = sample_four_ring_elements::<SIMDUnit, Shake128X4>(
        seed,
        generate_domain_separator(0, 4),
        generate_domain_separator(1, 0),
        generate_domain_separator(1, 1),
        generate_domain_separator(1, 2),
    );
    A[0][4] = four_ring_elements.0;
    A[1][0] = four_ring_elements.1;
    A[1][1] = four_ring_elements.2;
    A[1][2] = four_ring_elements.3;

    let four_ring_elements = sample_four_ring_elements::<SIMDUnit, Shake128X4>(
        seed,
        generate_domain_separator(1, 3),
        generate_domain_separator(1, 4),
        generate_domain_separator(2, 0),
        generate_domain_separator(2, 1),
    );
    A[1][3] = four_ring_elements.0;
    A[1][4] = four_ring_elements.1;
    A[2][0] = four_ring_elements.2;
    A[2][1] = four_ring_elements.3;

    let four_ring_elements = sample_four_ring_elements::<SIMDUnit, Shake128X4>(
        seed,
        generate_domain_separator(2, 2),
        generate_domain_separator(2, 3),
        generate_domain_separator(2, 4),
        generate_domain_separator(3, 0),
    );
    A[2][2] = four_ring_elements.0;
    A[2][3] = four_ring_elements.1;
    A[2][4] = four_ring_elements.2;
    A[3][0] = four_ring_elements.3;

    let four_ring_elements = sample_four_ring_elements::<SIMDUnit, Shake128X4>(
        seed,
        generate_domain_separator(3, 1),
        generate_domain_separator(3, 2),
        generate_domain_separator(3, 3),
        generate_domain_separator(3, 4),
    );
    A[3][1] = four_ring_elements.0;
    A[3][2] = four_ring_elements.1;
    A[3][3] = four_ring_elements.2;
    A[3][4] = four_ring_elements.3;

    let four_ring_elements = sample_four_ring_elements::<SIMDUnit, Shake128X4>(
        seed,
        generate_domain_separator(4, 0),
        generate_domain_separator(4, 1),
        generate_domain_separator(4, 2),
        generate_domain_separator(4, 3),
    );
    A[4][0] = four_ring_elements.0;
    A[4][1] = four_ring_elements.1;
    A[4][2] = four_ring_elements.2;
    A[4][3] = four_ring_elements.3;

    let four_ring_elements = sample_four_ring_elements::<SIMDUnit, Shake128X4>(
        seed,
        generate_domain_separator(4, 4),
        generate_domain_separator(5, 0),
        generate_domain_separator(5, 1),
        generate_domain_separator(5, 2),
    );
    A[4][4] = four_ring_elements.0;
    A[5][0] = four_ring_elements.1;
    A[5][1] = four_ring_elements.2;
    A[5][2] = four_ring_elements.3;

    // The the last 2 sampled ring elements are discarded here.
    let four_ring_elements = sample_four_ring_elements::<SIMDUnit, Shake128X4>(
        seed,
        generate_domain_separator(5, 3),
        generate_domain_separator(5, 4),
        generate_domain_separator(0, 0),
        generate_domain_separator(0, 0),
    );
    A[5][3] = four_ring_elements.0;
    A[5][4] = four_ring_elements.1;

    A
}

#[allow(non_snake_case)]
#[inline(always)]
pub(crate) fn matrix_A_8_by_7<
    SIMDUnit: Operations,
    Shake128X4: shake128::XofX4,
    const ROWS_IN_A: usize,
    const COLUMNS_IN_A: usize,
>(
    seed: [u8; 34],
) -> [[PolynomialRingElement<SIMDUnit>; COLUMNS_IN_A]; ROWS_IN_A] {
    let mut A = [[PolynomialRingElement::<SIMDUnit>::ZERO(); COLUMNS_IN_A]; ROWS_IN_A];

    let four_ring_elements = sample_four_ring_elements::<SIMDUnit, Shake128X4>(
        seed,
        generate_domain_separator(0, 0),
        generate_domain_separator(0, 1),
        generate_domain_separator(0, 2),
        generate_domain_separator(0, 3),
    );
    A[0][0] = four_ring_elements.0;
    A[0][1] = four_ring_elements.1;
    A[0][2] = four_ring_elements.2;
    A[0][3] = four_ring_elements.3;

    let four_ring_elements = sample_four_ring_elements::<SIMDUnit, Shake128X4>(
        seed,
        generate_domain_separator(0, 4),
        generate_domain_separator(0, 5),
        generate_domain_separator(0, 6),
        generate_domain_separator(1, 0),
    );
    A[0][4] = four_ring_elements.0;
    A[0][5] = four_ring_elements.1;
    A[0][6] = four_ring_elements.2;
    A[1][0] = four_ring_elements.3;

    let four_ring_elements = sample_four_ring_elements::<SIMDUnit, Shake128X4>(
        seed,
        generate_domain_separator(1, 1),
        generate_domain_separator(1, 2),
        generate_domain_separator(1, 3),
        generate_domain_separator(1, 4),
    );
    A[1][1] = four_ring_elements.0;
    A[1][2] = four_ring_elements.1;
    A[1][3] = four_ring_elements.2;
    A[1][4] = four_ring_elements.3;

    let four_ring_elements = sample_four_ring_elements::<SIMDUnit, Shake128X4>(
        seed,
        generate_domain_separator(1, 5),
        generate_domain_separator(1, 6),
        generate_domain_separator(2, 0),
        generate_domain_separator(2, 1),
    );
    A[1][5] = four_ring_elements.0;
    A[1][6] = four_ring_elements.1;
    A[2][0] = four_ring_elements.2;
    A[2][1] = four_ring_elements.3;

    let four_ring_elements = sample_four_ring_elements::<SIMDUnit, Shake128X4>(
        seed,
        generate_domain_separator(2, 2),
        generate_domain_separator(2, 3),
        generate_domain_separator(2, 4),
        generate_domain_separator(2, 5),
    );
    A[2][2] = four_ring_elements.0;
    A[2][3] = four_ring_elements.1;
    A[2][4] = four_ring_elements.2;
    A[2][5] = four_ring_elements.3;

    let four_ring_elements = sample_four_ring_elements::<SIMDUnit, Shake128X4>(
        seed,
        generate_domain_separator(2, 6),
        generate_domain_separator(3, 0),
        generate_domain_separator(3, 1),
        generate_domain_separator(3, 2),
    );
    A[2][6] = four_ring_elements.0;
    A[3][0] = four_ring_elements.1;
    A[3][1] = four_ring_elements.2;
    A[3][2] = four_ring_elements.3;

    let four_ring_elements = sample_four_ring_elements::<SIMDUnit, Shake128X4>(
        seed,
        generate_domain_separator(3, 3),
        generate_domain_separator(3, 4),
        generate_domain_separator(3, 5),
        generate_domain_separator(3, 6),
    );
    A[3][3] = four_ring_elements.0;
    A[3][4] = four_ring_elements.1;
    A[3][5] = four_ring_elements.2;
    A[3][6] = four_ring_elements.3;

    let four_ring_elements = sample_four_ring_elements::<SIMDUnit, Shake128X4>(
        seed,
        generate_domain_separator(4, 0),
        generate_domain_separator(4, 1),
        generate_domain_separator(4, 2),
        generate_domain_separator(4, 3),
    );
    A[4][0] = four_ring_elements.0;
    A[4][1] = four_ring_elements.1;
    A[4][2] = four_ring_elements.2;
    A[4][3] = four_ring_elements.3;

    let four_ring_elements = sample_four_ring_elements::<SIMDUnit, Shake128X4>(
        seed,
        generate_domain_separator(4, 4),
        generate_domain_separator(4, 5),
        generate_domain_separator(4, 6),
        generate_domain_separator(5, 0),
    );
    A[4][4] = four_ring_elements.0;
    A[4][5] = four_ring_elements.1;
    A[4][6] = four_ring_elements.2;
    A[5][0] = four_ring_elements.3;

    let four_ring_elements = sample_four_ring_elements::<SIMDUnit, Shake128X4>(
        seed,
        generate_domain_separator(5, 1),
        generate_domain_separator(5, 2),
        generate_domain_separator(5, 3),
        generate_domain_separator(5, 4),
    );
    A[5][1] = four_ring_elements.0;
    A[5][2] = four_ring_elements.1;
    A[5][3] = four_ring_elements.2;
    A[5][4] = four_ring_elements.3;

    let four_ring_elements = sample_four_ring_elements::<SIMDUnit, Shake128X4>(
        seed,
        generate_domain_separator(5, 5),
        generate_domain_separator(5, 6),
        generate_domain_separator(6, 0),
        generate_domain_separator(6, 1),
    );
    A[5][5] = four_ring_elements.0;
    A[5][6] = four_ring_elements.1;
    A[6][0] = four_ring_elements.2;
    A[6][1] = four_ring_elements.3;

    let four_ring_elements = sample_four_ring_elements::<SIMDUnit, Shake128X4>(
        seed,
        generate_domain_separator(6, 2),
        generate_domain_separator(6, 3),
        generate_domain_separator(6, 4),
        generate_domain_separator(6, 5),
    );
    A[6][2] = four_ring_elements.0;
    A[6][3] = four_ring_elements.1;
    A[6][4] = four_ring_elements.2;
    A[6][5] = four_ring_elements.3;

    let four_ring_elements = sample_four_ring_elements::<SIMDUnit, Shake128X4>(
        seed,
        generate_domain_separator(6, 6),
        generate_domain_separator(7, 0),
        generate_domain_separator(7, 1),
        generate_domain_separator(7, 2),
    );
    A[6][6] = four_ring_elements.0;
    A[7][0] = four_ring_elements.1;
    A[7][1] = four_ring_elements.2;
    A[7][2] = four_ring_elements.3;

    let four_ring_elements = sample_four_ring_elements::<SIMDUnit, Shake128X4>(
        seed,
        generate_domain_separator(7, 3),
        generate_domain_separator(7, 4),
        generate_domain_separator(7, 5),
        generate_domain_separator(7, 6),
    );
    A[7][3] = four_ring_elements.0;
    A[7][4] = four_ring_elements.1;
    A[7][5] = four_ring_elements.2;
    A[7][6] = four_ring_elements.3;

    A
}

#[allow(non_snake_case)]
pub(crate) fn matrix_A<
    SIMDUnit: Operations,
    Shake128X4: shake128::XofX4,
    const ROWS_IN_A: usize,
    const COLUMNS_IN_A: usize,
>(
    seed: [u8; 34],
) -> [[PolynomialRingElement<SIMDUnit>; COLUMNS_IN_A]; ROWS_IN_A] {
    match (ROWS_IN_A, COLUMNS_IN_A) {
        (4, 4) => matrix_A_4_by_4::<SIMDUnit, Shake128X4, ROWS_IN_A, COLUMNS_IN_A>(seed),
        (6, 5) => matrix_A_6_by_5::<SIMDUnit, Shake128X4, ROWS_IN_A, COLUMNS_IN_A>(seed),
        (8, 7) => matrix_A_8_by_7::<SIMDUnit, Shake128X4, ROWS_IN_A, COLUMNS_IN_A>(seed),
        _ => unreachable!(),
    }
}
