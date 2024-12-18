use crate::{
    hash_functions::{shake128, shake256},
    polynomial::PolynomialRingElement,
    sample::{
        sample_four_error_ring_elements, sample_four_ring_elements, SampleArgs, SampledRingElement,
    },
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

#[allow(non_snake_case)]
#[inline(always)]
pub(crate) fn matrix_A_4_by_4<
    SIMDUnit: Operations,
    const ROWS_IN_A: usize,
    const COLUMNS_IN_A: usize,
>(
    seed: [u8; 34],
) {
    todo!()
    // let mut A: Matrix<SIMDUnit, ROWS_IN_A, COLUMNS_IN_A> =
    //     [[PolynomialRingElement::<SIMDUnit>::ZERO(); COLUMNS_IN_A]; ROWS_IN_A];

    // let mut rand_stack = (
    //     [0u8; shake128::FIVE_BLOCKS_SIZE],
    //     [0u8; shake128::FIVE_BLOCKS_SIZE],
    //     [0u8; shake128::FIVE_BLOCKS_SIZE],
    //     [0u8; shake128::FIVE_BLOCKS_SIZE],
    // );
    // let mut tmp_stack = [
    //     ElementOut::new(),
    //     ElementOut::new(),
    //     ElementOut::new(),
    //     ElementOut::new(),
    // ];
    // let mut memory = SampleArgs::new(
    //     &mut rand_stack,
    //     &mut tmp_stack,
    //     &mut A,
    //     &[(0, 0), (0, 1), (0, 2), (0, 3)],
    // );
    // sample_four_ring_elements::<SIMDUnit, ROWS_IN_A, COLUMNS_IN_A>(
    //     seed,
    //     generate_domain_separator(0, 0),
    //     generate_domain_separator(0, 1),
    //     generate_domain_separator(0, 2),
    //     generate_domain_separator(0, 3),
    //     &mut memory,
    // );

    // memory.indices = &[(1, 0), (1, 1), (1, 2), (1, 3)];
    // sample_four_ring_elements::<SIMDUnit, ROWS_IN_A, COLUMNS_IN_A>(
    //     seed,
    //     generate_domain_separator(1, 0),
    //     generate_domain_separator(1, 1),
    //     generate_domain_separator(1, 2),
    //     generate_domain_separator(1, 3),
    //     &mut memory,
    // );

    // memory.indices = &[(2, 0), (2, 1), (2, 2), (2, 3)];
    // sample_four_ring_elements::<SIMDUnit, ROWS_IN_A, COLUMNS_IN_A>(
    //     seed,
    //     generate_domain_separator(2, 0),
    //     generate_domain_separator(2, 1),
    //     generate_domain_separator(2, 2),
    //     generate_domain_separator(2, 3),
    //     &mut memory,
    // );

    // memory.indices = &[(3, 0), (3, 1), (3, 2), (3, 3)];
    // sample_four_ring_elements::<SIMDUnit, ROWS_IN_A, COLUMNS_IN_A>(
    //     seed,
    //     generate_domain_separator(3, 0),
    //     generate_domain_separator(3, 1),
    //     generate_domain_separator(3, 2),
    //     generate_domain_separator(3, 3),
    //     &mut memory,
    // );

    // A
}

#[allow(non_snake_case)]
#[inline(always)]
#[allow(unsafe_code)]
pub(crate) fn matrix_A_6_by_5<
    SIMDUnit: Operations,
    const ROWS_IN_A: usize,
    const COLUMNS_IN_A: usize,
>(
    seed: [u8; 34],
    matrix: &mut [SampledRingElement<SIMDUnit>],
) {
    // let mut A = [[PolynomialRingElement::<SIMDUnit>::ZERO(); COLUMNS_IN_A]; ROWS_IN_A];
    // let mut matrix = [SampledRingElement::<SIMDUnit>::new(); 32];

    let mut rand_stack = (
        [0u8; shake128::FIVE_BLOCKS_SIZE],
        [0u8; shake128::FIVE_BLOCKS_SIZE],
        [0u8; shake128::FIVE_BLOCKS_SIZE],
        [0u8; shake128::FIVE_BLOCKS_SIZE],
    );
    let mut memory = SampleArgs::new(&mut rand_stack, matrix, 0);
    sample_four_ring_elements::<SIMDUnit, ROWS_IN_A, COLUMNS_IN_A>(
        seed,
        generate_domain_separator(0, 0),
        generate_domain_separator(0, 1),
        generate_domain_separator(0, 2),
        generate_domain_separator(0, 3),
        &mut memory,
    );

    memory.start_index = 4;
    sample_four_ring_elements::<SIMDUnit, ROWS_IN_A, COLUMNS_IN_A>(
        seed,
        generate_domain_separator(0, 4),
        generate_domain_separator(1, 0),
        generate_domain_separator(1, 1),
        generate_domain_separator(1, 2),
        &mut memory,
    );

    memory.start_index = 8;
    sample_four_ring_elements::<SIMDUnit, ROWS_IN_A, COLUMNS_IN_A>(
        seed,
        generate_domain_separator(1, 3),
        generate_domain_separator(1, 4),
        generate_domain_separator(2, 0),
        generate_domain_separator(2, 1),
        &mut memory,
    );

    memory.start_index = 12;
    sample_four_ring_elements::<SIMDUnit, ROWS_IN_A, COLUMNS_IN_A>(
        seed,
        generate_domain_separator(2, 2),
        generate_domain_separator(2, 3),
        generate_domain_separator(2, 4),
        generate_domain_separator(3, 0),
        &mut memory,
    );

    memory.start_index = 16;
    sample_four_ring_elements::<SIMDUnit, ROWS_IN_A, COLUMNS_IN_A>(
        seed,
        generate_domain_separator(3, 1),
        generate_domain_separator(3, 2),
        generate_domain_separator(3, 3),
        generate_domain_separator(3, 4),
        &mut memory,
    );

    memory.start_index = 20;
    sample_four_ring_elements::<SIMDUnit, ROWS_IN_A, COLUMNS_IN_A>(
        seed,
        generate_domain_separator(4, 0),
        generate_domain_separator(4, 1),
        generate_domain_separator(4, 2),
        generate_domain_separator(4, 3),
        &mut memory,
    );

    memory.start_index = 24;
    sample_four_ring_elements::<SIMDUnit, ROWS_IN_A, COLUMNS_IN_A>(
        seed,
        generate_domain_separator(4, 4),
        generate_domain_separator(5, 0),
        generate_domain_separator(5, 1),
        generate_domain_separator(5, 2),
        &mut memory,
    );

    // The the last 2 sampled ring elements are discarded here.
    memory.start_index = 28;
    sample_four_ring_elements::<SIMDUnit, ROWS_IN_A, COLUMNS_IN_A>(
        seed,
        generate_domain_separator(5, 3),
        generate_domain_separator(5, 4),
        generate_domain_separator(5, 5),
        generate_domain_separator(5, 6),
        &mut memory,
    );

    // let out = unsafe {
    //     [
    //         [
    //             matrix[0].re,
    //             matrix[1].re,
    //             matrix[2].re,
    //             matrix[3].re,
    //             matrix[4].re,
    //         ],
    //         [
    //             matrix[5 + 0].re,
    //             matrix[5 + 1].re,
    //             matrix[5 + 2].re,
    //             matrix[5 + 3].re,
    //             matrix[5 + 4].re,
    //         ],
    //         [
    //             matrix[2 * 5 + 0].re,
    //             matrix[2 * 5 + 1].re,
    //             matrix[2 * 5 + 2].re,
    //             matrix[2 * 5 + 3].re,
    //             matrix[2 * 5 + 4].re,
    //         ],
    //         [
    //             matrix[3 * 5 + 0].re,
    //             matrix[3 * 5 + 1].re,
    //             matrix[3 * 5 + 2].re,
    //             matrix[3 * 5 + 3].re,
    //             matrix[3 * 5 + 4].re,
    //         ],
    //         [
    //             matrix[4 * 5 + 0].re,
    //             matrix[4 * 5 + 1].re,
    //             matrix[4 * 5 + 2].re,
    //             matrix[4 * 5 + 3].re,
    //             matrix[4 * 5 + 4].re,
    //         ],
    //         [
    //             matrix[5 * 5 + 0].re,
    //             matrix[5 * 5 + 1].re,
    //             matrix[5 * 5 + 2].re,
    //             matrix[5 * 5 + 3].re,
    //             matrix[5 * 5 + 4].re,
    //         ],
    //     ]
    // };

    // unsafe { core::mem::transmute_copy(&out) }
    // core::array::from_fn(|i| core::array::from_fn(|j| unsafe { matrix[i * COLUMNS_IN_A + j].re }))
    // core::array::from_fn(|i| unsafe { matri[i + S1_DIMENSION].re }),
}

#[allow(non_snake_case)]
#[inline(always)]
pub(crate) fn matrix_A_8_by_7<
    SIMDUnit: Operations,
    const ROWS_IN_A: usize,
    const COLUMNS_IN_A: usize,
>(
    seed: [u8; 34],
) {
    todo!()
    // let mut A = [[PolynomialRingElement::<SIMDUnit>::ZERO(); COLUMNS_IN_A]; ROWS_IN_A];

    // let mut rand_stack = (
    //     [0u8; shake128::FIVE_BLOCKS_SIZE],
    //     [0u8; shake128::FIVE_BLOCKS_SIZE],
    //     [0u8; shake128::FIVE_BLOCKS_SIZE],
    //     [0u8; shake128::FIVE_BLOCKS_SIZE],
    // );
    // let mut tmp_stack = [
    //     ElementOut::new(),
    //     ElementOut::new(),
    //     ElementOut::new(),
    //     ElementOut::new(),
    // ];
    // let mut memory = SampleArgs::new(
    //     &mut rand_stack,
    //     &mut tmp_stack,
    //     &mut A,
    //     &[(0, 0), (0, 1), (0, 2), (0, 3)],
    // );

    // sample_four_ring_elements::<SIMDUnit, ROWS_IN_A, COLUMNS_IN_A>(
    //     seed,
    //     generate_domain_separator(0, 0),
    //     generate_domain_separator(0, 1),
    //     generate_domain_separator(0, 2),
    //     generate_domain_separator(0, 3),
    //     &mut memory,
    // );

    // memory.indices = &[(0, 4), (0, 5), (0, 6), (1, 0)];
    // sample_four_ring_elements::<SIMDUnit, ROWS_IN_A, COLUMNS_IN_A>(
    //     seed,
    //     generate_domain_separator(0, 4),
    //     generate_domain_separator(0, 5),
    //     generate_domain_separator(0, 6),
    //     generate_domain_separator(1, 0),
    //     &mut memory,
    // );

    // memory.indices = &[(1, 1), (1, 2), (1, 3), (1, 4)];
    // sample_four_ring_elements::<SIMDUnit, ROWS_IN_A, COLUMNS_IN_A>(
    //     seed,
    //     generate_domain_separator(1, 1),
    //     generate_domain_separator(1, 2),
    //     generate_domain_separator(1, 3),
    //     generate_domain_separator(1, 4),
    //     &mut memory,
    // );

    // memory.indices = &[(1, 5), (1, 6), (2, 0), (2, 1)];
    // sample_four_ring_elements::<SIMDUnit, ROWS_IN_A, COLUMNS_IN_A>(
    //     seed,
    //     generate_domain_separator(1, 5),
    //     generate_domain_separator(1, 6),
    //     generate_domain_separator(2, 0),
    //     generate_domain_separator(2, 1),
    //     &mut memory,
    // );

    // memory.indices = &[(2, 2), (2, 3), (2, 4), (2, 5)];
    // sample_four_ring_elements::<SIMDUnit, ROWS_IN_A, COLUMNS_IN_A>(
    //     seed,
    //     generate_domain_separator(2, 2),
    //     generate_domain_separator(2, 3),
    //     generate_domain_separator(2, 4),
    //     generate_domain_separator(2, 5),
    //     &mut memory,
    // );

    // memory.indices = &[(2, 6), (3, 0), (3, 1), (3, 2)];
    // sample_four_ring_elements::<SIMDUnit, ROWS_IN_A, COLUMNS_IN_A>(
    //     seed,
    //     generate_domain_separator(2, 6),
    //     generate_domain_separator(3, 0),
    //     generate_domain_separator(3, 1),
    //     generate_domain_separator(3, 2),
    //     &mut memory,
    // );

    // memory.indices = &[(3, 3), (3, 4), (3, 5), (3, 6)];
    // sample_four_ring_elements::<SIMDUnit, ROWS_IN_A, COLUMNS_IN_A>(
    //     seed,
    //     generate_domain_separator(3, 3),
    //     generate_domain_separator(3, 4),
    //     generate_domain_separator(3, 5),
    //     generate_domain_separator(3, 6),
    //     &mut memory,
    // );

    // memory.indices = &[(4, 0), (4, 1), (4, 2), (4, 3)];
    // sample_four_ring_elements::<SIMDUnit, ROWS_IN_A, COLUMNS_IN_A>(
    //     seed,
    //     generate_domain_separator(4, 0),
    //     generate_domain_separator(4, 1),
    //     generate_domain_separator(4, 2),
    //     generate_domain_separator(4, 3),
    //     &mut memory,
    // );

    // memory.indices = &[(4, 4), (4, 5), (4, 6), (5, 0)];
    // sample_four_ring_elements::<SIMDUnit, ROWS_IN_A, COLUMNS_IN_A>(
    //     seed,
    //     generate_domain_separator(4, 4),
    //     generate_domain_separator(4, 5),
    //     generate_domain_separator(4, 6),
    //     generate_domain_separator(5, 0),
    //     &mut memory,
    // );

    // memory.indices = &[(5, 1), (5, 2), (5, 3), (5, 4)];
    // sample_four_ring_elements::<SIMDUnit, ROWS_IN_A, COLUMNS_IN_A>(
    //     seed,
    //     generate_domain_separator(5, 1),
    //     generate_domain_separator(5, 2),
    //     generate_domain_separator(5, 3),
    //     generate_domain_separator(5, 4),
    //     &mut memory,
    // );

    // memory.indices = &[(5, 5), (5, 6), (6, 0), (6, 1)];
    // sample_four_ring_elements::<SIMDUnit, ROWS_IN_A, COLUMNS_IN_A>(
    //     seed,
    //     generate_domain_separator(5, 5),
    //     generate_domain_separator(5, 6),
    //     generate_domain_separator(6, 0),
    //     generate_domain_separator(6, 1),
    //     &mut memory,
    // );

    // memory.indices = &[(6, 2), (6, 3), (6, 4), (6, 5)];
    // sample_four_ring_elements::<SIMDUnit, ROWS_IN_A, COLUMNS_IN_A>(
    //     seed,
    //     generate_domain_separator(6, 2),
    //     generate_domain_separator(6, 3),
    //     generate_domain_separator(6, 4),
    //     generate_domain_separator(6, 5),
    //     &mut memory,
    // );

    // memory.indices = &[(6, 6), (7, 0), (7, 1), (7, 2)];
    // sample_four_ring_elements::<SIMDUnit, ROWS_IN_A, COLUMNS_IN_A>(
    //     seed,
    //     generate_domain_separator(6, 6),
    //     generate_domain_separator(7, 0),
    //     generate_domain_separator(7, 1),
    //     generate_domain_separator(7, 2),
    //     &mut memory,
    // );

    // memory.indices = &[(7, 3), (7, 4), (7, 5), (7, 6)];
    // sample_four_ring_elements::<SIMDUnit, ROWS_IN_A, COLUMNS_IN_A>(
    //     seed,
    //     generate_domain_separator(7, 3),
    //     generate_domain_separator(7, 4),
    //     generate_domain_separator(7, 5),
    //     generate_domain_separator(7, 6),
    //     &mut memory,
    // );

    // A
}

// XXX: of course we can't do this unconditionally, but with the manual monomorphization
//      macro, we could inject this. This gives us +50% faster key generation and +70% signing.
#[cfg_attr(not(hax), target_feature(enable = "avx2"))]
#[allow(unsafe_code)]
#[allow(non_snake_case)]
// #[inline(always)]
pub(crate) unsafe fn matrix_A<
    SIMDUnit: Operations,
    const ROWS_IN_A: usize,
    const COLUMNS_IN_A: usize,
>(
    seed: [u8; 34],
    matrix: &mut [SampledRingElement<SIMDUnit>],
) {
    match (ROWS_IN_A as u8, COLUMNS_IN_A as u8) {
        (4, 4) => matrix_A_4_by_4::<SIMDUnit, ROWS_IN_A, COLUMNS_IN_A>(seed),
        (6, 5) => matrix_A_6_by_5::<SIMDUnit, ROWS_IN_A, COLUMNS_IN_A>(seed, matrix),
        (8, 7) => matrix_A_8_by_7::<SIMDUnit, ROWS_IN_A, COLUMNS_IN_A>(seed),
        _ => unreachable!(),
    }
}

#[cfg(feature = "mldsa44")]
#[inline(always)]
#[allow(unsafe_code)]
fn sample_s1_and_s2_4_by_4<
    SIMDUnit: Operations,
    Shake256X4: shake256::XofX4,
    const ETA: usize,
    const S1_DIMENSION: usize,
    const S2_DIMENSION: usize,
>(
    seed_base: [u8; 66],
) {
    todo!()
    // let mut s1 = [SampledRingElement::<SIMDUnit>::new(); S1_DIMENSION];
    // let mut s2 = [SampledRingElement::<SIMDUnit>::new(); S2_DIMENSION];

    // sample_four_error_ring_elements::<SIMDUnit, Shake256X4, ETA>(seed_base, 0, 1, 2, 3, &mut s1);
    // sample_four_error_ring_elements::<SIMDUnit, Shake256X4, ETA>(seed_base, 4, 5, 6, 7, &mut s2);

    // (
    //     s1.map(|e| e.into_ring_element()),
    //     s2.map(|e| e.into_ring_element()),
    // )
}

#[cfg(feature = "mldsa65")]
#[inline(always)]
#[allow(unsafe_code)]
fn sample_s1_and_s2_5_by_6<
    SIMDUnit: Operations,
    Shake256X4: shake256::XofX4,
    const ETA: usize,
    const S1_DIMENSION: usize,
    const S2_DIMENSION: usize,
>(
    seed_base: [u8; 66],
    elements: &mut [SampledRingElement<SIMDUnit>],
) {
    // let mut s1 = [ElementOut::<SIMDUnit>::new(); S1_DIMENSION];
    // let mut s2 = [ElementOut::<SIMDUnit>::new(); S2_DIMENSION];
    // let mut elements = [SampledRingElement::<SIMDUnit>::new(); 12];

    sample_four_error_ring_elements::<SIMDUnit, Shake256X4, ETA>(seed_base, 0, 1, 2, 3, elements);
    // s1[0] = four.0;
    // s1[1] = four.1;
    // s1[2] = four.2;
    // s1[3] = four.3;

    sample_four_error_ring_elements::<SIMDUnit, Shake256X4, ETA>(
        seed_base,
        4,
        5,
        6,
        7,
        &mut elements[4..],
    );
    // s1[4] = four.0;
    // s2[0] = four.1;
    // s2[1] = four.2;
    // s2[2] = four.3;

    sample_four_error_ring_elements::<SIMDUnit, Shake256X4, ETA>(
        seed_base,
        8,
        9,
        10,
        11,
        &mut elements[8..],
    );
    // s2[3] = four.0;
    // s2[4] = four.1;
    // s2[5] = four.2;

    // (
    //     core::array::from_fn(|i| elements[i].into_ring_element()),
    //     core::array::from_fn(|i| elements[i + S1_DIMENSION].into_ring_element()),
    // )
}

#[cfg(feature = "mldsa87")]
#[inline(always)]
#[allow(unsafe_code)]
fn sample_s1_and_s2_7_by_8<
    SIMDUnit: Operations,
    Shake256X4: shake256::XofX4,
    const ETA: usize,
    const S1_DIMENSION: usize,
    const S2_DIMENSION: usize,
>(
    seed_base: [u8; 66],
) {
    todo!()
    // let mut s1 = [PolynomialRingElement::<SIMDUnit>::ZERO(); S1_DIMENSION];
    // let mut s2 = [PolynomialRingElement::<SIMDUnit>::ZERO(); S2_DIMENSION];
    // let mut elements = [SampledRingElement::<SIMDUnit>::new(); 16];

    // sample_four_error_ring_elements::<SIMDUnit, Shake256X4, ETA>(
    //     seed_base,
    //     0,
    //     1,
    //     2,
    //     3,
    //     &mut elements,
    // );

    // sample_four_error_ring_elements::<SIMDUnit, Shake256X4, ETA>(
    //     seed_base,
    //     4,
    //     5,
    //     6,
    //     7,
    //     &mut elements[4..],
    // );
    // // s1[4] = four.0;
    // // s1[5] = four.1;
    // // s1[6] = four.2;
    // // s2[0] = four.3;

    // sample_four_error_ring_elements::<SIMDUnit, Shake256X4, ETA>(
    //     seed_base,
    //     8,
    //     9,
    //     10,
    //     11,
    //     &mut elements[8..],
    // );
    // // s2[1] = four.0;
    // // s2[2] = four.1;
    // // s2[3] = four.2;
    // // s2[4] = four.3;

    // sample_four_error_ring_elements::<SIMDUnit, Shake256X4, ETA>(
    //     seed_base,
    //     12,
    //     13,
    //     14,
    //     15,
    //     &mut elements[12..],
    // );
    // // s2[5] = four.0;
    // // s2[6] = four.1;
    // // s2[7] = four.2;

    // // (s1, s2)

    // (
    //     core::array::from_fn(|i| elements[i].into_ring_element()),
    //     core::array::from_fn(|i| elements[i + S1_DIMENSION].into_ring_element()),
    // )
}

#[cfg_attr(not(hax), target_feature(enable = "avx2"))]
#[allow(unsafe_code)]
pub(crate) unsafe fn sample_s1_and_s2<
    SIMDUnit: Operations,
    Shake256X4: shake256::XofX4,
    const ETA: usize,
    const S1_DIMENSION: usize,
    const S2_DIMENSION: usize,
>(
    seed: [u8; 66],
    elements: &mut [SampledRingElement<SIMDUnit>],
) {
    match (S1_DIMENSION as u8, S2_DIMENSION as u8) {
        #[cfg(feature = "mldsa44")]
        (4, 4) => {
            sample_s1_and_s2_4_by_4::<SIMDUnit, Shake256X4, ETA, S1_DIMENSION, S2_DIMENSION>(seed)
        }
        #[cfg(feature = "mldsa65")]
        (5, 6) => sample_s1_and_s2_5_by_6::<SIMDUnit, Shake256X4, ETA, S1_DIMENSION, S2_DIMENSION>(
            seed, elements,
        ),
        #[cfg(feature = "mldsa87")]
        (7, 8) => {
            sample_s1_and_s2_7_by_8::<SIMDUnit, Shake256X4, ETA, S1_DIMENSION, S2_DIMENSION>(seed)
        }
        _ => unreachable!(),
    }
}
