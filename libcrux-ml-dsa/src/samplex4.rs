use crate::{
    hash_functions::{shake128, shake256},
    polynomial::PolynomialRingElement,
    sample::{sample_four_error_ring_elements, sample_up_to_four_ring_elements},
    simd::traits::Operations,
};

/// The x4 sampling implementation that is selected during multiplexing.
pub(crate) trait X4Sampler {
    /// Sample the matrix A using platform specific implementation.
    fn matrix<SIMDUnit: Operations, const ROWS_IN_A: usize, const COLUMNS_IN_A: usize>(
        seed: &[u8],
        matrix: &mut [[PolynomialRingElement<SIMDUnit>; COLUMNS_IN_A]; ROWS_IN_A],
    );
}

#[inline(always)]
#[cfg(feature = "mldsa44")]
pub(crate) fn matrix_4_by_4<
    SIMDUnit: Operations,
    Shake128: shake128::XofX4,
    const ROWS_IN_A: usize,
    const COLUMNS_IN_A: usize,
>(
    seed: &[u8],
    matrix: &mut [[PolynomialRingElement<SIMDUnit>; COLUMNS_IN_A]; ROWS_IN_A],
) {
    let mut rand_stack0 = [0u8; shake128::FIVE_BLOCKS_SIZE];
    let mut rand_stack1 = [0u8; shake128::FIVE_BLOCKS_SIZE];
    let mut rand_stack2 = [0u8; shake128::FIVE_BLOCKS_SIZE];
    let mut rand_stack3 = [0u8; shake128::FIVE_BLOCKS_SIZE];
    let mut tmp_stack = [[0i32; 263], [0i32; 263], [0i32; 263], [0i32; 263]];

    sample_up_to_four_ring_elements::<SIMDUnit, Shake128, ROWS_IN_A, COLUMNS_IN_A>(
        seed,
        matrix,
        &mut rand_stack0,
        &mut rand_stack1,
        &mut rand_stack2,
        &mut rand_stack3,
        &mut tmp_stack,
        &[(0, 0), (0, 1), (0, 2), (0, 3)],
        4,
    );
    sample_up_to_four_ring_elements::<SIMDUnit, Shake128, ROWS_IN_A, COLUMNS_IN_A>(
        seed,
        matrix,
        &mut rand_stack0,
        &mut rand_stack1,
        &mut rand_stack2,
        &mut rand_stack3,
        &mut tmp_stack,
        &[(1, 0), (1, 1), (1, 2), (1, 3)],
        4,
    );
    sample_up_to_four_ring_elements::<SIMDUnit, Shake128, ROWS_IN_A, COLUMNS_IN_A>(
        seed,
        matrix,
        &mut rand_stack0,
        &mut rand_stack1,
        &mut rand_stack2,
        &mut rand_stack3,
        &mut tmp_stack,
        &[(2, 0), (2, 1), (2, 2), (2, 3)],
        4,
    );
    sample_up_to_four_ring_elements::<SIMDUnit, Shake128, ROWS_IN_A, COLUMNS_IN_A>(
        seed,
        matrix,
        &mut rand_stack0,
        &mut rand_stack1,
        &mut rand_stack2,
        &mut rand_stack3,
        &mut tmp_stack,
        &[(3, 0), (3, 1), (3, 2), (3, 3)],
        4,
    );
}

#[inline(always)]
#[cfg(feature = "mldsa65")]
pub(crate) fn matrix_6_by_5<
    SIMDUnit: Operations,
    Shake128: shake128::XofX4,
    const ROWS_IN_A: usize,
    const COLUMNS_IN_A: usize,
>(
    seed: &[u8],
    matrix: &mut [[PolynomialRingElement<SIMDUnit>; COLUMNS_IN_A]; ROWS_IN_A],
) {
    let mut rand_stack0 = [0u8; shake128::FIVE_BLOCKS_SIZE];
    let mut rand_stack1 = [0u8; shake128::FIVE_BLOCKS_SIZE];
    let mut rand_stack2 = [0u8; shake128::FIVE_BLOCKS_SIZE];
    let mut rand_stack3 = [0u8; shake128::FIVE_BLOCKS_SIZE];
    let mut tmp_stack = [[0i32; 263], [0i32; 263], [0i32; 263], [0i32; 263]];

    sample_up_to_four_ring_elements::<SIMDUnit, Shake128, ROWS_IN_A, COLUMNS_IN_A>(
        seed,
        matrix,
        &mut rand_stack0,
        &mut rand_stack1,
        &mut rand_stack2,
        &mut rand_stack3,
        &mut tmp_stack,
        &[(0, 0), (0, 1), (0, 2), (0, 3)],
        4,
    );
    sample_up_to_four_ring_elements::<SIMDUnit, Shake128, ROWS_IN_A, COLUMNS_IN_A>(
        seed,
        matrix,
        &mut rand_stack0,
        &mut rand_stack1,
        &mut rand_stack2,
        &mut rand_stack3,
        &mut tmp_stack,
        &[(0, 4), (1, 0), (1, 1), (1, 2)],
        4,
    );
    sample_up_to_four_ring_elements::<SIMDUnit, Shake128, ROWS_IN_A, COLUMNS_IN_A>(
        seed,
        matrix,
        &mut rand_stack0,
        &mut rand_stack1,
        &mut rand_stack2,
        &mut rand_stack3,
        &mut tmp_stack,
        &[(1, 3), (1, 4), (2, 0), (2, 1)],
        4,
    );
    sample_up_to_four_ring_elements::<SIMDUnit, Shake128, ROWS_IN_A, COLUMNS_IN_A>(
        seed,
        matrix,
        &mut rand_stack0,
        &mut rand_stack1,
        &mut rand_stack2,
        &mut rand_stack3,
        &mut tmp_stack,
        &[(2, 2), (2, 3), (2, 4), (3, 0)],
        4,
    );
    sample_up_to_four_ring_elements::<SIMDUnit, Shake128, ROWS_IN_A, COLUMNS_IN_A>(
        seed,
        matrix,
        &mut rand_stack0,
        &mut rand_stack1,
        &mut rand_stack2,
        &mut rand_stack3,
        &mut tmp_stack,
        &[(3, 1), (3, 2), (3, 3), (3, 4)],
        4,
    );
    sample_up_to_four_ring_elements::<SIMDUnit, Shake128, ROWS_IN_A, COLUMNS_IN_A>(
        seed,
        matrix,
        &mut rand_stack0,
        &mut rand_stack1,
        &mut rand_stack2,
        &mut rand_stack3,
        &mut tmp_stack,
        &[(4, 0), (4, 1), (4, 2), (4, 3)],
        4,
    );
    sample_up_to_four_ring_elements::<SIMDUnit, Shake128, ROWS_IN_A, COLUMNS_IN_A>(
        seed,
        matrix,
        &mut rand_stack0,
        &mut rand_stack1,
        &mut rand_stack2,
        &mut rand_stack3,
        &mut tmp_stack,
        &[(4, 4), (5, 0), (5, 1), (5, 2)],
        4,
    );

    // The last 2 sampled ring elements are discarded here.
    sample_up_to_four_ring_elements::<SIMDUnit, Shake128, ROWS_IN_A, COLUMNS_IN_A>(
        seed,
        matrix,
        &mut rand_stack0,
        &mut rand_stack1,
        &mut rand_stack2,
        &mut rand_stack3,
        &mut tmp_stack,
        &[(5, 3), (5, 4), (5, 5), (5, 6)],
        2,
    );
}

#[inline(always)]
#[cfg(feature = "mldsa87")]
pub(crate) fn matrix_8_by_7<
    SIMDUnit: Operations,
    Shake128: shake128::XofX4,
    const ROWS_IN_A: usize,
    const COLUMNS_IN_A: usize,
>(
    seed: &[u8],
    matrix: &mut [[PolynomialRingElement<SIMDUnit>; COLUMNS_IN_A]; ROWS_IN_A],
) {
    let mut rand_stack0 = [0u8; shake128::FIVE_BLOCKS_SIZE];
    let mut rand_stack1 = [0u8; shake128::FIVE_BLOCKS_SIZE];
    let mut rand_stack2 = [0u8; shake128::FIVE_BLOCKS_SIZE];
    let mut rand_stack3 = [0u8; shake128::FIVE_BLOCKS_SIZE];
    let mut tmp_stack = [[0i32; 263], [0i32; 263], [0i32; 263], [0i32; 263]];

    sample_up_to_four_ring_elements::<SIMDUnit, Shake128, ROWS_IN_A, COLUMNS_IN_A>(
        seed,
        matrix,
        &mut rand_stack0,
        &mut rand_stack1,
        &mut rand_stack2,
        &mut rand_stack3,
        &mut tmp_stack,
        &[(0, 0), (0, 1), (0, 2), (0, 3)],
        4,
    );
    sample_up_to_four_ring_elements::<SIMDUnit, Shake128, ROWS_IN_A, COLUMNS_IN_A>(
        seed,
        matrix,
        &mut rand_stack0,
        &mut rand_stack1,
        &mut rand_stack2,
        &mut rand_stack3,
        &mut tmp_stack,
        &[(0, 4), (0, 5), (0, 6), (1, 0)],
        4,
    );
    sample_up_to_four_ring_elements::<SIMDUnit, Shake128, ROWS_IN_A, COLUMNS_IN_A>(
        seed,
        matrix,
        &mut rand_stack0,
        &mut rand_stack1,
        &mut rand_stack2,
        &mut rand_stack3,
        &mut tmp_stack,
        &[(1, 1), (1, 2), (1, 3), (1, 4)],
        4,
    );
    sample_up_to_four_ring_elements::<SIMDUnit, Shake128, ROWS_IN_A, COLUMNS_IN_A>(
        seed,
        matrix,
        &mut rand_stack0,
        &mut rand_stack1,
        &mut rand_stack2,
        &mut rand_stack3,
        &mut tmp_stack,
        &[(1, 5), (1, 6), (2, 0), (2, 1)],
        4,
    );
    sample_up_to_four_ring_elements::<SIMDUnit, Shake128, ROWS_IN_A, COLUMNS_IN_A>(
        seed,
        matrix,
        &mut rand_stack0,
        &mut rand_stack1,
        &mut rand_stack2,
        &mut rand_stack3,
        &mut tmp_stack,
        &[(2, 2), (2, 3), (2, 4), (2, 5)],
        4,
    );
    sample_up_to_four_ring_elements::<SIMDUnit, Shake128, ROWS_IN_A, COLUMNS_IN_A>(
        seed,
        matrix,
        &mut rand_stack0,
        &mut rand_stack1,
        &mut rand_stack2,
        &mut rand_stack3,
        &mut tmp_stack,
        &[(2, 6), (3, 0), (3, 1), (3, 2)],
        4,
    );
    sample_up_to_four_ring_elements::<SIMDUnit, Shake128, ROWS_IN_A, COLUMNS_IN_A>(
        seed,
        matrix,
        &mut rand_stack0,
        &mut rand_stack1,
        &mut rand_stack2,
        &mut rand_stack3,
        &mut tmp_stack,
        &[(3, 3), (3, 4), (3, 5), (3, 6)],
        4,
    );
    sample_up_to_four_ring_elements::<SIMDUnit, Shake128, ROWS_IN_A, COLUMNS_IN_A>(
        seed,
        matrix,
        &mut rand_stack0,
        &mut rand_stack1,
        &mut rand_stack2,
        &mut rand_stack3,
        &mut tmp_stack,
        &[(4, 0), (4, 1), (4, 2), (4, 3)],
        4,
    );
    sample_up_to_four_ring_elements::<SIMDUnit, Shake128, ROWS_IN_A, COLUMNS_IN_A>(
        seed,
        matrix,
        &mut rand_stack0,
        &mut rand_stack1,
        &mut rand_stack2,
        &mut rand_stack3,
        &mut tmp_stack,
        &[(4, 4), (4, 5), (4, 6), (5, 0)],
        4,
    );
    sample_up_to_four_ring_elements::<SIMDUnit, Shake128, ROWS_IN_A, COLUMNS_IN_A>(
        seed,
        matrix,
        &mut rand_stack0,
        &mut rand_stack1,
        &mut rand_stack2,
        &mut rand_stack3,
        &mut tmp_stack,
        &[(5, 1), (5, 2), (5, 3), (5, 4)],
        4,
    );
    sample_up_to_four_ring_elements::<SIMDUnit, Shake128, ROWS_IN_A, COLUMNS_IN_A>(
        seed,
        matrix,
        &mut rand_stack0,
        &mut rand_stack1,
        &mut rand_stack2,
        &mut rand_stack3,
        &mut tmp_stack,
        &[(5, 5), (5, 6), (6, 0), (6, 1)],
        4,
    );
    sample_up_to_four_ring_elements::<SIMDUnit, Shake128, ROWS_IN_A, COLUMNS_IN_A>(
        seed,
        matrix,
        &mut rand_stack0,
        &mut rand_stack1,
        &mut rand_stack2,
        &mut rand_stack3,
        &mut tmp_stack,
        &[(6, 2), (6, 3), (6, 4), (6, 5)],
        4,
    );
    sample_up_to_four_ring_elements::<SIMDUnit, Shake128, ROWS_IN_A, COLUMNS_IN_A>(
        seed,
        matrix,
        &mut rand_stack0,
        &mut rand_stack1,
        &mut rand_stack2,
        &mut rand_stack3,
        &mut tmp_stack,
        &[(6, 6), (7, 0), (7, 1), (7, 2)],
        4,
    );
    sample_up_to_four_ring_elements::<SIMDUnit, Shake128, ROWS_IN_A, COLUMNS_IN_A>(
        seed,
        matrix,
        &mut rand_stack0,
        &mut rand_stack1,
        &mut rand_stack2,
        &mut rand_stack3,
        &mut tmp_stack,
        &[(7, 3), (7, 4), (7, 5), (7, 6)],
        4,
    );
}

pub(crate) mod portable {
    use super::*;

    pub(crate) struct PortableSampler {}
    impl X4Sampler for PortableSampler {
        #[inline(always)]
        fn matrix<SIMDUnit: Operations, const ROWS_IN_A: usize, const COLUMNS_IN_A: usize>(
            seed: &[u8],
            matrix: &mut [[PolynomialRingElement<SIMDUnit>; COLUMNS_IN_A]; ROWS_IN_A],
        ) {
            matrix_generic::<
                SIMDUnit,
                crate::hash_functions::portable::Shake128X4,
                ROWS_IN_A,
                COLUMNS_IN_A,
            >(seed, matrix)
        }
    }
}

#[cfg(feature = "simd128")]
pub(crate) mod neon {
    use super::*;

    pub(crate) struct NeonSampler {}
    impl X4Sampler for NeonSampler {
        #[inline(always)]
        fn matrix_A<SIMDUnit: Operations, const ROWS_IN_A: usize, const COLUMNS_IN_A: usize>(
            seed: [u8; 34],
        ) -> [[PolynomialRingElement<SIMDUnit>; COLUMNS_IN_A]; ROWS_IN_A] {
            matrix_generic::<
                SIMDUnit,
                crate::hash_functions::neon::Shake128x4,
                ROWS_IN_A,
                COLUMNS_IN_A,
            >(seed)
        }
    }
}

#[cfg(feature = "simd256")]
pub(crate) mod avx2 {
    use super::*;

    pub(crate) struct AVX2Sampler {}
    impl X4Sampler for AVX2Sampler {
        #[inline(always)]
        #[allow(unsafe_code)]
        fn matrix<SIMDUnit: Operations, const ROWS_IN_A: usize, const COLUMNS_IN_A: usize>(
            seed: &[u8],
            matrix: &mut [[PolynomialRingElement<SIMDUnit>; COLUMNS_IN_A]; ROWS_IN_A],
        ) {
            unsafe { matrix_avx2(seed, matrix) }
        }
    }

    #[cfg_attr(not(hax), target_feature(enable = "avx2"))]
    #[allow(unsafe_code)]

    pub(crate) unsafe fn matrix_avx2<
        SIMDUnit: Operations,
        const ROWS_IN_A: usize,
        const COLUMNS_IN_A: usize,
    >(
        seed: &[u8],
        matrix: &mut [[PolynomialRingElement<SIMDUnit>; COLUMNS_IN_A]; ROWS_IN_A],
    ) {
        match (ROWS_IN_A as u8, COLUMNS_IN_A as u8) {
            #[cfg(feature = "mldsa44")]
            (4, 4) => matrix_4_by_4::<
                SIMDUnit,
                crate::hash_functions::simd256::Shake128x4,
                ROWS_IN_A,
                COLUMNS_IN_A,
            >(seed, matrix),
            #[cfg(feature = "mldsa65")]
            (6, 5) => matrix_6_by_5::<
                SIMDUnit,
                crate::hash_functions::simd256::Shake128x4,
                ROWS_IN_A,
                COLUMNS_IN_A,
            >(seed, matrix),
            #[cfg(feature = "mldsa87")]
            (8, 7) => matrix_8_by_7::<
                SIMDUnit,
                crate::hash_functions::simd256::Shake128x4,
                ROWS_IN_A,
                COLUMNS_IN_A,
            >(seed, matrix),
            _ => unreachable!(),
        }
    }
}

pub(crate) fn matrix_generic<
    SIMDUnit: Operations,
    Shake128: shake128::XofX4,
    const ROWS_IN_A: usize,
    const COLUMNS_IN_A: usize,
>(
    seed: &[u8],
    matrix: &mut [[PolynomialRingElement<SIMDUnit>; COLUMNS_IN_A]; ROWS_IN_A],
) {
    match (ROWS_IN_A as u8, COLUMNS_IN_A as u8) {
        #[cfg(feature = "mldsa44")]
        (4, 4) => matrix_4_by_4::<SIMDUnit, Shake128, ROWS_IN_A, COLUMNS_IN_A>(seed, matrix),
        #[cfg(feature = "mldsa65")]
        (6, 5) => matrix_6_by_5::<SIMDUnit, Shake128, ROWS_IN_A, COLUMNS_IN_A>(seed, matrix),
        #[cfg(feature = "mldsa87")]
        (8, 7) => matrix_8_by_7::<SIMDUnit, Shake128, ROWS_IN_A, COLUMNS_IN_A>(seed, matrix),
        _ => unreachable!(),
    }
}

#[inline(always)]
pub(crate) fn sample_s1_and_s2<
    SIMDUnit: Operations,
    Shake256X4: shake256::XofX4,
    const ETA: usize,
    const ROW_COLUMN: usize,
>(
    seed: &[u8],
    s1_s2: &mut [PolynomialRingElement<SIMDUnit>; ROW_COLUMN],
) {
    for i in 0..ROW_COLUMN.div_ceil(4) {
        sample_four_error_ring_elements::<SIMDUnit, Shake256X4, ETA>(seed, 4 * i as u16, s1_s2);
    }
}
