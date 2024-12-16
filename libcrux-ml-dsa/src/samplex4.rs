use crate::{
    hash_functions::{shake128, shake256},
    polynomial::PolynomialRingElement,
    sample::{sample_four_error_ring_elements, sample_four_ring_elements, SampleArgs},
    simd::traits::Operations,
};

/// The x4 sampling implementation that is selected during multiplexing.
#[allow(unused)]
pub(crate) enum X4Sampler {
    AVX2,
    Neon,
    Portable,
}

#[inline(always)]
fn generate_domain_separator((row, column): (u8, u8)) -> u16 {
    (column as u16) | ((row as u16) << 8)
}

type Matrix<SIMDUnit, const ROWS_IN_A: usize, const COLUMNS_IN_A: usize> =
    [[PolynomialRingElement<SIMDUnit>; COLUMNS_IN_A]; ROWS_IN_A];

/// A call to sample four ring elements from $seed into $memory at indices $a, $b
/// $c, $d.
macro_rules! sample_four_ring_elements_into {
    ($memory:ident, $seed:ident, $a:expr, $b:expr, $c:expr, $d:expr) => {
        $memory.indices = &[$a, $b, $c, $d];
        sample_four_ring_elements::<SIMDUnit, Shake128, ROWS_IN_A, COLUMNS_IN_A>(
            $seed,
            generate_domain_separator($a),
            generate_domain_separator($b),
            generate_domain_separator($c),
            generate_domain_separator($d),
            &mut $memory,
        );
    };
}

#[allow(non_snake_case)]
#[inline(always)]
#[cfg(feature = "mldsa44")]
pub(crate) fn matrix_A_4_by_4<
    SIMDUnit: Operations,
    Shake128: shake128::XofX4,
    const ROWS_IN_A: usize,
    const COLUMNS_IN_A: usize,
>(
    seed: [u8; 34],
) -> Matrix<SIMDUnit, ROWS_IN_A, COLUMNS_IN_A> {
    let mut A: Matrix<SIMDUnit, ROWS_IN_A, COLUMNS_IN_A> =
        [[PolynomialRingElement::<SIMDUnit>::ZERO(); COLUMNS_IN_A]; ROWS_IN_A];

    let mut rand_stack = (
        [0u8; shake128::FIVE_BLOCKS_SIZE],
        [0u8; shake128::FIVE_BLOCKS_SIZE],
        [0u8; shake128::FIVE_BLOCKS_SIZE],
        [0u8; shake128::FIVE_BLOCKS_SIZE],
    );
    let mut tmp_stack = [[0i32; 263], [0i32; 263], [0i32; 263], [0i32; 263]];
    let mut memory = SampleArgs::new(&mut rand_stack, &mut tmp_stack, &mut A, &[]);

    sample_four_ring_elements_into!(memory, seed, (0, 0), (0, 1), (0, 2), (0, 3));
    sample_four_ring_elements_into!(memory, seed, (1, 0), (1, 1), (1, 2), (1, 3));
    sample_four_ring_elements_into!(memory, seed, (2, 0), (2, 1), (2, 2), (2, 3));
    sample_four_ring_elements_into!(memory, seed, (3, 0), (3, 1), (3, 2), (3, 3));

    A
}

#[allow(non_snake_case)]
#[inline(always)]
#[cfg(feature = "mldsa65")]
pub(crate) fn matrix_A_6_by_5<
    SIMDUnit: Operations,
    Shake128: shake128::XofX4,
    const ROWS_IN_A: usize,
    const COLUMNS_IN_A: usize,
>(
    seed: [u8; 34],
) -> [[PolynomialRingElement<SIMDUnit>; COLUMNS_IN_A]; ROWS_IN_A] {
    let mut A = [[PolynomialRingElement::<SIMDUnit>::ZERO(); COLUMNS_IN_A]; ROWS_IN_A];

    let mut rand_stack = (
        [0u8; shake128::FIVE_BLOCKS_SIZE],
        [0u8; shake128::FIVE_BLOCKS_SIZE],
        [0u8; shake128::FIVE_BLOCKS_SIZE],
        [0u8; shake128::FIVE_BLOCKS_SIZE],
    );
    let mut tmp_stack = [[0i32; 263], [0i32; 263], [0i32; 263], [0i32; 263]];
    let mut memory = SampleArgs::new(&mut rand_stack, &mut tmp_stack, &mut A, &[]);

    sample_four_ring_elements_into!(memory, seed, (0, 0), (0, 1), (0, 2), (0, 3));
    sample_four_ring_elements_into!(memory, seed, (0, 4), (1, 0), (1, 1), (1, 2));
    sample_four_ring_elements_into!(memory, seed, (1, 3), (1, 4), (2, 0), (2, 1));
    sample_four_ring_elements_into!(memory, seed, (2, 2), (2, 3), (2, 4), (3, 0));
    sample_four_ring_elements_into!(memory, seed, (3, 1), (3, 2), (3, 3), (3, 4));
    sample_four_ring_elements_into!(memory, seed, (4, 0), (4, 1), (4, 2), (4, 3));
    sample_four_ring_elements_into!(memory, seed, (4, 4), (5, 0), (5, 1), (5, 2));

    // The last 2 sampled ring elements are discarded here.
    memory.indices = &[(5, 3), (5, 4)];
    sample_four_ring_elements::<SIMDUnit, Shake128, ROWS_IN_A, COLUMNS_IN_A>(
        seed,
        generate_domain_separator((5, 3)),
        generate_domain_separator((5, 4)),
        generate_domain_separator((5, 5)),
        generate_domain_separator((5, 6)),
        &mut memory,
    );

    A
}

#[allow(non_snake_case)]
#[inline(always)]
#[cfg(feature = "mldsa87")]
pub(crate) fn matrix_A_8_by_7<
    SIMDUnit: Operations,
    Shake128: shake128::XofX4,
    const ROWS_IN_A: usize,
    const COLUMNS_IN_A: usize,
>(
    seed: [u8; 34],
) -> [[PolynomialRingElement<SIMDUnit>; COLUMNS_IN_A]; ROWS_IN_A] {
    let mut A = [[PolynomialRingElement::<SIMDUnit>::ZERO(); COLUMNS_IN_A]; ROWS_IN_A];

    let mut rand_stack = (
        [0u8; shake128::FIVE_BLOCKS_SIZE],
        [0u8; shake128::FIVE_BLOCKS_SIZE],
        [0u8; shake128::FIVE_BLOCKS_SIZE],
        [0u8; shake128::FIVE_BLOCKS_SIZE],
    );
    let mut tmp_stack = [[0i32; 263], [0i32; 263], [0i32; 263], [0i32; 263]];
    let mut memory = SampleArgs::new(&mut rand_stack, &mut tmp_stack, &mut A, &[]);

    sample_four_ring_elements_into!(memory, seed, (0, 0), (0, 1), (0, 2), (0, 3));
    sample_four_ring_elements_into!(memory, seed, (0, 4), (0, 5), (0, 6), (1, 0));
    sample_four_ring_elements_into!(memory, seed, (1, 1), (1, 2), (1, 3), (1, 4));
    sample_four_ring_elements_into!(memory, seed, (1, 5), (1, 6), (2, 0), (2, 1));
    sample_four_ring_elements_into!(memory, seed, (2, 2), (2, 3), (2, 4), (2, 5));
    sample_four_ring_elements_into!(memory, seed, (2, 6), (3, 0), (3, 1), (3, 2));
    sample_four_ring_elements_into!(memory, seed, (3, 3), (3, 4), (3, 5), (3, 6));
    sample_four_ring_elements_into!(memory, seed, (4, 0), (4, 1), (4, 2), (4, 3));
    sample_four_ring_elements_into!(memory, seed, (4, 4), (4, 5), (4, 6), (5, 0));
    sample_four_ring_elements_into!(memory, seed, (5, 1), (5, 2), (5, 3), (5, 4));
    sample_four_ring_elements_into!(memory, seed, (5, 5), (5, 6), (6, 0), (6, 1));
    sample_four_ring_elements_into!(memory, seed, (6, 2), (6, 3), (6, 4), (6, 5));
    sample_four_ring_elements_into!(memory, seed, (6, 6), (7, 0), (7, 1), (7, 2));
    sample_four_ring_elements_into!(memory, seed, (7, 3), (7, 4), (7, 5), (7, 6));

    A
}

#[inline(always)]
#[allow(unsafe_code)]
#[allow(non_snake_case)]
pub(crate) fn matrix_A<SIMDUnit: Operations, const ROWS_IN_A: usize, const COLUMNS_IN_A: usize>(
    seed: [u8; 34],
    sampler: X4Sampler,
) -> [[PolynomialRingElement<SIMDUnit>; COLUMNS_IN_A]; ROWS_IN_A] {
    match sampler {
        #[cfg(feature = "simd256")]
        X4Sampler::AVX2 => unsafe { matrix_A_avx2::<SIMDUnit, ROWS_IN_A, COLUMNS_IN_A>(seed) },
        #[cfg(feature = "simd128")]
        X4Sampler::Neon => matrix_A_generic::<
            SIMDUnit,
            crate::hash_functions::neon::Shake128x4,
            ROWS_IN_A,
            COLUMNS_IN_A,
        >(seed),
        X4Sampler::Portable => matrix_A_generic::<
            SIMDUnit,
            crate::hash_functions::portable::Shake128X4,
            ROWS_IN_A,
            COLUMNS_IN_A,
        >(seed),
        _ => unreachable!(),
    }
}

#[cfg_attr(not(hax), target_feature(enable = "avx2"))]
#[allow(unsafe_code)]
#[allow(non_snake_case)]
pub(crate) unsafe fn matrix_A_avx2<
    SIMDUnit: Operations,
    const ROWS_IN_A: usize,
    const COLUMNS_IN_A: usize,
>(
    seed: [u8; 34],
) -> [[PolynomialRingElement<SIMDUnit>; COLUMNS_IN_A]; ROWS_IN_A] {
    match (ROWS_IN_A as u8, COLUMNS_IN_A as u8) {
        #[cfg(feature = "mldsa44")]
        (4, 4) => matrix_A_4_by_4::<
            SIMDUnit,
            crate::hash_functions::simd256::Shake128x4,
            ROWS_IN_A,
            COLUMNS_IN_A,
        >(seed),
        #[cfg(feature = "mldsa65")]
        (6, 5) => matrix_A_6_by_5::<
            SIMDUnit,
            crate::hash_functions::simd256::Shake128x4,
            ROWS_IN_A,
            COLUMNS_IN_A,
        >(seed),
        #[cfg(feature = "mldsa87")]
        (8, 7) => matrix_A_8_by_7::<
            SIMDUnit,
            crate::hash_functions::simd256::Shake128x4,
            ROWS_IN_A,
            COLUMNS_IN_A,
        >(seed),
        _ => unreachable!(),
    }
}

#[allow(non_snake_case)]
pub(crate) fn matrix_A_generic<
    SIMDUnit: Operations,
    Shake128: shake128::XofX4,
    const ROWS_IN_A: usize,
    const COLUMNS_IN_A: usize,
>(
    seed: [u8; 34],
) -> [[PolynomialRingElement<SIMDUnit>; COLUMNS_IN_A]; ROWS_IN_A] {
    match (ROWS_IN_A as u8, COLUMNS_IN_A as u8) {
        #[cfg(feature = "mldsa44")]
        (4, 4) => matrix_A_4_by_4::<SIMDUnit, Shake128, ROWS_IN_A, COLUMNS_IN_A>(seed),
        #[cfg(feature = "mldsa65")]
        (6, 5) => matrix_A_6_by_5::<SIMDUnit, Shake128, ROWS_IN_A, COLUMNS_IN_A>(seed),
        #[cfg(feature = "mldsa87")]
        (8, 7) => matrix_A_8_by_7::<SIMDUnit, Shake128, ROWS_IN_A, COLUMNS_IN_A>(seed),
        _ => unreachable!(),
    }
}

#[cfg(feature = "mldsa44")]
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

    let four = sample_four_error_ring_elements::<SIMDUnit, Shake256X4, ETA>(seed_base, 0, 1, 2, 3);
    s1[0] = four.0;
    s1[1] = four.1;
    s1[2] = four.2;
    s1[3] = four.3;

    let four = sample_four_error_ring_elements::<SIMDUnit, Shake256X4, ETA>(seed_base, 4, 5, 6, 7);
    s2[0] = four.0;
    s2[1] = four.1;
    s2[2] = four.2;
    s2[3] = four.3;

    (s1, s2)
}

#[cfg(feature = "mldsa65")]
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

    let four = sample_four_error_ring_elements::<SIMDUnit, Shake256X4, ETA>(seed_base, 0, 1, 2, 3);
    s1[0] = four.0;
    s1[1] = four.1;
    s1[2] = four.2;
    s1[3] = four.3;

    let four = sample_four_error_ring_elements::<SIMDUnit, Shake256X4, ETA>(seed_base, 4, 5, 6, 7);
    s1[4] = four.0;
    s2[0] = four.1;
    s2[1] = four.2;
    s2[2] = four.3;

    let four =
        sample_four_error_ring_elements::<SIMDUnit, Shake256X4, ETA>(seed_base, 8, 9, 10, 11);
    s2[3] = four.0;
    s2[4] = four.1;
    s2[5] = four.2;

    (s1, s2)
}

#[cfg(feature = "mldsa87")]
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

    let four = sample_four_error_ring_elements::<SIMDUnit, Shake256X4, ETA>(seed_base, 0, 1, 2, 3);
    s1[0] = four.0;
    s1[1] = four.1;
    s1[2] = four.2;
    s1[3] = four.3;

    let four = sample_four_error_ring_elements::<SIMDUnit, Shake256X4, ETA>(seed_base, 4, 5, 6, 7);
    s1[4] = four.0;
    s1[5] = four.1;
    s1[6] = four.2;
    s2[0] = four.3;

    let four =
        sample_four_error_ring_elements::<SIMDUnit, Shake256X4, ETA>(seed_base, 8, 9, 10, 11);
    s2[1] = four.0;
    s2[2] = four.1;
    s2[3] = four.2;
    s2[4] = four.3;

    let four =
        sample_four_error_ring_elements::<SIMDUnit, Shake256X4, ETA>(seed_base, 12, 13, 14, 15);
    s2[5] = four.0;
    s2[6] = four.1;
    s2[7] = four.2;

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
        #[cfg(feature = "mldsa44")]
        (4, 4) => {
            sample_s1_and_s2_4_by_4::<SIMDUnit, Shake256X4, ETA, S1_DIMENSION, S2_DIMENSION>(seed)
        }
        #[cfg(feature = "mldsa65")]
        (5, 6) => {
            sample_s1_and_s2_5_by_6::<SIMDUnit, Shake256X4, ETA, S1_DIMENSION, S2_DIMENSION>(seed)
        }
        #[cfg(feature = "mldsa87")]
        (7, 8) => {
            sample_s1_and_s2_7_by_8::<SIMDUnit, Shake256X4, ETA, S1_DIMENSION, S2_DIMENSION>(seed)
        }
        _ => unreachable!(),
    }
}
