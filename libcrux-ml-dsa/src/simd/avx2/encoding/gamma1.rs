use libcrux_intrinsics::avx2::*;

#[inline(always)]
fn serialize_when_gamma1_is_2_pow_17<const OUTPUT_SIZE: usize>(
    simd_unit: Vec256,
) -> [u8; OUTPUT_SIZE] {
    let mut serialized = [0u8; 32];

    const GAMMA1: i32 = 1 << 17;
    let simd_unit_shifted = mm256_sub_epi32(mm256_set1_epi32(GAMMA1), simd_unit);

    let adjacent_2_combined = mm256_sllv_epi32(
        simd_unit_shifted,
        mm256_set_epi32(0, 14, 0, 14, 0, 14, 0, 14),
    );
    let adjacent_2_combined = mm256_srli_epi64::<14>(adjacent_2_combined);

    let every_second_element = mm256_bsrli_epi128::<8>(adjacent_2_combined);
    let every_second_element_shifted = mm256_slli_epi64::<36>(every_second_element);

    let adjacent_4_combined = mm256_add_epi64(adjacent_2_combined, every_second_element_shifted);
    let adjacent_4_combined = mm256_srlv_epi64(adjacent_4_combined, mm256_set_epi64x(28, 0, 28, 0));

    let lower_4 = mm256_castsi256_si128(adjacent_4_combined);
    mm_storeu_bytes_si128(&mut serialized[0..16], lower_4);

    let upper_4 = mm256_extracti128_si256::<1>(adjacent_4_combined);
    mm_storeu_bytes_si128(&mut serialized[9..25], upper_4);

    serialized[0..18].try_into().unwrap()
}

#[inline(always)]
fn serialize_when_gamma1_is_2_pow_19<const OUTPUT_SIZE: usize>(
    simd_unit: Vec256,
) -> [u8; OUTPUT_SIZE] {
    let mut serialized = [0u8; 32];

    const GAMMA1: i32 = 1 << 19;
    let simd_unit_shifted = mm256_sub_epi32(mm256_set1_epi32(GAMMA1), simd_unit);

    let adjacent_2_combined = mm256_sllv_epi32(
        simd_unit_shifted,
        mm256_set_epi32(0, 12, 0, 12, 0, 12, 0, 12),
    );
    let adjacent_2_combined = mm256_srli_epi64::<12>(adjacent_2_combined);

    let adjacent_4_combined = mm256_shuffle_epi8(
        adjacent_2_combined,
        mm256_set_epi8(
            -1, -1, -1, -1, -1, -1, 12, 11, 10, 9, 8, 4, 3, 2, 1, 0, -1, -1, -1, -1, -1, -1, 12,
            11, 10, 9, 8, 4, 3, 2, 1, 0,
        ),
    );

    // We now have 80 bits starting at position 0 in the lower 128-bit lane, ...
    let lower_4 = mm256_castsi256_si128(adjacent_4_combined);
    mm_storeu_bytes_si128(&mut serialized[0..16], lower_4);

    // ... and the second 80 bits at position 0 in the upper 128-bit lane
    let upper_4 = mm256_extracti128_si256::<1>(adjacent_4_combined);
    mm_storeu_bytes_si128(&mut serialized[10..26], upper_4);

    serialized[0..20].try_into().unwrap()
}

#[inline(always)]
pub(crate) fn serialize<const OUTPUT_SIZE: usize>(simd_unit: Vec256) -> [u8; OUTPUT_SIZE] {
    match OUTPUT_SIZE as u8 {
        18 => serialize_when_gamma1_is_2_pow_17::<OUTPUT_SIZE>(simd_unit),
        20 => serialize_when_gamma1_is_2_pow_19::<OUTPUT_SIZE>(simd_unit),
        _ => unreachable!(),
    }
}

#[inline(always)]
fn deserialize_when_gamma1_is_2_pow_17(serialized: &[u8]) -> Vec256 {
    debug_assert!(serialized.len() == 18);

    const GAMMA1: i32 = 1 << 17;
    const GAMMA1_TIMES_2_MASK: i32 = (GAMMA1 << 1) - 1;

    let serialized_lower = mm_loadu_si128(&serialized[0..16]);
    let serialized_upper = mm_loadu_si128(&serialized[2..18]);

    let serialized = mm256_set_m128i(serialized_upper, serialized_lower);

    let coefficients = mm256_shuffle_epi8(
        serialized,
        mm256_set_epi8(
            -1, 15, 14, 13, -1, 13, 12, 11, -1, 11, 10, 9, -1, 9, 8, 7, -1, 8, 7, 6, -1, 6, 5, 4,
            -1, 4, 3, 2, -1, 2, 1, 0,
        ),
    );

    let coefficients = mm256_srlv_epi32(coefficients, mm256_set_epi32(6, 4, 2, 0, 6, 4, 2, 0));
    let coefficients = mm256_and_si256(coefficients, mm256_set1_epi32(GAMMA1_TIMES_2_MASK));

    mm256_sub_epi32(mm256_set1_epi32(GAMMA1), coefficients)
}

#[inline(always)]
fn deserialize_when_gamma1_is_2_pow_19(serialized: &[u8]) -> Vec256 {
    // Each set of 5 bytes deserializes to 2 coefficients, and since each Vec256
    // can hold 8 such coefficients, we process 5 * (8 / 2) = 20 bytes in this
    // function.
    debug_assert!(serialized.len() == 20);

    const GAMMA1: i32 = 1 << 19;
    const GAMMA1_TIMES_2_MASK: i32 = (GAMMA1 << 1) - 1;

    let serialized_lower = mm_loadu_si128(&serialized[0..16]);
    let serialized_upper = mm_loadu_si128(&serialized[4..20]);

    let serialized = mm256_set_m128i(serialized_upper, serialized_lower);

    let coefficients = mm256_shuffle_epi8(
        serialized,
        mm256_set_epi8(
            -1, 15, 14, 13, -1, 13, 12, 11, -1, 10, 9, 8, -1, 8, 7, 6, -1, 9, 8, 7, -1, 7, 6, 5,
            -1, 4, 3, 2, -1, 2, 1, 0,
        ),
    );

    let coefficients = mm256_srlv_epi32(coefficients, mm256_set_epi32(4, 0, 4, 0, 4, 0, 4, 0));
    let coefficients = mm256_and_si256(coefficients, mm256_set1_epi32(GAMMA1_TIMES_2_MASK));

    mm256_sub_epi32(mm256_set1_epi32(GAMMA1), coefficients)
}

#[inline(always)]
pub(crate) fn deserialize<const GAMMA1_EXPONENT: usize>(serialized: &[u8]) -> Vec256 {
    match GAMMA1_EXPONENT as u8 {
        17 => deserialize_when_gamma1_is_2_pow_17(serialized),
        19 => deserialize_when_gamma1_is_2_pow_19(serialized),
        _ => unreachable!(),
    }
}
