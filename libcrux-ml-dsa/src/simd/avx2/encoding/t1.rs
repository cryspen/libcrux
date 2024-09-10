use libcrux_intrinsics::avx2::*;

#[inline(always)]
pub(crate) fn serialize(simd_unit: Vec256) -> [u8; 10] {
    let mut serialized = [0u8; 24];

    let adjacent_2_combined =
        mm256_sllv_epi32(simd_unit, mm256_set_epi32(0, 22, 0, 22, 0, 22, 0, 22));
    let adjacent_2_combined = mm256_srli_epi64::<22>(adjacent_2_combined);

    let adjacent_4_combined =
        mm256_permutevar8x32_epi32(adjacent_2_combined, mm256_set_epi32(0, 0, 6, 4, 0, 0, 2, 0));
    let adjacent_4_combined = mm256_sllv_epi32(
        adjacent_4_combined,
        mm256_set_epi32(0, 12, 0, 12, 0, 12, 0, 12),
    );
    let adjacent_4_combined = mm256_srli_epi64::<12>(adjacent_4_combined);

    // We now have 40 bits starting at position 0 in the lower 128-bit lane, ...
    let lower_4 = mm256_castsi256_si128(adjacent_4_combined);
    mm_storeu_bytes_si128(&mut serialized[0..16], lower_4);

    // and 40 bits starting at position 0 in the upper 128-bit lane.
    let upper_4 = mm256_extracti128_si256::<1>(adjacent_4_combined);
    mm_storeu_bytes_si128(&mut serialized[5..21], upper_4);

    serialized[0..10].try_into().unwrap()
}

#[inline(always)]
pub(crate) fn deserialize(bytes: &[u8]) -> Vec256 {
    debug_assert_eq!(bytes.len(), 10);

    const COEFFICIENT_MASK: i32 = (1 << 10) - 1;

    let mut bytes_extended = [0u8; 16];
    bytes_extended[0..10].copy_from_slice(bytes);

    let bytes_loaded = mm_loadu_si128(&bytes_extended);
    let bytes_loaded = mm256_set_m128i(bytes_loaded, bytes_loaded);

    let coefficients = mm256_shuffle_epi8(
        bytes_loaded,
        mm256_set_epi8(
            -1, -1, 9, 8, -1, -1, 8, 7, -1, -1, 7, 6, -1, -1, 6, 5, -1, -1, 4, 3, -1, -1, 3, 2, -1,
            -1, 2, 1, -1, -1, 1, 0,
        ),
    );

    let coefficients = mm256_srlv_epi32(coefficients, mm256_set_epi32(6, 4, 2, 0, 6, 4, 2, 0));

    mm256_and_si256(coefficients, mm256_set1_epi32(COEFFICIENT_MASK))
}
