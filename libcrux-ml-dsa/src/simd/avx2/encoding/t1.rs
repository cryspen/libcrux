use libcrux_intrinsics::avx2::*;

#[inline(always)]
pub fn serialize(simd_unit: Vec256) -> [u8; 10] {
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
