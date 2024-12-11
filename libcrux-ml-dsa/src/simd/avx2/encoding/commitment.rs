use libcrux_intrinsics::avx2::*;

#[inline(always)]
pub(in crate::simd::avx2) fn serialize(simd_unit: Vec256, out: &mut [u8]) {
    let mut serialized = [0u8; 19];

    match out.len() as u8 {
        4 => {
            let adjacent_2_combined =
                mm256_sllv_epi32(simd_unit, mm256_set_epi32(0, 28, 0, 28, 0, 28, 0, 28));
            let adjacent_2_combined = mm256_srli_epi64::<28>(adjacent_2_combined);

            let adjacent_4_combined = mm256_permutevar8x32_epi32(
                adjacent_2_combined,
                mm256_set_epi32(0, 0, 0, 0, 6, 2, 4, 0),
            );
            let adjacent_4_combined = mm256_castsi256_si128(adjacent_4_combined);
            let adjacent_4_combined = mm_shuffle_epi8(
                adjacent_4_combined,
                mm_set_epi8(
                    0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 12, 4,
                    8, 0,
                ),
            );

            mm_storeu_bytes_si128(&mut serialized[0..16], adjacent_4_combined);

            out.copy_from_slice(&serialized[0..4]);
        }

        6 => {
            let adjacent_2_combined =
                mm256_sllv_epi32(simd_unit, mm256_set_epi32(0, 26, 0, 26, 0, 26, 0, 26));
            let adjacent_2_combined = mm256_srli_epi64::<26>(adjacent_2_combined);

            let adjacent_3_combined = mm256_shuffle_epi8(
                adjacent_2_combined,
                mm256_set_epi8(
                    -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, 9, 8, 1, 0, -1, -1, -1, -1, -1,
                    -1, -1, -1, -1, -1, -1, -1, 9, 8, 1, 0,
                ),
            );

            let adjacent_3_combined = mm256_mullo_epi16(
                adjacent_3_combined,
                mm256_set_epi16(1, 1, 1, 1, 1, 1, 1, 1 << 4, 1, 1, 1, 1, 1, 1, 1, 1 << 4),
            );
            let adjacent_3_combined =
                mm256_srlv_epi32(adjacent_3_combined, mm256_set_epi32(0, 0, 0, 4, 0, 0, 0, 4));

            // We now have 24 bits starting at position 0 in the lower 128-bit lane, ...
            let lower_3 = mm256_castsi256_si128(adjacent_3_combined);
            mm_storeu_bytes_si128(&mut serialized[0..16], lower_3);

            // and 24 bits starting at position 0 in the upper 128-bit lane.
            let upper_3 = mm256_extracti128_si256::<1>(adjacent_3_combined);
            mm_storeu_bytes_si128(&mut serialized[3..19], upper_3);

            out.copy_from_slice(&serialized[0..6]);
        }

        _ => unreachable!(),
    }
}
