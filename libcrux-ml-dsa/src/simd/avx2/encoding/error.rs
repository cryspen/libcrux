use libcrux_intrinsics::avx2::*;

#[inline(always)]
pub fn serialize<const OUTPUT_SIZE: usize>(simd_unit: Vec256) -> [u8; OUTPUT_SIZE] {
    let mut serialized = [0u8; 16];

    match OUTPUT_SIZE {
        3 => {
            const ETA: i32 = 2;
            let simd_unit_shifted = mm256_sub_epi32(mm256_set1_epi32(ETA), simd_unit);

            let adjacent_2_combined =
                mm256_sllv_epi32(simd_unit_shifted, mm256_set_epi32(0, 29, 0, 29, 0, 29, 0, 29));
            let adjacent_2_combined = mm256_srli_epi64::<29>(adjacent_2_combined);
        }

        4 => {
            const ETA: i32 = 4;
            let simd_unit_shifted = mm256_sub_epi32(mm256_set1_epi32(ETA), simd_unit);

            let adjacent_2_combined =
                mm256_sllv_epi32(simd_unit_shifted, mm256_set_epi32(0, 28, 0, 28, 0, 28, 0, 28));
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

            serialized[0..4].try_into().unwrap()
        }

        _ => unreachable!(),
    }
}
