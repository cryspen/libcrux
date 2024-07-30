use libcrux_intrinsics::avx2::*;

#[inline(always)]
pub(crate) fn extract_least_significant_bits(simd_unit: Vec256) -> u8 {
    let first_byte_from_each_i32_lane = mm256_shuffle_epi8(
        simd_unit,
        mm256_set_epi8(
            -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, 12, 8, 4, 0, -1, -1, -1, -1, -1, -1,
            -1, -1, -1, -1, -1, -1, 12, 8, 4, 0,
        ),
    );

    let bytes_grouped = mm256_permutevar8x32_epi32(
        first_byte_from_each_i32_lane,
        mm256_set_epi32(0, 0, 0, 0, 0, 0, 4, 0),
    );
    let bytes_grouped = mm256_castsi256_si128(bytes_grouped);

    let bits = mm_movemask_epi8(bytes_grouped);

    (bits & 0xFF) as u8
}

