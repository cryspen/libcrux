use libcrux_intrinsics::avx2::*;

#[inline(always)]
fn serialize_when_eta_is_2<const OUTPUT_SIZE: usize>(simd_unit: Vec256) -> [u8; OUTPUT_SIZE] {
    let mut serialized = [0u8; 16];

    const ETA: i32 = 2;
    let simd_unit_shifted = mm256_sub_epi32(mm256_set1_epi32(ETA), simd_unit);

    let adjacent_2_combined = mm256_sllv_epi32(
        simd_unit_shifted,
        mm256_set_epi32(0, 29, 0, 29, 0, 29, 0, 29),
    );
    let adjacent_2_combined = mm256_srli_epi64::<29>(adjacent_2_combined);

    let adjacent_4_combined = mm256_shuffle_epi8(
        adjacent_2_combined,
        mm256_set_epi8(
            -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, 8, -1, 0, -1, -1, -1, -1, -1, -1,
            -1, -1, -1, -1, -1, -1, -1, 8, -1, 0,
        ),
    );
    let adjacent_4_combined = mm256_madd_epi16(
        adjacent_4_combined,
        mm256_set_epi16(0, 0, 0, 0, 0, 0, 1 << 6, 1, 0, 0, 0, 0, 0, 0, 1 << 6, 1),
    );

    let adjacent_6_combined =
        mm256_permutevar8x32_epi32(adjacent_4_combined, mm256_set_epi32(0, 0, 0, 0, 0, 0, 4, 0));
    let adjacent_6_combined = mm256_castsi256_si128(adjacent_6_combined);

    let adjacent_6_combined = mm_sllv_epi32(adjacent_6_combined, mm_set_epi32(0, 0, 0, 20));
    let adjacent_6_combined = mm_srli_epi64::<20>(adjacent_6_combined);

    mm_storeu_bytes_si128(&mut serialized[0..16], adjacent_6_combined);

    serialized[0..3].try_into().unwrap()
}
#[inline(always)]
fn serialize_when_eta_is_4<const OUTPUT_SIZE: usize>(simd_unit: Vec256) -> [u8; OUTPUT_SIZE] {
    let mut serialized = [0u8; 16];

    const ETA: i32 = 4;
    let simd_unit_shifted = mm256_sub_epi32(mm256_set1_epi32(ETA), simd_unit);

    let adjacent_2_combined = mm256_sllv_epi32(
        simd_unit_shifted,
        mm256_set_epi32(0, 28, 0, 28, 0, 28, 0, 28),
    );
    let adjacent_2_combined = mm256_srli_epi64::<28>(adjacent_2_combined);

    let adjacent_4_combined =
        mm256_permutevar8x32_epi32(adjacent_2_combined, mm256_set_epi32(0, 0, 0, 0, 6, 2, 4, 0));
    let adjacent_4_combined = mm256_castsi256_si128(adjacent_4_combined);
    let adjacent_4_combined = mm_shuffle_epi8(
        adjacent_4_combined,
        mm_set_epi8(
            0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 12, 4, 8, 0,
        ),
    );

    mm_storeu_bytes_si128(&mut serialized[0..16], adjacent_4_combined);

    serialized[0..4].try_into().unwrap()
}
#[inline(always)]
pub fn serialize<const OUTPUT_SIZE: usize>(simd_unit: Vec256) -> [u8; OUTPUT_SIZE] {
    match OUTPUT_SIZE {
        3 => serialize_when_eta_is_2::<OUTPUT_SIZE>(simd_unit),
        4 => serialize_when_eta_is_4::<OUTPUT_SIZE>(simd_unit),
        _ => unreachable!(),
    }
}
