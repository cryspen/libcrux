use libcrux_intrinsics::avx2::*;

use crate::constants::BITS_IN_LOWER_PART_OF_T;

#[inline(always)]
fn change_interval(simd_unit: Vec256) -> Vec256 {
    let interval_end = mm256_set1_epi32(1 << (BITS_IN_LOWER_PART_OF_T - 1));

    mm256_sub_epi32(interval_end, simd_unit)
}

#[inline(always)]
pub(crate) fn serialize(simd_unit: Vec256) -> [u8; 13] {
    let mut serialized = [0u8; 16];

    let simd_unit = change_interval(simd_unit);

    let adjacent_2_combined =
        mm256_sllv_epi32(simd_unit, mm256_set_epi32(0, 19, 0, 19, 0, 19, 0, 19));
    let adjacent_2_combined = mm256_srli_epi64::<19>(adjacent_2_combined);

    let adjacent_4_combined =
        mm256_permutevar8x32_epi32(adjacent_2_combined, mm256_set_epi32(0, 0, 0, 0, 6, 4, 2, 0));
    let adjacent_4_combined =
        mm256_sllv_epi32(adjacent_4_combined, mm256_set_epi32(0, 6, 0, 6, 0, 6, 0, 6));
    let adjacent_4_combined = mm256_srli_epi64::<6>(adjacent_4_combined);

    let second_4_combined = mm256_bsrli_epi128::<8>(adjacent_4_combined);
    let least_12_bits_shifted_up = mm256_slli_epi64::<52>(second_4_combined);

    let bits_sequential = mm256_add_epi64(adjacent_4_combined, least_12_bits_shifted_up);
    let bits_sequential = mm256_srlv_epi64(bits_sequential, mm256_set_epi64x(0, 0, 12, 0));

    let bits_sequential = mm256_castsi256_si128(bits_sequential);
    mm_storeu_bytes_si128(&mut serialized, bits_sequential);

    serialized[0..13].try_into().unwrap()
}

#[inline(always)]
pub(crate) fn deserialize(serialized: &[u8]) -> Vec256 {
    debug_assert_eq!(serialized.len(), 13);

    const COEFFICIENT_MASK: i32 = (1 << 13) - 1;

    let mut serialized_extended = [0u8; 16];
    serialized_extended[0..13].copy_from_slice(serialized);

    let serialized = mm_loadu_si128(&serialized_extended);
    let serialized = mm256_set_m128i(serialized, serialized);

    let coefficients = mm256_shuffle_epi8(
        serialized,
        mm256_set_epi8(
            -1, -1, 12, 11, -1, 11, 10, 9, -1, -1, 9, 8, -1, 8, 7, 6, -1, 6, 5, 4, -1, -1, 4, 3,
            -1, 3, 2, 1, -1, -1, 1, 0,
        ),
    );

    let coefficients = mm256_srlv_epi32(coefficients, mm256_set_epi32(3, 6, 1, 4, 7, 2, 5, 0));
    let coefficients = mm256_and_si256(coefficients, mm256_set1_epi32(COEFFICIENT_MASK));

    change_interval(coefficients)
}
