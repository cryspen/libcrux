use crate::intrinsics::*;

use crate::{portable, SIMD256Vector};

#[inline(always)]
pub(crate) fn serialize_1(vector: __m256i) -> [u8; 2] {
    let lsb_shifted_up = mm256_slli_epi16::<15>(vector);

    let low_lanes = mm256_castsi256_si128(lsb_shifted_up);
    let high_lanes = mm256_extracti128_si256::<1>(lsb_shifted_up);

    let msbs = mm_packs_epi16(low_lanes, high_lanes);

    let bits_packed = mm_movemask_epi8(msbs);

    let mut serialized = [0u8; 2];
    serialized[0] = bits_packed as u8;
    serialized[1] = (bits_packed >> 8) as u8;

    serialized
}

#[inline(always)]
pub(crate) fn deserialize_1(bytes: &[u8]) -> __m256i {
    let shift_lsb_to_msb = mm256_set_epi16(
        1 << 0,
        1 << 1,
        1 << 2,
        1 << 3,
        1 << 4,
        1 << 5,
        1 << 6,
        1 << 7,
        1 << 0,
        1 << 1,
        1 << 2,
        1 << 3,
        1 << 4,
        1 << 5,
        1 << 6,
        1 << 7,
    );

    let coefficients = mm256_set_epi16(
        bytes[1] as i16,
        bytes[1] as i16,
        bytes[1] as i16,
        bytes[1] as i16,
        bytes[1] as i16,
        bytes[1] as i16,
        bytes[1] as i16,
        bytes[1] as i16,
        bytes[0] as i16,
        bytes[0] as i16,
        bytes[0] as i16,
        bytes[0] as i16,
        bytes[0] as i16,
        bytes[0] as i16,
        bytes[0] as i16,
        bytes[0] as i16,
    );

    let coefficients_in_msb = mm256_mullo_epi16(coefficients, shift_lsb_to_msb);
    let coefficients_in_lsb = mm256_srli_epi16::<7>(coefficients_in_msb);

    mm256_and_si256(coefficients_in_lsb, mm256_set1_epi16((1 << 1) - 1))
}

#[inline(always)]
pub(crate) fn serialize_4(vector: __m256i) -> [u8; 8] {
    let mut serialized = [0u8; 16];

    let adjacent_2_combined = mm256_madd_epi16(
        vector,
        mm256_set_epi16(
            1 << 4,
            1,
            1 << 4,
            1,
            1 << 4,
            1,
            1 << 4,
            1,
            1 << 4,
            1,
            1 << 4,
            1,
            1 << 4,
            1,
            1 << 4,
            1,
        ),
    );

    let adjacent_8_combined = mm256_shuffle_epi8(
        adjacent_2_combined,
        mm256_set_epi8(
            -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, 12, 8, 4, 0, -1, -1, -1, -1, -1,
            -1, -1, -1, -1, -1, -1, -1, 12, 8, 4, 0,
        ),
    );

    let combined = mm256_permutevar8x32_epi32(
        adjacent_8_combined,
        mm256_set_epi32(0, 0, 0, 0, 0, 0, 4, 0),
    );
    let combined = mm256_castsi256_si128(combined);

    mm_storeu_bytes_si128(&mut serialized[..], combined);

    serialized[0..8].try_into().unwrap()
}

#[inline(always)]
pub(crate) fn deserialize_4(bytes: &[u8]) -> __m256i {
    let shift_lsbs_to_msbs = mm256_set_epi16(
        1 << 0,
        1 << 4,
        1 << 0,
        1 << 4,
        1 << 0,
        1 << 4,
        1 << 0,
        1 << 4,
        1 << 0,
        1 << 4,
        1 << 0,
        1 << 4,
        1 << 0,
        1 << 4,
        1 << 0,
        1 << 4,
    );

    let coefficients = mm256_set_epi16(
        bytes[7] as i16,
        bytes[7] as i16,
        bytes[6] as i16,
        bytes[6] as i16,
        bytes[5] as i16,
        bytes[5] as i16,
        bytes[4] as i16,
        bytes[4] as i16,
        bytes[3] as i16,
        bytes[3] as i16,
        bytes[2] as i16,
        bytes[2] as i16,
        bytes[1] as i16,
        bytes[1] as i16,
        bytes[0] as i16,
        bytes[0] as i16,
    );

    let coefficients_in_msb = mm256_mullo_epi16(coefficients, shift_lsbs_to_msbs);
    let coefficients_in_lsb = mm256_srli_epi16::<4>(coefficients_in_msb);

    mm256_and_si256(coefficients_in_lsb, mm256_set1_epi16((1 << 4) - 1))
}

#[inline(always)]
pub(crate) fn serialize_5(vector: __m256i) -> [u8; 10] {
    let mut serialized = [0u8; 32];

    let adjacent_2_combined = mm256_madd_epi16(
        vector,
        mm256_set_epi16(
            1 << 5,
            1,
            1 << 5,
            1,
            1 << 5,
            1,
            1 << 5,
            1,
            1 << 5,
            1,
            1 << 5,
            1,
            1 << 5,
            1,
            1 << 5,
            1,
        ),
    );

    let adjacent_4_combined = mm256_sllv_epi32(
        adjacent_2_combined,
        mm256_set_epi32(0, 22, 0, 22, 0, 22, 0, 22),
    );
    let adjacent_4_combined = mm256_srli_epi64::<22>(adjacent_4_combined);

    let adjacent_8_combined = mm256_shuffle_epi32::<0b00_00_10_00>(adjacent_4_combined);
    let adjacent_8_combined = mm256_sllv_epi32(
        adjacent_8_combined,
        mm256_set_epi32(0, 12, 0, 12, 0, 12, 0, 12),
    );
    let adjacent_8_combined = mm256_srli_epi64::<12>(adjacent_8_combined);

    let lower_8 = mm256_castsi256_si128(adjacent_8_combined);
    let upper_8 = mm256_extracti128_si256::<1>(adjacent_8_combined);

    mm_storeu_bytes_si128(&mut serialized[0..16], lower_8);
    mm_storeu_bytes_si128(&mut serialized[5..21], upper_8);

    serialized[0..10].try_into().unwrap()
}

#[inline(always)]
pub(crate) fn deserialize_5(bytes: &[u8]) -> __m256i {
    let output = portable::deserialize_5(bytes);

    crate::from_i16_array(&portable::to_i16_array(output)).elements
}

#[inline(always)]
pub(crate) fn serialize_10(vector: __m256i) -> [u8; 20] {
    let mut serialized = [0u8; 32];

    let adjacent_2_combined = mm256_madd_epi16(
        vector,
        mm256_set_epi16(
            1 << 10,
            1,
            1 << 10,
            1,
            1 << 10,
            1,
            1 << 10,
            1,
            1 << 10,
            1,
            1 << 10,
            1,
            1 << 10,
            1,
            1 << 10,
            1,
        ),
    );

    let adjacent_4_combined = mm256_sllv_epi32(
        adjacent_2_combined,
        mm256_set_epi32(0, 12, 0, 12, 0, 12, 0, 12),
    );
    let adjacent_4_combined = mm256_srli_epi64::<12>(adjacent_4_combined);

    let adjacent_8_combined = mm256_shuffle_epi8(
        adjacent_4_combined,
        mm256_set_epi8(
            -1, -1, -1, -1, -1, -1, 12, 11, 10, 9, 8, 4, 3, 2, 1, 0, -1, -1, -1, -1, -1, -1,
            12, 11, 10, 9, 8, 4, 3, 2, 1, 0,
        ),
    );

    let lower_8 = mm256_castsi256_si128(adjacent_8_combined);
    let upper_8 = mm256_extracti128_si256::<1>(adjacent_8_combined);

    mm_storeu_bytes_si128(&mut serialized[0..16], lower_8);
    mm_storeu_bytes_si128(&mut serialized[10..26], upper_8);

    serialized[0..20].try_into().unwrap()
}

#[inline(always)]
pub(crate) fn deserialize_10(bytes: &[u8]) -> __m256i {
    let shift_lsbs_to_msbs = mm256_set_epi16(
        1 << 0,
        1 << 2,
        1 << 4,
        1 << 6,
        1 << 0,
        1 << 2,
        1 << 4,
        1 << 6,
        1 << 0,
        1 << 2,
        1 << 4,
        1 << 6,
        1 << 0,
        1 << 2,
        1 << 4,
        1 << 6,
    );

    let lower_coefficients = mm_loadu_si128(bytes[0..16].try_into().unwrap());
    let lower_coefficients = mm_shuffle_epi8(
        lower_coefficients,
        mm_set_epi8(9, 8, 8, 7, 7, 6, 6, 5, 4, 3, 3, 2, 2, 1, 1, 0),
    );
    let upper_coefficients = mm_loadu_si128(bytes[4..20].try_into().unwrap());
    let upper_coefficients = mm_shuffle_epi8(
        upper_coefficients,
        mm_set_epi8(15, 14, 14, 13, 13, 12, 12, 11, 10, 9, 9, 8, 8, 7, 7, 6),
    );

    let coefficients = mm256_castsi128_si256(lower_coefficients);
    let coefficients = mm256_inserti128_si256::<1>(coefficients, upper_coefficients);

    let coefficients = mm256_mullo_epi16(coefficients, shift_lsbs_to_msbs);
    let coefficients = mm256_srli_epi16::<6>(coefficients);
    let coefficients = mm256_and_si256(coefficients, mm256_set1_epi16((1 << 10) - 1));

    coefficients
}

#[inline(always)]
pub(crate) fn serialize_11(vector: __m256i) -> [u8; 22] {
    let input = portable::from_i16_array(crate::to_i16_array(SIMD256Vector { elements: vector }));

    portable::serialize_11(input)
}

#[inline(always)]
pub(crate) fn deserialize_11(bytes: &[u8]) -> __m256i {
    let output = portable::deserialize_11(bytes);

    crate::from_i16_array(&portable::to_i16_array(output)).elements
}

#[inline(always)]
pub(crate) fn serialize_12(vector: __m256i) -> [u8; 24] {
    let mut serialized = [0u8; 32];

    let adjacent_2_combined = mm256_madd_epi16(
        vector,
        mm256_set_epi16(
            1 << 12,
            1,
            1 << 12,
            1,
            1 << 12,
            1,
            1 << 12,
            1,
            1 << 12,
            1,
            1 << 12,
            1,
            1 << 12,
            1,
            1 << 12,
            1,
        ),
    );

    let adjacent_4_combined = mm256_sllv_epi32(
        adjacent_2_combined,
        mm256_set_epi32(0, 8, 0, 8, 0, 8, 0, 8),
    );
    let adjacent_4_combined = mm256_srli_epi64::<8>(adjacent_4_combined);

    let adjacent_8_combined = mm256_shuffle_epi8(
        adjacent_4_combined,
        mm256_set_epi8(
            -1, -1, -1, -1, 13, 12, 11, 10, 9, 8, 5, 4, 3, 2, 1, 0, -1, -1, -1, -1, 13, 12, 11,
            10, 9, 8, 5, 4, 3, 2, 1, 0,
        ),
    );

    let lower_8 = mm256_castsi256_si128(adjacent_8_combined);
    let upper_8 = mm256_extracti128_si256::<1>(adjacent_8_combined);

    mm_storeu_bytes_si128(&mut serialized[0..16], lower_8);
    mm_storeu_bytes_si128(&mut serialized[12..28], upper_8);

    serialized[0..24].try_into().unwrap()
}

#[inline(always)]
pub(crate) fn deserialize_12(bytes: &[u8]) -> __m256i {
    let shift_lsbs_to_msbs = mm256_set_epi16(
        1 << 0,
        1 << 4,
        1 << 0,
        1 << 4,
        1 << 0,
        1 << 4,
        1 << 0,
        1 << 4,
        1 << 0,
        1 << 4,
        1 << 0,
        1 << 4,
        1 << 0,
        1 << 4,
        1 << 0,
        1 << 4,
    );

    let lower_coefficients = mm_loadu_si128(bytes[0..16].try_into().unwrap());
    let lower_coefficients = mm_shuffle_epi8(
        lower_coefficients,
        mm_set_epi8(11, 10, 10, 9, 8, 7, 7, 6, 5, 4, 4, 3, 2, 1, 1, 0),
    );
    let upper_coefficients = mm_loadu_si128(bytes[8..24].try_into().unwrap());
    let upper_coefficients = mm_shuffle_epi8(
        upper_coefficients,
        mm_set_epi8(15, 14, 14, 13, 12, 11, 11, 10, 9, 8, 8, 7, 6, 5, 5, 4),
    );

    let coefficients = mm256_castsi128_si256(lower_coefficients);
    let coefficients = mm256_inserti128_si256::<1>(coefficients, upper_coefficients);

    let coefficients = mm256_mullo_epi16(coefficients, shift_lsbs_to_msbs);
    let coefficients = mm256_srli_epi16::<4>(coefficients);
    let coefficients = mm256_and_si256(coefficients, mm256_set1_epi16((1 << 12) - 1));

    coefficients
}
