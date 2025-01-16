use libcrux_intrinsics::avx2::*;

use crate::simd::avx2::Eta;

#[inline(always)]
fn serialize_when_eta_is_2(simd_unit: &Vec256, out: &mut [u8]) {
    let mut serialized = [0u8; 16];

    const ETA: i32 = 2;
    let simd_unit_shifted = mm256_sub_epi32(mm256_set1_epi32(ETA), *simd_unit);

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

    out.copy_from_slice(&serialized[0..3]);
}

#[inline(always)]
fn serialize_when_eta_is_4(simd_unit: &Vec256, out: &mut [u8]) {
    let mut serialized = [0u8; 16];

    const ETA: i32 = 4;
    let simd_unit_shifted = mm256_sub_epi32(mm256_set1_epi32(ETA), *simd_unit);

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

    out.copy_from_slice(&serialized[0..4])
}

#[inline(always)]
pub fn serialize(eta: Eta, simd_unit: &Vec256, serialized: &mut [u8]) {
    // [eurydice] injects an unused variable here in the C code for some reason.
    match eta {
        Eta::Two => serialize_when_eta_is_2(simd_unit, serialized),
        Eta::Four => serialize_when_eta_is_4(simd_unit, serialized),
    }
}

#[inline(always)]
fn deserialize_to_unsigned_when_eta_is_2(bytes: &[u8]) -> Vec256 {
    debug_assert!(bytes.len() == 3);

    const COEFFICIENT_MASK: i32 = (1 << 3) - 1;

    let bytes_in_simd_unit = mm256_set_epi32(
        bytes[2] as i32,
        bytes[2] as i32,
        ((bytes[2] as i32) << 8) | (bytes[1] as i32),
        bytes[1] as i32,
        bytes[1] as i32,
        ((bytes[1] as i32) << 8) | (bytes[0] as i32),
        bytes[0] as i32,
        bytes[0] as i32,
    );

    let coefficients =
        mm256_srlv_epi32(bytes_in_simd_unit, mm256_set_epi32(5, 2, 7, 4, 1, 6, 3, 0));

    mm256_and_si256(coefficients, mm256_set1_epi32(COEFFICIENT_MASK))
}

#[inline(always)]
fn deserialize_to_unsigned_when_eta_is_4(bytes: &[u8]) -> Vec256 {
    debug_assert!(bytes.len() == 4);

    const COEFFICIENT_MASK: i32 = (1 << 4) - 1;

    let bytes_in_simd_unit = mm256_set_epi32(
        bytes[3] as i32,
        bytes[3] as i32,
        bytes[2] as i32,
        bytes[2] as i32,
        bytes[1] as i32,
        bytes[1] as i32,
        bytes[0] as i32,
        bytes[0] as i32,
    );

    let coefficients =
        mm256_srlv_epi32(bytes_in_simd_unit, mm256_set_epi32(4, 0, 4, 0, 4, 0, 4, 0));

    mm256_and_si256(coefficients, mm256_set1_epi32(COEFFICIENT_MASK))
}
#[inline(always)]
pub(crate) fn deserialize_to_unsigned(eta: Eta, serialized: &[u8]) -> Vec256 {
    match eta {
        Eta::Two => deserialize_to_unsigned_when_eta_is_2(serialized),
        Eta::Four => deserialize_to_unsigned_when_eta_is_4(serialized),
    }
}

#[inline(always)]
pub(crate) fn deserialize(eta: Eta, serialized: &[u8], out: &mut Vec256) {
    let unsigned = deserialize_to_unsigned(eta, serialized);

    // [eurydice]: https://github.com/AeneasVerif/eurydice/issues/122
    let eta = match eta {
        Eta::Two => 2,
        Eta::Four => 4,
    };
    *out = mm256_sub_epi32(mm256_set1_epi32(eta), unsigned);
}
