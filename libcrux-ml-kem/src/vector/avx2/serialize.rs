use super::*;

#[inline(always)]
pub(crate) fn serialize_1(vector: Vec256) -> [u8; 2] {
    // We care only about the least significant bit in each lane,
    // move it to the most significant position to make it easier to work with.
    let lsb_to_msb = mm256_slli_epi16::<15>(vector);

    // Get the first 8 16-bit elements ...
    let low_msbs = mm256_castsi256_si128(lsb_to_msb);

    // ... and the next 8 16-bit elements ...
    let high_msbs = mm256_extracti128_si256::<1>(lsb_to_msb);

    // ... and then pack them into 8-bit values using signed saturation.
    // This function packs all the |low_msbs|, and then the high ones.
    //
    // We shifted by 15 above to take advantage of signed saturation:
    //
    // - if the sign bit of the 16-bit element being packed is 1, the
    // corresponding 8-bit element in |msbs| will be 0xFF.
    // - if the sign bit of the 16-bit element being packed is 0, the
    // corresponding 8-bit element in |msbs| will be 0.
    let msbs = mm_packs_epi16(low_msbs, high_msbs);

    // Now that we have all 16 bits we need conveniently placed in one vector,
    // extract them into two bytes.
    let bits_packed = mm_movemask_epi8(msbs);

    let mut serialized = [0u8; 2];
    serialized[0] = bits_packed as u8;
    serialized[1] = (bits_packed >> 8) as u8;

    serialized
}

#[inline(always)]
pub(crate) fn deserialize_1(bytes: &[u8]) -> Vec256 {
    // We need to take each bit from the 2 bytes of input and put them
    // into their own 16-bit lane. Ideally, we'd load the two bytes into the vector,
    // duplicate them, and right-shift the 0th element by 0 bits,
    // the first element by 1 bit, the second by 2 bits and so on before AND-ing
    // with 0x1 to leave only the least signifinicant bit.
    // But |_mm256_srlv_epi16| does not exist unfortunately, so we have to resort
    // to a workaround.
    //
    // Rather than shifting each element by a different amount, we'll multiply
    // each element by a value such that the bit we're interested in becomes the most
    // significant bit.

    // The coefficients are loaded as follows:
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

    // And this vector, when multiplied with the previous one, ensures that the
    // bit we'd like to keep in each lane becomes the most significant bit upon
    // multiplication.
    let shift_lsb_to_msb = mm256_set_epi16(
        1 << 8,
        1 << 9,
        1 << 10,
        1 << 11,
        1 << 12,
        1 << 13,
        1 << 14,
        1 << 15,
        1 << 8,
        1 << 9,
        1 << 10,
        1 << 11,
        1 << 12,
        1 << 13,
        1 << 14,
        1 << 15,
    );
    let coefficients_in_msb = mm256_mullo_epi16(coefficients, shift_lsb_to_msb);

    // Now that they're all in the most significant bit position, shift them
    // down to the least significant bit.
    mm256_srli_epi16::<15>(coefficients_in_msb)
}

#[inline(always)]
pub(crate) fn serialize_4(vector: Vec256) -> [u8; 8] {
    let mut serialized = [0u8; 16];

    // If |vector| is laid out as follows:
    //
    // 0x000A 0x000B 0x000C 0x000D | 0x000E 0x000F 0x000G 0x000H | ....
    //
    // |adjacent_2_combined| will be laid out as a series of 32-bit integeres,
    // as follows:
    //
    // 0x00_00_00_BA 0x00_00_00_DC | 0x00_00_00_FE 0x00_00_00_HG | ...
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

    // Recall that |adjacent_2_combined| goes as follows:
    //
    // 0x00_00_00_BA 0x00_00_00_DC | 0x00_00_00_FE 0x00_00_00_HG | ...
    //
    // Out of this, we only need the first byte, the 4th byte, the 8th byte
    // and so on from the bottom and the top 128 bits.
    let adjacent_8_combined = mm256_shuffle_epi8(
        adjacent_2_combined,
        mm256_set_epi8(
            -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, 12, 8, 4, 0, -1, -1, -1, -1, -1, -1,
            -1, -1, -1, -1, -1, -1, 12, 8, 4, 0,
        ),
    );

    // |adjacent_8_combined| looks like this:
    //
    // 0: 0xHG_FE_DC_BA 1: 0x00_00_00_00 | 2: 0x00_00_00_00 3: 0x00_00_00_00 | 4: 0xPO_NM_LK_JI ....
    //
    // We put the element at 4 after the element at 0 ...
    let combined =
        mm256_permutevar8x32_epi32(adjacent_8_combined, mm256_set_epi32(0, 0, 0, 0, 0, 0, 4, 0));
    let combined = mm256_castsi256_si128(combined);

    // ... so that we can read them out in one go.
    mm_storeu_bytes_si128(&mut serialized[..], combined);

    serialized[0..8].try_into().unwrap()
}

#[inline(always)]
pub(crate) fn deserialize_4(bytes: &[u8]) -> Vec256 {
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
pub(crate) fn serialize_5(vector: Vec256) -> [u8; 10] {
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
pub(crate) fn deserialize_5(bytes: &[u8]) -> Vec256 {
    let coefficients = mm_set_epi8(
        bytes[9], bytes[8], bytes[8], bytes[7], bytes[7], bytes[6], bytes[6], bytes[5], bytes[4],
        bytes[3], bytes[3], bytes[2], bytes[2], bytes[1], bytes[1], bytes[0],
    );

    let coefficients_loaded = mm256_castsi128_si256(coefficients);
    let coefficients_loaded = mm256_inserti128_si256::<1>(coefficients_loaded, coefficients);

    let coefficients = mm256_shuffle_epi8(
        coefficients_loaded,
        mm256_set_epi8(
            15, 14, 15, 14, 13, 12, 13, 12, 11, 10, 11, 10, 9, 8, 9, 8, 7, 6, 7, 6, 5, 4, 5, 4, 3,
            2, 3, 2, 1, 0, 1, 0,
        ),
    );

    let coefficients = mm256_mullo_epi16(
        coefficients,
        mm256_set_epi16(
            1 << 0,
            1 << 5,
            1 << 2,
            1 << 7,
            1 << 4,
            1 << 9,
            1 << 6,
            1 << 11,
            1 << 0,
            1 << 5,
            1 << 2,
            1 << 7,
            1 << 4,
            1 << 9,
            1 << 6,
            1 << 11,
        ),
    );
    mm256_srli_epi16::<11>(coefficients)
}

#[inline(always)]
pub(crate) fn serialize_10(vector: Vec256) -> [u8; 20] {
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
            -1, -1, -1, -1, -1, -1, 12, 11, 10, 9, 8, 4, 3, 2, 1, 0, -1, -1, -1, -1, -1, -1, 12,
            11, 10, 9, 8, 4, 3, 2, 1, 0,
        ),
    );

    let lower_8 = mm256_castsi256_si128(adjacent_8_combined);
    let upper_8 = mm256_extracti128_si256::<1>(adjacent_8_combined);

    mm_storeu_bytes_si128(&mut serialized[0..16], lower_8);
    mm_storeu_bytes_si128(&mut serialized[10..26], upper_8);

    serialized[0..20].try_into().unwrap()
}

#[inline(always)]
pub(crate) fn deserialize_10(bytes: &[u8]) -> Vec256 {
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
pub(crate) fn serialize_11(vector: Vec256) -> [u8; 22] {
    let input = portable::from_i16_array(to_i16_array(SIMD256Vector { elements: vector }));

    portable::serialize_11(input)
}

#[inline(always)]
pub(crate) fn deserialize_11(bytes: &[u8]) -> Vec256 {
    let output = portable::deserialize_11(bytes);

    from_i16_array(&portable::to_i16_array(output)).elements
}

#[inline(always)]
pub(crate) fn serialize_12(vector: Vec256) -> [u8; 24] {
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

    let adjacent_4_combined =
        mm256_sllv_epi32(adjacent_2_combined, mm256_set_epi32(0, 8, 0, 8, 0, 8, 0, 8));
    let adjacent_4_combined = mm256_srli_epi64::<8>(adjacent_4_combined);

    let adjacent_8_combined = mm256_shuffle_epi8(
        adjacent_4_combined,
        mm256_set_epi8(
            -1, -1, -1, -1, 13, 12, 11, 10, 9, 8, 5, 4, 3, 2, 1, 0, -1, -1, -1, -1, 13, 12, 11, 10,
            9, 8, 5, 4, 3, 2, 1, 0,
        ),
    );

    let lower_8 = mm256_castsi256_si128(adjacent_8_combined);
    let upper_8 = mm256_extracti128_si256::<1>(adjacent_8_combined);

    mm_storeu_bytes_si128(&mut serialized[0..16], lower_8);
    mm_storeu_bytes_si128(&mut serialized[12..28], upper_8);

    serialized[0..24].try_into().unwrap()
}

#[inline(always)]
pub(crate) fn deserialize_12(bytes: &[u8]) -> Vec256 {
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
