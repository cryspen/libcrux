use super::*;
use crate::vector::portable::PortableVector;

#[inline(always)]
pub(crate) fn serialize_1(vector: Vec256) -> [u8; 2] {
    // Suppose |vector| is laid out as follows (superscript number indicates the
    // corresponding bit is duplicated that many times):
    //
    // 0¹⁵a₀ 0¹⁵b₀ 0¹⁵c₀ 0¹⁵d₀ | 0¹⁵e₀ 0¹⁵f₀ 0¹⁵g₀ 0¹⁵h₀ | ...
    //
    // We care only about the least significant bit in each lane,
    // move it to the most significant position to make it easier to work with.
    // |vector| now becomes:
    //
    // a₀0¹⁵ b₀0¹⁵ c₀0¹⁵ d₀0¹⁵ | e₀0¹⁵ f₀0¹⁵ g₀0¹⁵ h₀0¹⁵ | ↩
    // i₀0¹⁵ j₀0¹⁵ k₀0¹⁵ l₀0¹⁵ | m₀0¹⁵ n₀0¹⁵ o₀0¹⁵ p₀0¹⁵
    let lsb_to_msb = mm256_slli_epi16::<15>(vector);

    // Get the first 8 16-bit elements ...
    let low_msbs = mm256_castsi256_si128(lsb_to_msb);

    // ... and the next 8 16-bit elements ...
    let high_msbs = mm256_extracti128_si256::<1>(lsb_to_msb);

    // ... and then pack them into 8-bit values using signed saturation.
    // This function packs all the |low_msbs|, and then the high ones.
    //
    //
    // low_msbs =  a₀0¹⁵ b₀0¹⁵ c₀0¹⁵ d₀0¹⁵ | e₀0¹⁵ f₀0¹⁵ g₀0¹⁵ h₀0¹⁵
    // high_msbs = i₀0¹⁵ j₀0¹⁵ k₀0¹⁵ l₀0¹⁵ | m₀0¹⁵ n₀0¹⁵ o₀0¹⁵ p₀0¹⁵
    //
    // We shifted by 15 above to take advantage of the signed saturation performed
    // by mm_packs_epi16:
    //
    // - if the sign bit of the 16-bit element being packed is 1, the
    // corresponding 8-bit element in |msbs| will be 0xFF.
    // - if the sign bit of the 16-bit element being packed is 0, the
    // corresponding 8-bit element in |msbs| will be 0.
    //
    // Thus, if, for example, a₀ = 1, e₀ = 1, and p₀ = 1, and every other bit
    // is 0, after packing into 8 bit value, |msbs| will look like:
    //
    // 0xFF 0x00 0x00 0x00 | 0xFF 0x00 0x00 0x00 | 0x00 0x00 0x00 0x00 | 0x00 0x00 0x00 0xFF
    let msbs = mm_packs_epi16(low_msbs, high_msbs);

    // Now that every element is either 0xFF or 0x00, we just extract the most
    // significant bit from each element and collate them into two bytes.
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
    // But since |_mm256_srlv_epi16| does not exist, so we have to resort to a
    // workaround.
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
        -32768,
        1 << 8,
        1 << 9,
        1 << 10,
        1 << 11,
        1 << 12,
        1 << 13,
        1 << 14,
        -32768,
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
    mm_storeu_bytes_si128(&mut serialized, combined);

    serialized[0..8].try_into().unwrap()
}

#[inline(always)]
pub(crate) fn deserialize_4(bytes: &[u8]) -> Vec256 {
    // Every 4 bits from each byte of input should be put into its own 16-bit lane.
    // Since |_mm256_srlv_epi16| does not exist, we have to resort to a workaround.
    //
    // Rather than shifting each element by a different amount, we'll multiply
    // each element by a value such that the bits we're interested in become the most
    // significant bits (of an 8-bit value).
    let coefficients = mm256_set_epi16(
        // In this lane, the 4 bits we need to put are already the most
        // significant bits of |bytes[7]|.
        bytes[7] as i16,
        // In this lane, the 4 bits we need to put are the least significant bits,
        // so we need to shift the 4 least-significant bits of |bytes[7]| to the
        // most significant bits (of an 8-bit value).
        bytes[7] as i16,
        // and so on ...
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

    let shift_lsbs_to_msbs = mm256_set_epi16(
        // These constants are chosen to shift the bits of the values
        // that we loaded into |coefficients|.
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

    let coefficients_in_msb = mm256_mullo_epi16(coefficients, shift_lsbs_to_msbs);

    // Once the 4-bit coefficients are in the most significant positions (of
    // an 8-bit value), shift them all down by 4.
    let coefficients_in_lsb = mm256_srli_epi16::<4>(coefficients_in_msb);

    // Zero the remaining bits.
    mm256_and_si256(coefficients_in_lsb, mm256_set1_epi16((1 << 4) - 1))
}

#[inline(always)]
pub(crate) fn serialize_5(vector: Vec256) -> [u8; 10] {
    let mut serialized = [0u8; 32];

    // If |vector| is laid out as follows (superscript number indicates the
    // corresponding bit is duplicated that many times):
    //
    // 0¹¹a₄a₃a₂a₁a₀ 0¹¹b₄b₃b₂b₁b₀ 0¹¹c₄c₃c₂c₁c₀ 0¹¹d₄d₃d₂d₁d₀ | ↩
    // 0¹¹e₄e₃e₂e₁e₀ 0¹¹f₄f₃f₂f₁f₀ 0¹¹g₄g₃g₂g₁g₀ 0¹¹h₄h₃h₂h₁h₀ | ↩
    //
    // |adjacent_2_combined| will be laid out as a series of 32-bit integers,
    // as follows:
    //
    // 0²²b₄b₃b₂b₁b₀a₄a₃a₂a₁a₀ 0²²d₄d₃d₂d₁d₀c₄c₃c₂c₁c₀ | ↩
    // 0²²f₄f₃f₂f₁f₀e₄e₃e₂e₁e₀ 0²²h₄h₃h₂h₁h₀g₄g₃g₂g₁g₀ | ↩
    // ....
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

    // Recall that |adjacent_2_combined| is laid out as follows:
    //
    // 0²²b₄b₃b₂b₁b₀a₄a₃a₂a₁a₀ 0²²d₄d₃d₂d₁d₀c₄c₃c₂c₁c₀ | ↩
    // 0²²f₄f₃f₂f₁f₀e₄e₃e₂e₁e₀ 0²²h₄h₃h₂h₁h₀g₄g₃g₂g₁g₀ | ↩
    // ....
    //
    // This shift results in:
    //
    // b₄b₃b₂b₁b₀a₄a₃a₂a₁a₀0²² 0²²d₄d₃d₂d₁d₀c₄c₃c₂c₁c₀ | ↩
    // f₄f₃f₂f₁f₀e₄e₃e₂e₁e₀0²² 0²²h₄h₃h₂h₁h₀g₄g₃g₂g₁g₀ | ↩
    // ....
    //
    let adjacent_4_combined = mm256_sllv_epi32(
        adjacent_2_combined,
        mm256_set_epi32(0, 22, 0, 22, 0, 22, 0, 22),
    );

    // |adjacent_4_combined|, when viewed as 64-bit lanes, is:
    //
    // 0²²d₄d₃d₂d₁d₀c₄c₃c₂c₁c₀b₄b₃b₂b₁b₀a₄a₃a₂a₁a₀0²² | ↩
    // 0²²h₄h₃h₂h₁h₀g₄g₃g₂g₁g₀f₄f₃f₂f₁f₀e₄e₃e₂e₁e₀0²² | ↩
    // ...
    //
    // so we just shift down by 22 bits to remove the least significant 0 bits
    // that aren't part of the bits we need.
    let adjacent_4_combined = mm256_srli_epi64::<22>(adjacent_4_combined);

    // |adjacent_4_combined|, when viewed as a set of 32-bit values, looks like:
    //
    // 0:0¹²d₄d₃d₂d₁d₀c₄c₃c₂c₁c₀b₄b₃b₂b₁b₀a₄a₃a₂a₁a₀ 1:0³² 2:0¹²h₄h₃h₂h₁h₀g₄g₃g₂g₁g₀f₄f₃f₂f₁f₀e₄e₃e₂e₁e₀ 3:0³² | ↩
    //
    // To be able to read out the bytes in one go, we need to shifts the bits in
    // position 2 to position 1 in each 128-bit lane.
    let adjacent_8_combined = mm256_shuffle_epi32::<0b00_00_10_00>(adjacent_4_combined);

    // |adjacent_8_combined|, when viewed as a set of 32-bit values, now looks like:
    //
    // 0¹²d₄d₃d₂d₁d₀c₄c₃c₂c₁c₀b₄b₃b₂b₁b₀a₄a₃a₂a₁a₀ 0¹²h₄h₃h₂h₁h₀g₄g₃g₂g₁g₀f₄f₃f₂f₁f₀e₄e₃e₂e₁e₀ 0³² 0³² | ↩
    //
    // Once again, we line these bits up by shifting the up values at indices
    // 0 and 5 by 12, viewing the resulting register as a set of 64-bit values,
    // and then shifting down the 64-bit values by 12 bits.
    let adjacent_8_combined = mm256_sllv_epi32(
        adjacent_8_combined,
        mm256_set_epi32(0, 0, 0, 12, 0, 0, 0, 12),
    );
    let adjacent_8_combined = mm256_srli_epi64::<12>(adjacent_8_combined);

    // We now have 40 bits starting at position 0 in the lower 128-bit lane, ...
    let lower_8 = mm256_castsi256_si128(adjacent_8_combined);
    mm_storeu_bytes_si128(&mut serialized[0..16], lower_8);

    // ... and the second 40 bits at position 0 in the upper 128-bit lane
    let upper_8 = mm256_extracti128_si256::<1>(adjacent_8_combined);
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

    // If |vector| is laid out as follows (superscript number indicates the
    // corresponding bit is duplicated that many times):
    //
    // 0⁶a₉a₈a₇a₆a₅a₄a₃a₂a₁a₀ 0⁶b₉b₈b₇b₆b₅b₄b₃b₂b₁b₀ 0⁶c₉c₈c₇c₆c₅c₄c₃c₂c₁c₀ 0⁶d₉d₈d₇d₆d₅d₄d₃d₂d₁d₀ | ↩
    // 0⁶e₉e₈e₇e₆e₅e₄e₃e₂e₁e₀ 0⁶f₉f₈f₇f₆f₅f₄f₃f₂f₁f₀ 0⁶g₉g₈g₇g₆g₅g₄g₃g₂g₁g₀ 0⁶h₉h₈h₇h₆h₅h₄h₃h₂h₁h₀ | ↩
    // ...
    //
    // |adjacent_2_combined| will be laid out as a series of 32-bit integers,
    // as follows:
    //
    // 0¹²b₉b₈b₇b₆b₅b₄b₃b₂b₁b₀a₉a₈a₇a₆a₅a₄a₃a₂a₁a₀ 0¹²d₉d₈d₇d₆d₅d₄d₃d₂d₁d₀c₉c₈c₇c₆c₅c₄c₃c₂c₁c₀ | ↩
    // 0¹²f₉f₈f₇f₆f₅f₄f₃f₂f₁f₀e₉e₈e₇e₆e₅e₄e₃e₂e₁e₀ 0¹²h₉h₈h₇h₆h₅h₄h₃h₂h₁h₀g₉g₈g₇g₆g₅g₄g₃g₂g₁g₀ | ↩
    // ....
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

    // Shifting up the values at the even indices by 12, we get:
    //
    // b₉b₈b₇b₆b₅b₄b₃b₂b₁b₀a₉a₈a₇a₆a₅a₄a₃a₂a₁a₀0¹² 0¹²d₉d₈d₇d₆d₅d₄d₃d₂d₁d₀c₉c₈c₇c₆c₅c₄c₃c₂c₁c₀ | ↩
    // f₉f₈f₇f₆f₅f₄f₃f₂f₁f₀e₉e₈e₇e₆e₅e₄e₃e₂e₁e₀0¹² 0¹²h₉h₈h₇h₆h₅h₄h₃h₂h₁h₀g₉g₈g₇g₆g₅g₄g₃g₂g₁g₀ | ↩
    // ...
    let adjacent_4_combined = mm256_sllv_epi32(
        adjacent_2_combined,
        mm256_set_epi32(0, 12, 0, 12, 0, 12, 0, 12),
    );

    // Viewing this as a set of 64-bit integers we get:
    //
    // 0¹²d₉d₈d₇d₆d₅d₄d₃d₂d₁d₀c₉c₈c₇c₆c₅c₄c₃c₂c₁c₀b₉b₈b₇b₆b₅b₄b₃b₂b₁b₀a₉a₈a₇a₆a₅a₄a₃a₂a₁a₀0¹²  | ↩
    // 0¹²h₉h₈h₇h₆h₅h₄h₃h₂h₁h₀g₉g₈g₇g₆g₅g₄g₃g₂g₁g₀f₉f₈f₇f₆f₅f₄f₃f₂f₁f₀e₉e₈e₇e₆e₅e₄e₃e₂e₁e₀0¹²  | ↩
    // ...
    //
    // Shifting down by 12 gives us:
    //
    // 0²⁴d₉d₈d₇d₆d₅d₄d₃d₂d₁d₀c₉c₈c₇c₆c₅c₄c₃c₂c₁c₀b₉b₈b₇b₆b₅b₄b₃b₂b₁b₀a₉a₈a₇a₆a₅a₄a₃a₂a₁a₀ | ↩
    // 0²⁴h₉h₈h₇h₆h₅h₄h₃h₂h₁h₀g₉g₈g₇g₆g₅g₄g₃g₂g₁g₀f₉f₈f₇f₆f₅f₄f₃f₂f₁f₀e₉e₈e₇e₆e₅e₄e₃e₂e₁e₀ | ↩
    // ...
    let adjacent_4_combined = mm256_srli_epi64::<12>(adjacent_4_combined);

    // |adjacent_4_combined|, when the bottom and top 128 bit-lanes are grouped
    // into bytes, looks like:
    //
    // 0₇0₆0₅B₄B₃B₂B₁B₀ | ↩
    // 0₁₅0₁₄0₁₃B₁₂B₁₁B₁₀B₉B₈ | ↩
    //
    // In each 128-bit lane, we want to put bytes 8, 9, 10, 11, 12 after
    // bytes 0, 1, 2, 3 to allow for sequential reading.
    let adjacent_8_combined = mm256_shuffle_epi8(
        adjacent_4_combined,
        mm256_set_epi8(
            -1, -1, -1, -1, -1, -1, 12, 11, 10, 9, 8, 4, 3, 2, 1, 0, -1, -1, -1, -1, -1, -1, 12,
            11, 10, 9, 8, 4, 3, 2, 1, 0,
        ),
    );

    // We now have 64 bits starting at position 0 in the lower 128-bit lane, ...
    let lower_8 = mm256_castsi256_si128(adjacent_8_combined);
    mm_storeu_bytes_si128(&mut serialized[0..16], lower_8);

    // and 64 bits starting at position 0 in the upper 128-bit lane.
    let upper_8 = mm256_extracti128_si256::<1>(adjacent_8_combined);
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

    let lower_coefficients = mm_loadu_si128(&bytes[0..16]);
    let lower_coefficients = mm_shuffle_epi8(
        lower_coefficients,
        mm_set_epi8(9, 8, 8, 7, 7, 6, 6, 5, 4, 3, 3, 2, 2, 1, 1, 0),
    );
    let upper_coefficients = mm_loadu_si128(&bytes[4..20]);
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
    let mut array = [0i16; 16];
    mm256_storeu_si256_i16(&mut array, vector);
    let input = PortableVector::from_i16_array(&array);
    PortableVector::serialize_11(input)
}

#[inline(always)]
pub(crate) fn deserialize_11(bytes: &[u8]) -> Vec256 {
    let output = PortableVector::deserialize_11(bytes);
    let array = PortableVector::to_i16_array(output);
    mm256_loadu_si256_i16(&array)
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

    let lower_coefficients = mm_loadu_si128(&bytes[0..16]);
    let lower_coefficients = mm_shuffle_epi8(
        lower_coefficients,
        mm_set_epi8(11, 10, 10, 9, 8, 7, 7, 6, 5, 4, 4, 3, 2, 1, 1, 0),
    );
    let upper_coefficients = mm_loadu_si128(&bytes[8..24]);
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
