#[cfg(target_arch = "x86")]
use core::arch::x86::*;
#[cfg(target_arch = "x86_64")]
use core::arch::x86_64::*;

use crate::portable;
use crate::SIMD256Vector;

#[inline(always)]
pub(crate) fn serialize_1(v: SIMD256Vector) -> [u8; 2] {
    let mut serialized = [0u8; 2];

    let bits_packed = unsafe {
        let lsb_shifted_up = _mm256_slli_epi16(v.elements, 15);

        let low_lanes = _mm256_castsi256_si128(lsb_shifted_up);
        let high_lanes = _mm256_extracti128_si256(lsb_shifted_up, 1);

        let msbs = _mm_packs_epi16(low_lanes, high_lanes);

        _mm_movemask_epi8(msbs)
    };

    serialized[0] = bits_packed as u8;
    serialized[1] = (bits_packed >> 8) as u8;

    serialized
}

#[inline(always)]
pub(crate) fn deserialize_1(bytes: &[u8]) -> SIMD256Vector {
    let deserialized = unsafe {
        let shift_lsb_to_msb = _mm256_set_epi16(
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

        let coefficients = _mm256_set_epi16(
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

        let coefficients_in_msb = _mm256_mullo_epi16(coefficients, shift_lsb_to_msb);
        let coefficients_in_lsb = _mm256_srli_epi16(coefficients_in_msb, 7);

        _mm256_and_si256(coefficients_in_lsb, _mm256_set1_epi16((1 << 1) - 1))
    };

    SIMD256Vector {
        elements: deserialized,
    }
}

#[inline(always)]
pub(crate) fn serialize_4(v: SIMD256Vector) -> [u8; 8] {
    let mut serialized = [0u8; 16];

    unsafe {
        let adjacent_2_combined = _mm256_madd_epi16(
            v.elements,
            _mm256_set_epi16(
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

        let adjacent_8_combined = _mm256_shuffle_epi8(
            adjacent_2_combined,
            _mm256_set_epi8(
                -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, 12, 8, 4, 0, -1, -1, -1, -1, -1,
                -1, -1, -1, -1, -1, -1, -1, 12, 8, 4, 0,
            ),
        );

        let combined = _mm256_permutevar8x32_epi32(
            adjacent_8_combined,
            _mm256_set_epi32(0, 0, 0, 0, 0, 0, 4, 0),
        );
        let combined = _mm256_castsi256_si128(combined);

        _mm_storeu_si128(serialized.as_mut_ptr() as *mut __m128i, combined);
    }

    serialized[0..8].try_into().unwrap()
}

#[inline(always)]
pub(crate) fn deserialize_4(bytes: &[u8]) -> SIMD256Vector {
    let deserialized = unsafe {
        let shift_lsbs_to_msbs = _mm256_set_epi16(
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

        let coefficients = _mm256_set_epi16(
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

        let coefficients_in_msb = _mm256_mullo_epi16(coefficients, shift_lsbs_to_msbs);
        let coefficients_in_lsb = _mm256_srli_epi16(coefficients_in_msb, 4);

        _mm256_and_si256(coefficients_in_lsb, _mm256_set1_epi16((1 << 4) - 1))
    };

    SIMD256Vector {
        elements: deserialized,
    }
}

#[inline(always)]
pub(crate) fn serialize_5(v: SIMD256Vector) -> [u8; 10] {
    let mut serialized = [0u8; 32];

    unsafe {
        let adjacent_2_combined = _mm256_madd_epi16(
            v.elements,
            _mm256_set_epi16(
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

        let adjacent_4_combined = _mm256_sllv_epi32(
            adjacent_2_combined,
            _mm256_set_epi32(0, 22, 0, 22, 0, 22, 0, 22),
        );
        let adjacent_4_combined = _mm256_srli_epi64(adjacent_4_combined, 22);

        let adjacent_8_combined = _mm256_shuffle_epi32(adjacent_4_combined, 0b00_00_10_00);
        let adjacent_8_combined = _mm256_sllv_epi32(
            adjacent_8_combined,
            _mm256_set_epi32(0, 12, 0, 12, 0, 12, 0, 12),
        );
        let adjacent_8_combined = _mm256_srli_epi64(adjacent_8_combined, 12);

        let lower_8 = _mm256_castsi256_si128(adjacent_8_combined);
        let upper_8 = _mm256_extracti128_si256(adjacent_8_combined, 1);

        _mm_storeu_si128(serialized.as_mut_ptr() as *mut __m128i, lower_8);
        _mm_storeu_si128(serialized.as_mut_ptr().offset(5) as *mut __m128i, upper_8);
    }

    serialized[0..10].try_into().unwrap()
}

#[inline(always)]
pub(crate) fn deserialize_5(v: &[u8]) -> SIMD256Vector {
    let output = portable::deserialize_5(v);

    crate::from_i16_array(&portable::to_i16_array(output))
}

#[inline(always)]
pub(crate) fn serialize_10(v: SIMD256Vector) -> [u8; 20] {
    let mut serialized = [0u8; 32];

    unsafe {
        let adjacent_2_combined = _mm256_madd_epi16(
            v.elements,
            _mm256_set_epi16(
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

        let adjacent_4_combined = _mm256_sllv_epi32(
            adjacent_2_combined,
            _mm256_set_epi32(0, 12, 0, 12, 0, 12, 0, 12),
        );
        let adjacent_4_combined = _mm256_srli_epi64(adjacent_4_combined, 12);

        let adjacent_8_combined = _mm256_shuffle_epi8(
            adjacent_4_combined,
            _mm256_set_epi8(
                -1, -1, -1, -1, -1, -1, 12, 11, 10, 9, 8, 4, 3, 2, 1, 0, -1, -1, -1, -1, -1, -1,
                12, 11, 10, 9, 8, 4, 3, 2, 1, 0,
            ),
        );

        let lower_8 = _mm256_castsi256_si128(adjacent_8_combined);
        let upper_8 = _mm256_extracti128_si256(adjacent_8_combined, 1);

        _mm_storeu_si128(serialized.as_mut_ptr() as *mut __m128i, lower_8);
        _mm_storeu_si128(serialized.as_mut_ptr().offset(10) as *mut __m128i, upper_8);
    }

    serialized[0..20].try_into().unwrap()
}

#[inline(always)]
pub(crate) fn deserialize_10(v: &[u8]) -> SIMD256Vector {
    let deserialized = unsafe {
        let shift_lsbs_to_msbs = _mm256_set_epi16(
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

        let lower_coefficients = _mm_loadu_si128(v.as_ptr() as *const __m128i);
        let lower_coefficients = _mm_shuffle_epi8(
            lower_coefficients,
            _mm_set_epi8(9, 8, 8, 7, 7, 6, 6, 5, 4, 3, 3, 2, 2, 1, 1, 0),
        );
        let upper_coefficients = _mm_loadu_si128(v.as_ptr().offset(4) as *const __m128i);
        let upper_coefficients = _mm_shuffle_epi8(
            upper_coefficients,
            _mm_set_epi8(15, 14, 14, 13, 13, 12, 12, 11, 10, 9, 9, 8, 8, 7, 7, 6),
        );

        let coefficients = _mm256_castsi128_si256(lower_coefficients);
        let coefficients = _mm256_inserti128_si256(coefficients, upper_coefficients, 1);

        let coefficients = _mm256_mullo_epi16(coefficients, shift_lsbs_to_msbs);
        let coefficients = _mm256_srli_epi16(coefficients, 6);
        let coefficients = _mm256_and_si256(coefficients, _mm256_set1_epi16((1 << 10) - 1));

        coefficients
    };

    SIMD256Vector {
        elements: deserialized,
    }
}

#[inline(always)]
pub(crate) fn serialize_11(v: SIMD256Vector) -> [u8; 22] {
    let input = portable::from_i16_array(crate::to_i16_array(v));

    portable::serialize_11(input)
}

#[inline(always)]
pub(crate) fn deserialize_11(v: &[u8]) -> SIMD256Vector {
    let output = portable::deserialize_11(v);

    crate::from_i16_array(&portable::to_i16_array(output))
}

#[inline(always)]
pub(crate) fn serialize_12(v: SIMD256Vector) -> [u8; 24] {
    let mut serialized = [0u8; 32];

    unsafe {
        let adjacent_2_combined = _mm256_madd_epi16(
            v.elements,
            _mm256_set_epi16(
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

        let adjacent_4_combined = _mm256_sllv_epi32(
            adjacent_2_combined,
            _mm256_set_epi32(0, 8, 0, 8, 0, 8, 0, 8),
        );
        let adjacent_4_combined = _mm256_srli_epi64(adjacent_4_combined, 8);

        let adjacent_8_combined = _mm256_shuffle_epi8(
            adjacent_4_combined,
            _mm256_set_epi8(
                -1, -1, -1, -1, 13, 12, 11, 10, 9, 8, 5, 4, 3, 2, 1, 0, -1, -1, -1, -1, 13, 12, 11,
                10, 9, 8, 5, 4, 3, 2, 1, 0,
            ),
        );

        let lower_8 = _mm256_castsi256_si128(adjacent_8_combined);
        let upper_8 = _mm256_extracti128_si256(adjacent_8_combined, 1);

        _mm_storeu_si128(serialized.as_mut_ptr() as *mut __m128i, lower_8);
        _mm_storeu_si128(serialized.as_mut_ptr().offset(12) as *mut __m128i, upper_8);
    }

    serialized[0..24].try_into().unwrap()
}

#[inline(always)]
pub(crate) fn deserialize_12(v: &[u8]) -> SIMD256Vector {
    let deserialized = unsafe {
        let shift_lsbs_to_msbs = _mm256_set_epi16(
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

        let lower_coefficients = _mm_loadu_si128(v.as_ptr() as *const __m128i);
        let lower_coefficients = _mm_shuffle_epi8(
            lower_coefficients,
            _mm_set_epi8(11, 10, 10, 9, 8, 7, 7, 6, 5, 4, 4, 3, 2, 1, 1, 0),
        );
        let upper_coefficients = _mm_loadu_si128(v.as_ptr().offset(8) as *const __m128i);
        let upper_coefficients = _mm_shuffle_epi8(
            upper_coefficients,
            _mm_set_epi8(15, 14, 14, 13, 12, 11, 11, 10, 9, 8, 8, 7, 6, 5, 5, 4),
        );

        let coefficients = _mm256_castsi128_si256(lower_coefficients);
        let coefficients = _mm256_inserti128_si256(coefficients, upper_coefficients, 1);

        let coefficients = _mm256_mullo_epi16(coefficients, shift_lsbs_to_msbs);
        let coefficients = _mm256_srli_epi16(coefficients, 4);
        let coefficients = _mm256_and_si256(coefficients, _mm256_set1_epi16((1 << 12) - 1));

        coefficients
    };

    SIMD256Vector {
        elements: deserialized,
    }
}
