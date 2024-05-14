#[inline(always)]
#[cfg(target_arch = "x86")]
use core::arch::x86::*;
#[cfg(target_arch = "x86_64")]
use core::arch::x86_64::*;

use crate::{SIMD256Vector, serialize_1, deserialize_12, FIELD_MODULUS};

pub(crate) fn rejection_sample(uniform_bytes: &[u8]) -> (usize, [i16; 16]) {
    let mut sampled = [0i16; 16];

    let count = unsafe {
        let field_modulus = _mm256_set1_epi16(FIELD_MODULUS);
        let ones = _mm_set1_epi8(1);

        let potential_coefficients = deserialize_12(uniform_bytes).elements;

        let compare_with_field_modulus = _mm256_cmpgt_epi16(field_modulus, potential_coefficients);
        let good = serialize_1(SIMD256Vector {
            elements: compare_with_field_modulus,
        });

        // Write out the indices indicated by the set bits of |good| such that
        // the "good" elements can be read in sequence from the beginning of
        // |potential_coefficients|

        // Start with the first 8 bits, i.e. |good[0]|
        let byte_start_indices = _pdep_u64(good[0] as u64, 0x0101010101010101) as u128;
        let byte_start_indices = ((byte_start_indices << 8) - byte_start_indices) as u64;
        let byte_start_indices = _pext_u64(0x0E0C0A0806040200, byte_start_indices);

        let byte_shuffle_indices_first_byte = _mm_cvtsi64_si128(byte_start_indices as i64);
        let byte_shuffle_indices_second_byte = _mm_add_epi8(byte_shuffle_indices_first_byte, ones);

        let byte_shuffle_indices_low = _mm_unpacklo_epi8(
            byte_shuffle_indices_first_byte,
            byte_shuffle_indices_second_byte,
        );

        // Then the next 8 bits, i.e. |good[1]|
        let byte_start_indices = _pdep_u64(good[1] as u64, 0x0101010101010101) as u128;
        let byte_start_indices = ((byte_start_indices << 8) - byte_start_indices) as u64;
        let byte_start_indices = _pext_u64(0x0E0C0A0806040200, byte_start_indices);

        let byte_shuffle_indices_first_byte = _mm_cvtsi64_si128(byte_start_indices as i64);
        let byte_shuffle_indices_second_byte = _mm_add_epi8(byte_shuffle_indices_first_byte, ones);

        let byte_shuffle_indices_high = _mm_unpacklo_epi8(
            byte_shuffle_indices_first_byte,
            byte_shuffle_indices_second_byte,
        );

        // Write out the indices to an __m256 and then shuffle
        let byte_shuffle_indices = _mm256_castsi128_si256(byte_shuffle_indices_low);
        let byte_shuffle_indices =
            _mm256_inserti128_si256(byte_shuffle_indices, byte_shuffle_indices_high, 1);

        let coefficients = _mm256_shuffle_epi8(potential_coefficients, byte_shuffle_indices);

        // Write out the elements themselves
        let low_coefficients = _mm256_castsi256_si128(coefficients);
        _mm_storeu_si128(sampled.as_mut_ptr() as *mut __m128i, low_coefficients);
        let count_sampled = good[0].count_ones();

        let high_coefficients = _mm256_extracti128_si256(coefficients, 1);
        _mm_storeu_si128(
            sampled.as_mut_ptr().offset(count_sampled as isize) as *mut __m128i,
            high_coefficients,
        );
        let count_sampled = count_sampled + good[1].count_ones();

        count_sampled
    };

    (count as usize, sampled)
}
