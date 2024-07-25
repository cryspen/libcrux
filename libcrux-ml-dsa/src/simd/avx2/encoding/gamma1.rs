use libcrux_intrinsics::avx2::*;

#[inline(always)]
fn serialize_when_gamma1_is_2_pow_17<const OUTPUT_SIZE: usize>(
    simd_unit: Vec256,
) -> [u8; OUTPUT_SIZE] {
    const GAMMA1: i32 = 1 << 17;

    // TODO: The official reference code does not vectorize this (see
    // https://github.com/pq-crystals/dilithium/blob/master/avx2/poly.c#L962)
    // so for the moment we'll just write out the coefficients to array and serialize
    // it the way we'd do so without AVX2 instructions. After we're done vectorizing
    // everything else, we can circle back to this and take a shot at this too.
    let mut coefficients = [0i32; 8];
    mm256_storeu_si256_i32(&mut coefficients, simd_unit);

    let mut serialized = [0u8; OUTPUT_SIZE];

    for (i, coefficients) in coefficients.chunks_exact(4).enumerate() {
        let coefficient0 = GAMMA1 - coefficients[0];
        let coefficient1 = GAMMA1 - coefficients[1];
        let coefficient2 = GAMMA1 - coefficients[2];
        let coefficient3 = GAMMA1 - coefficients[3];

        serialized[9 * i] = coefficient0 as u8;
        serialized[9 * i + 1] = (coefficient0 >> 8) as u8;

        serialized[9 * i + 2] = (coefficient0 >> 16) as u8;
        serialized[9 * i + 2] |= (coefficient1 << 2) as u8;

        serialized[9 * i + 3] = (coefficient1 >> 6) as u8;

        serialized[9 * i + 4] = (coefficient1 >> 14) as u8;
        serialized[9 * i + 4] |= (coefficient2 << 4) as u8;

        serialized[9 * i + 5] = (coefficient2 >> 4) as u8;

        serialized[9 * i + 6] = (coefficient2 >> 12) as u8;
        serialized[9 * i + 6] |= (coefficient3 << 6) as u8;

        serialized[9 * i + 7] = (coefficient3 >> 2) as u8;
        serialized[9 * i + 8] = (coefficient3 >> 10) as u8;
    }

    serialized
}

#[inline(always)]
fn serialize_when_gamma1_is_2_pow_19<const OUTPUT_SIZE: usize>(
    simd_unit: Vec256,
) -> [u8; OUTPUT_SIZE] {
    let mut serialized = [0u8; 32];

    const GAMMA1: i32 = 1 << 19;
    let simd_unit_shifted = mm256_sub_epi32(mm256_set1_epi32(GAMMA1), simd_unit);

    let adjacent_2_combined = mm256_sllv_epi32(
        simd_unit_shifted,
        mm256_set_epi32(0, 12, 0, 12, 0, 12, 0, 12),
    );
    let adjacent_2_combined = mm256_srli_epi64::<12>(adjacent_2_combined);

    let adjacent_4_combined = mm256_shuffle_epi8(
        adjacent_2_combined,
        mm256_set_epi8(
            -1, -1, -1, -1, -1, -1, 12, 11, 10, 9, 8, 4, 3, 2, 1, 0, -1, -1, -1, -1, -1, -1, 12,
            11, 10, 9, 8, 4, 3, 2, 1, 0,
        ),
    );

    // We now have 80 bits starting at position 0 in the lower 128-bit lane, ...
    let lower_4 = mm256_castsi256_si128(adjacent_4_combined);
    mm_storeu_bytes_si128(&mut serialized[0..16], lower_4);

    // ... and the second 80 bits at position 0 in the upper 128-bit lane
    let upper_4 = mm256_extracti128_si256::<1>(adjacent_4_combined);
    mm_storeu_bytes_si128(&mut serialized[10..26], upper_4);

    serialized[0..20].try_into().unwrap()
}

#[inline(always)]
pub fn serialize<const OUTPUT_SIZE: usize>(simd_unit: Vec256) -> [u8; OUTPUT_SIZE] {
    match OUTPUT_SIZE {
        18 => serialize_when_gamma1_is_2_pow_17::<OUTPUT_SIZE>(simd_unit),
        20 => serialize_when_gamma1_is_2_pow_19::<OUTPUT_SIZE>(simd_unit),
        _ => unreachable!(),
    }
}
