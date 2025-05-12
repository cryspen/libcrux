use libcrux_intrinsics::avx2::*;

#[cfg(hax)]
use minicore::abstractions::{
    bit::Bit,
    bitvec::{bitvec_postprocess_norm, BitVec},
};

#[hax_lib::ensures(|(lower, upper)| {
    use hax_lib::*;
    let lower = BitVec::<128>::from(lower);
    let upper = BitVec::<128>::from(upper);
    let simd_unit = BitVec::<256>::from(*simd_unit);
    forall(|i: u64|
        implies(i < 48, if i < 24 {lower[i]} else { upper[i - 24] } == simd_unit[i / 6 * 32 + i % 6])
    )
})]
#[inline(always)]
fn serialize_6(simd_unit: &Vec256) -> (Vec128, Vec128) {
    #[hax_lib::fstar::before(r#"[@@FStar.Tactics.postprocess_with ${bitvec_postprocess_norm}]"#)]
    #[inline(always)]
    fn normalized_serialize_6(simd_unit: &Vec256) -> (Vec128, Vec128) {
        let adjacent_2_combined =
            mm256_sllv_epi32(*simd_unit, mm256_set_epi32(0, 26, 0, 26, 0, 26, 0, 26));
        let adjacent_2_combined = mm256_srli_epi64::<26>(adjacent_2_combined);

        let adjacent_3_combined = mm256_shuffle_epi8(
            adjacent_2_combined,
            mm256_set_epi8(
                -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, 9, 8, 1, 0, -1, -1, -1, -1, -1, -1,
                -1, -1, -1, -1, -1, -1, 9, 8, 1, 0,
            ),
        );

        let adjacent_3_combined = mm256_mullo_epi16(
            adjacent_3_combined,
            // Note: the explicit style `1i16 << N` matters for F* proofs here.
            mm256_set_epi16(
                1i16 << 0,
                1i16 << 0,
                1i16 << 0,
                1i16 << 0,
                1i16 << 0,
                1i16 << 0,
                1i16 << 0,
                1i16 << 4,
                1i16 << 0,
                1i16 << 0,
                1i16 << 0,
                1i16 << 0,
                1i16 << 0,
                1i16 << 0,
                1i16 << 0,
                1i16 << 4,
            ),
        );
        let adjacent_3_combined =
            mm256_srlv_epi32(adjacent_3_combined, mm256_set_epi32(0, 0, 0, 4, 0, 0, 0, 4));

        // We now have 24 bits starting at position 0 in the lower 128-bit lane, ...
        let lower = mm256_castsi256_si128(adjacent_3_combined);
        // and 24 bits starting at position 0 in the upper 128-bit lane.
        let upper = mm256_extracti128_si256::<1>(adjacent_3_combined);

        (lower, upper)
    }
    normalized_serialize_6(simd_unit)
}

#[hax_lib::ensures(|r| {
    use hax_lib::*;
    let r = BitVec::<128>::from(r);
    let simd_unit = BitVec::<256>::from(*simd_unit);
    forall(|i: u64|
        implies(i < 32, r[i] == simd_unit[i / 4 * 32 + i % 4])
    )
})]
#[inline(always)]
fn serialize_4(simd_unit: &Vec256) -> Vec128 {
    // The F* annotation normalizes the body of the function. After normalization, this function is a simple permutation of bits.
    #[hax_lib::fstar::before(r#"[@@FStar.Tactics.postprocess_with ${bitvec_postprocess_norm}]"#)]
    #[inline(always)]
    fn normalized_serialize_4(simd_unit: &Vec256) -> Vec128 {
        let adjacent_2_combined =
            mm256_sllv_epi32(*simd_unit, mm256_set_epi32(0, 28, 0, 28, 0, 28, 0, 28));
        let adjacent_2_combined = mm256_srli_epi64::<28>(adjacent_2_combined);

        let adjacent_4_combined = mm256_permutevar8x32_epi32(
            adjacent_2_combined,
            mm256_set_epi32(0, 0, 0, 0, 6, 2, 4, 0),
        );
        let adjacent_4_combined = mm256_castsi256_si128(adjacent_4_combined);
        let adjacent_4_combined = mm_shuffle_epi8(
            adjacent_4_combined,
            mm_set_epi8(
                0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 12, 4, 8, 0,
            ),
        );
        adjacent_4_combined
    }
    normalized_serialize_4(simd_unit)
}

#[inline(always)]
#[hax_lib::requires(out.len() == 4 || out.len() == 6)]
pub(in crate::simd::avx2) fn serialize(simd_unit: &Vec256, out: &mut [u8]) {
    let mut serialized = [0u8; 19];

    match out.len() as u8 {
        4 => {
            mm_storeu_bytes_si128(&mut serialized[0..16], serialize_4(simd_unit));
            out.copy_from_slice(&serialized[0..4]);
        }

        6 => {
            let (lower_3, upper_3) = serialize_6(simd_unit);

            mm_storeu_bytes_si128(&mut serialized[0..16], lower_3);
            mm_storeu_bytes_si128(&mut serialized[3..19], upper_3);

            out.copy_from_slice(&serialized[0..6]);
        }

        _ => unreachable!(),
    }
}
