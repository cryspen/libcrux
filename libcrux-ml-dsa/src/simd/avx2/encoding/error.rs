use libcrux_intrinsics::avx2::*;

use crate::simd::avx2::Eta;

#[inline(always)]
#[hax_lib::fstar::before("open Spec.Intrinsics")]
#[hax_lib::fstar::options(
    "--fuel 0 --ifuel 0 --z3rlimit 5000 --z3smtopt '(set-option :smt.arith.nl false)'"
)]
#[hax_lib::requires(
    fstar!(r"forall (i: nat {i < 256}). i % 32 >= 3 ==> ${simd_unit_shifted}.(mk_int i) == Core_models.Abstractions.Bit.Bit_Zero")
)]
#[hax_lib::ensures(|result| {
    fstar!(r"forall (i:nat{i < 24}). ${result}.(mk_int i) == ${simd_unit_shifted}.(mk_int ((i / 3) * 32 + i % 3))")
})]
fn serialize_when_eta_is_2_aux(simd_unit_shifted: Vec256) -> Vec128 {
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

    adjacent_6_combined
}

#[inline(always)]
#[hax_lib::requires(fstar!("forall i. let x = (2 - v (to_i32x8 simd_unit i)) in x >= 0 && x <= 7"))]
fn serialize_when_eta_is_2(simd_unit: &Vec256, out: &mut [u8]) {
    let mut serialized = [0u8; 16];

    const ETA: i32 = 2;
    let simd_unit_shifted = mm256_sub_epi32(mm256_set1_epi32(ETA), *simd_unit);

    hax_lib::fstar!("i32_lt_pow2_n_to_bit_zero_lemma 3 $simd_unit_shifted");
    let adjacent_6_combined = serialize_when_eta_is_2_aux(simd_unit_shifted);

    mm_storeu_bytes_si128(&mut serialized[0..16], adjacent_6_combined);
    out.copy_from_slice(&serialized[0..3]);
}

#[inline(always)]
#[hax_lib::fstar::options(
    "--fuel 0 --ifuel 0 --z3rlimit 5000 --z3smtopt '(set-option :smt.arith.nl false)'"
)]
#[hax_lib::requires(
    fstar!(r"forall (i: nat {i < 256}). i % 32 >= 4 ==> ${simd_unit_shifted}.(mk_int i) == Core_models.Abstractions.Bit.Bit_Zero")
)]
#[hax_lib::ensures(|result| {
    fstar!(r"forall (i:nat{i < 32}). ${result}.(mk_int i) == ${simd_unit_shifted}.(mk_int ((i / 4) * 32 + i % 4))")
})]
fn serialize_when_eta_is_4_aux(simd_unit_shifted: Vec256) -> Vec128 {
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

    adjacent_4_combined
}

#[hax_lib::requires(fstar!("forall i. let x = (4 - v (to_i32x8 simd_unit i)) in x >= 0 && x <= 15"))]
#[inline(always)]
fn serialize_when_eta_is_4(simd_unit: &Vec256, out: &mut [u8]) {
    let mut serialized = [0u8; 16];

    const ETA: i32 = 4;
    let simd_unit_shifted = mm256_sub_epi32(mm256_set1_epi32(ETA), *simd_unit);

    hax_lib::fstar!("i32_lt_pow2_n_to_bit_zero_lemma 4 $simd_unit_shifted");
    let adjacent_4_combined = serialize_when_eta_is_4_aux(simd_unit_shifted);

    mm_storeu_bytes_si128(&mut serialized[0..16], adjacent_4_combined);

    out.copy_from_slice(&serialized[0..4])
}

#[hax_lib::requires(
    fstar!("forall i. let x = (v (${eta as u8}) - v (to_i32x8 simd_unit i)) in x >= 0 && x <= (pow2 (v (${eta as u8})) - 1)")
)]
#[inline(always)]
pub fn serialize(eta: Eta, simd_unit: &Vec256, serialized: &mut [u8]) {
    // [eurydice] injects an unused variable here in the C code for some reason.
    match eta {
        Eta::Two => serialize_when_eta_is_2(simd_unit, serialized),
        Eta::Four => serialize_when_eta_is_4(simd_unit, serialized),
    }
}

// #[hax_lib::ensures(|result| {
//     fstar!(r#"
// forall (i:nat{i < 24}).
//      ${result}.(mk_int i)
//   == get_bit (Seq.index ${bytes} (i / 3)) (mk_int (i % 8))
// "#)
// })]
// #[hax_lib::fstar::options(
//     "--fuel 0 --ifuel 0 --z3rlimit 500 --z3smtopt '(set-option :smt.arith.nl false)'"
// )]

#[inline(always)]
#[hax_lib::requires(bytes.len() == 3)]
#[hax_lib::ensures(|result| fstar!(r#"
  (forall (i: nat {i <  24}). u8_to_bv bytes.[mk_usize (i / 8)] (mk_int (i % 8)) == ${result}.(mk_int (i / 3 * 32 + i % 3)))
/\ (forall (i: nat {i < 256}). i % 32 >= 3 ==> Core_models.Abstractions.Bit.Bit_Zero? ${result}.(mk_int i))
"#))]
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
#[hax_lib::requires(bytes.len() == 4)]
#[hax_lib::ensures(|result| fstar!(r#"
  (forall (i: nat {i <  32}). u8_to_bv bytes.[mk_usize (i / 8)] (mk_int (i % 8)) == ${result}.(mk_int (i / 4 * 32 + i % 4)))
/\ (forall (i: nat {i < 256}). i % 32 >= 4 ==> Core_models.Abstractions.Bit.Bit_Zero? ${result}.(mk_int i))
"#))]
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
#[hax_lib::requires(serialized.len() == match eta {
    Eta::Two => 3,
    Eta::Four => 4,
})]
pub(crate) fn deserialize_to_unsigned(eta: Eta, serialized: &[u8]) -> Vec256 {
    match eta {
        Eta::Two => deserialize_to_unsigned_when_eta_is_2(serialized),
        Eta::Four => deserialize_to_unsigned_when_eta_is_4(serialized),
    }
}

#[inline(always)]
#[hax_lib::requires(serialized.len() == match eta {
    Eta::Two => 3,
    Eta::Four => 4,
})]
pub(crate) fn deserialize(eta: Eta, serialized: &[u8], out: &mut Vec256) {
    let unsigned = deserialize_to_unsigned(eta, serialized);

    // [eurydice]: https://github.com/AeneasVerif/eurydice/issues/122
    let eta = match eta {
        Eta::Two => 2,
        Eta::Four => 4,
    };
    *out = mm256_sub_epi32(mm256_set1_epi32(eta), unsigned);
}
