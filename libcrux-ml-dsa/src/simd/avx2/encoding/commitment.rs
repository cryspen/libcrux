use libcrux_intrinsics::avx2::*;

use minicore::abstractions::{bit::Bit, bitvec::BitVec};

fn pointwise(x: BitVec<128>) -> BitVec<128> {
    macro_rules! mk_match {
        ($i:ident $x:ident $($l:literal)*) => {
            match $i {
                $($l => $x[$l],)*
                _ => unreachable!(),
            }
        }
    }
    BitVec::from_fn(|i| {
        mk_match!(i x   0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 
                        31 32 33 34 35 36 37 38 39 40 41 42 43 44 45 46 47 48 49 50 51 52 53 54 55 56 57 58
                        59 60 61 62 63 64 65 66 67 68 69 70 71 72 73 74 75 76 77 78 79 80 81 82 83 84 85 86
                        87 88 89 90 91 92 93 94 95 96 97 98 99 100 101 102 103 104 105 106 107 108 109 110 111
                        112 113 114 115 116 117 118 119 120 121 122 123 124 125 126 127)
    })
}

#[hax_lib::fstar::before(r#"
let rw (x: Minicore.Abstractions.Bitvec.t_BitVec (mk_u64 128)): Lemma (x == pointwise x) = admit ()

[@@FStar.Tactics.V2.(postprocess_with (fun () -> 
        let done = alloc false in
        ctrl_rewrite TopDown (fun _ -> if read done then (false, Skip) else (true, Continue))
                             (fun _ -> (fun () -> apply_lemma_rw (`rw); write done true)
                                       `or_else` trefl);
        norm [primops; iota; delta_namespace ["Core"; "Libcrux_ml_dsa"; "Libcrux_intrinsics"; "Minicore"; "FStar.FunctionalExtensionality"; "Rust_primitives"]; zeta_full];
        compute ();
        norm [primops; iota; delta; zeta_full]
        ))]
"#)]
fn serialize_4_aux(simd_unit: &Vec256) -> Vec128 {
    let adjacent_2_combined = mm256_sllv_epi32_u32(*simd_unit, 0, 28, 0, 28, 0, 28, 0, 28);
    let x = adjacent_2_combined;
    let adjacent_2_combined = mm256_srli_epi64::<28>(adjacent_2_combined);

    let adjacent_4_combined =
        mm256_permutevar8x32_epi32_u32(adjacent_2_combined, 0, 0, 0, 0, 6, 2, 4, 0);
    let adjacent_4_combined = mm256_castsi256_si128(adjacent_4_combined);
    mm_shuffle_epi8_u8(
        adjacent_4_combined,
        0xF0,
        0xF0,
        0xF0,
        0xF0,
        0xF0,
        0xF0,
        0xF0,
        0xF0,
        0xF0,
        0xF0,
        0xF0,
        0xF0,
        12,
        4,
        8,
        0,
    )
}

#[hax_lib::ensures(|r| {
    use hax_lib::*;
    let r = BitVec::<128>::from(r);
    let simd_unit = BitVec::<256>::from(*simd_unit);
    forall(|i: u64|
        implies(i < 32, r[i] == simd_unit[i / 4 * 32 + i % 4])
    )
})]
fn serialize_4(simd_unit: &Vec256) -> Vec128 {
    serialize_4_aux(simd_unit)
}

// mod spec {
//     use minicore::arch::x86::{extra::*, *};

//     pub fn serialize_4(simd_unit: &__m256i, out: &mut [u8]) -> __m256i {
//         let mut serialized = [0u8; 19];
//         debug_assert!(out.len() == 4);

//         let adjacent_2_combined = mm256_sllv_epi32_u32(*simd_unit, 0, 28, 0, 28, 0, 28, 0, 28);
//         let x = adjacent_2_combined;
//         let adjacent_2_combined = _mm256_srli_epi64::<28>(adjacent_2_combined);

//         let adjacent_4_combined =
//             mm256_permutevar8x32_epi32_u32(adjacent_2_combined, 0, 0, 0, 0, 6, 2, 4, 0);
//         let adjacent_4_combined = _mm256_castsi256_si128(adjacent_4_combined);
//         let adjacent_4_combined = mm_shuffle_epi8_u8(
//             adjacent_4_combined,
//             0xF0,
//             0xF0,
//             0xF0,
//             0xF0,
//             0xF0,
//             0xF0,
//             0xF0,
//             0xF0,
//             0xF0,
//             0xF0,
//             0xF0,
//             0xF0,
//             12,
//             4,
//             8,
//             0,
//         );

//         mm_storeu_bytes_si128(&mut serialized[0..16], adjacent_4_combined);

//         out.copy_from_slice(&serialized[0..4]);

//         x
//     }
// }

// #[test]
// fn test_4() {
//     use minicore::abstractions::bitvec::BitVec;
//     for _ in 0..1000 {
//         let vector: BitVec<256> = BitVec::rand();
//         let mut out_l = [0u8; 4];
//         let mut out_r = [0u8; 4];
//         let l = serialize_4(&vector.into(), &mut out_l);
//         let r = spec::serialize_4(&vector, &mut out_r);
//         assert_eq!(BitVec::from(l), r);
//         assert_eq!(out_l, out_r);
//     }
// }

#[inline(always)]
pub(in crate::simd::avx2) fn serialize(simd_unit: &Vec256, out: &mut [u8]) {
    let mut serialized = [0u8; 19];

    match out.len() as u8 {
        4 => {
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
                    0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 12, 4,
                    8, 0,
                ),
            );

            mm_storeu_bytes_si128(&mut serialized[0..16], adjacent_4_combined);

            out.copy_from_slice(&serialized[0..4]);
        }

        6 => {
            let adjacent_2_combined =
                mm256_sllv_epi32(*simd_unit, mm256_set_epi32(0, 26, 0, 26, 0, 26, 0, 26));
            let adjacent_2_combined = mm256_srli_epi64::<26>(adjacent_2_combined);

            let adjacent_3_combined = mm256_shuffle_epi8(
                adjacent_2_combined,
                mm256_set_epi8(
                    -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, 9, 8, 1, 0, -1, -1, -1, -1, -1,
                    -1, -1, -1, -1, -1, -1, -1, 9, 8, 1, 0,
                ),
            );

            let adjacent_3_combined = mm256_mullo_epi16(
                adjacent_3_combined,
                mm256_set_epi16(1, 1, 1, 1, 1, 1, 1, 1 << 4, 1, 1, 1, 1, 1, 1, 1, 1 << 4),
            );
            let adjacent_3_combined =
                mm256_srlv_epi32(adjacent_3_combined, mm256_set_epi32(0, 0, 0, 4, 0, 0, 0, 4));

            // We now have 24 bits starting at position 0 in the lower 128-bit lane, ...
            let lower_3 = mm256_castsi256_si128(adjacent_3_combined);
            mm_storeu_bytes_si128(&mut serialized[0..16], lower_3);

            // and 24 bits starting at position 0 in the upper 128-bit lane.
            let upper_3 = mm256_extracti128_si256::<1>(adjacent_3_combined);
            mm_storeu_bytes_si128(&mut serialized[3..19], upper_3);

            out.copy_from_slice(&serialized[0..6]);
        }

        _ => unreachable!(),
    }
}
