//! A (partial) Rust-based model of [`core::arch::x86`] and [`core::arch::x86_64`].
//!
//! This module provides a purely Rust implementation of selected operations from
//! `core::arch::x86` and `core::arch::x86_64`.

use crate::abstractions::{bit::*, bitvec::*, funarr::*};

pub(crate) mod upstream {
    #[cfg(target_arch = "x86")]
    pub use core::arch::x86::*;
    #[cfg(target_arch = "x86_64")]
    pub use core::arch::x86_64::*;
}

/// Conversions impls between `BitVec<N>` and `__mNi` types.
#[cfg(not(hax))]
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
mod conversions {
    use super::upstream::{
        __m128i, __m256i, _mm256_loadu_si256, _mm256_storeu_si256, _mm_loadu_si128,
        _mm_storeu_si128,
    };
    use super::BitVec;

    impl From<BitVec<256>> for __m256i {
        fn from(bv: BitVec<256>) -> __m256i {
            let bv: &[u8] = &bv.to_vec()[..];
            unsafe { _mm256_loadu_si256(bv.as_ptr() as *const _) }
        }
    }

    impl From<BitVec<128>> for __m128i {
        fn from(bv: BitVec<128>) -> __m128i {
            let slice: &[u8] = &bv.to_vec()[..];
            unsafe { _mm_loadu_si128(slice.as_ptr() as *const __m128i) }
        }
    }

    impl From<__m256i> for BitVec<256> {
        fn from(vec: __m256i) -> BitVec<256> {
            let mut v = [0u8; 32];
            unsafe {
                _mm256_storeu_si256(v.as_mut_ptr() as *mut _, vec);
            }
            BitVec::from_slice(&v[..], 8)
        }
    }

    impl From<__m128i> for BitVec<128> {
        fn from(vec: __m128i) -> BitVec<128> {
            let mut v = [0u8; 16];
            unsafe {
                _mm_storeu_si128(v.as_mut_ptr() as *mut _, vec);
            }
            BitVec::from_slice(&v[..], 8)
        }
    }
}

/// 256-bit wide integer vector type.
/// Models `core::arch::x86::__m256i` or `core::arch::x86_64::__m256i` (the __m256i type defined by Intel, representing a 256-bit SIMD register).
#[allow(non_camel_case_types)]
pub type __m256i = BitVec<256>;

/// 128-bit wide integer vector type.
/// Models `core::arch::x86::__m128i` or `core::arch::x86_64::__m128i` (the __m128i type defined by Intel, representing a 128-bit SIMD register).
#[allow(non_camel_case_types)]
pub type __m128i = BitVec<128>;

#[hax_lib::exclude]
pub fn _mm_storeu_si128(output: *mut __m128i, a: __m128i) {
    // This is equivalent to `*output = a`
    let mut out = [0u8; 128];
    extra::mm_storeu_bytes_si128(&mut out, a);
    unsafe {
        *(output.as_mut().unwrap()) = BitVec::from_slice(&mut out, 8);
    }
}

#[hax_lib::requires(SHIFT_BY >= 0 && SHIFT_BY < 16)]
pub fn _mm256_slli_epi16<const SHIFT_BY: i32>(vector: __m256i) -> __m256i {
    #[cfg(not(hax))]
    debug_assert!(SHIFT_BY >= 0 && SHIFT_BY < 16);
    BitVec::from_fn(|i| {
        let nth_bit = i % 16;
        let shift = SHIFT_BY as u64;
        if nth_bit >= shift {
            vector[i - shift]
        } else {
            Bit::Zero
        }
    })
}

#[hax_lib::requires(SHIFT_BY >= 0 && SHIFT_BY < 64)]
pub fn _mm256_srli_epi64<const SHIFT_BY: i32>(vector: __m256i) -> __m256i {
    #[cfg(not(hax))]
    debug_assert!(SHIFT_BY >= 0 && SHIFT_BY < 64);
    BitVec::from_fn(|i| {
        let nth_bit = i % 64;
        let shift = SHIFT_BY as u64;
        if nth_bit < 64 - shift {
            vector[i + shift]
        } else {
            Bit::Zero
        }
    })
}

#[hax_lib::exclude]
pub fn _mm256_sllv_epi32(vector: __m256i, counts: __m256i) -> __m256i {
    // extra::mm256_sllv_epi32_u32_array(vector, counts.to_vec().try_into().unwrap())
    todo!()
}

#[hax_lib::exclude]
pub fn _mm256_permutevar8x32_epi32(a: __m256i, b: __m256i) -> __m256i {
    // extra::mm256_permutevar8x32_epi32_u32_array(a, b.to_vec().try_into().unwrap())
    todo!()
}

pub fn _mm256_castsi256_si128(vector: __m256i) -> __m128i {
    BitVec::from_fn(|i| vector[i])
}

#[hax_lib::exclude]
pub fn _mm_shuffle_epi8(vector: __m128i, indexes: __m128i) -> __m128i {
    // let indexes: [u8; 16] = indexes.to_vec().try_into().unwrap();
    // extra::mm_shuffle_epi8_u8_array(vector, indexes)
    todo!()
}

use hax_lib::implies;

#[hax_lib::fstar::replace(
    "
    assume val b: nat -> $:{Bit}
    let bb (i: u64) = b (v i)
"
)]
fn bb(i: u64) -> Bit {
    todo!()
}

fn hey() {
    let x0 = proveme(&BitVec::from_fn(|i| bb(i)))[0];
    let x1 = proveme(&BitVec::from_fn(|i| bb(i)))[1];
    let x2 = proveme(&BitVec::from_fn(|i| bb(i)))[2];
    let x3 = proveme(&BitVec::from_fn(|i| bb(i)))[3];
    let x4 = proveme(&BitVec::from_fn(|i| bb(i)))[4];
    let x5 = proveme(&BitVec::from_fn(|i| bb(i)))[5];
    let x6 = proveme(&BitVec::from_fn(|i| bb(i)))[6];
    let x7 = proveme(&BitVec::from_fn(|i| bb(i)))[7];
    let x8 = proveme(&BitVec::from_fn(|i| bb(i)))[8];
    let x9 = proveme(&BitVec::from_fn(|i| bb(i)))[9];
    let x10 = proveme(&BitVec::from_fn(|i| bb(i)))[10];
    let x11 = proveme(&BitVec::from_fn(|i| bb(i)))[11];
    let x12 = proveme(&BitVec::from_fn(|i| bb(i)))[12];
    let x13 = proveme(&BitVec::from_fn(|i| bb(i)))[13];
    let x14 = proveme(&BitVec::from_fn(|i| bb(i)))[14];
    let x15 = proveme(&BitVec::from_fn(|i| bb(i)))[15];
    let x16 = proveme(&BitVec::from_fn(|i| bb(i)))[16];
    let x17 = proveme(&BitVec::from_fn(|i| bb(i)))[17];
    let x18 = proveme(&BitVec::from_fn(|i| bb(i)))[18];
    let x19 = proveme(&BitVec::from_fn(|i| bb(i)))[19];
    let x20 = proveme(&BitVec::from_fn(|i| bb(i)))[20];
    let x21 = proveme(&BitVec::from_fn(|i| bb(i)))[21];
    let x22 = proveme(&BitVec::from_fn(|i| bb(i)))[22];
    let x23 = proveme(&BitVec::from_fn(|i| bb(i)))[23];
    let x24 = proveme(&BitVec::from_fn(|i| bb(i)))[24];
    let x25 = proveme(&BitVec::from_fn(|i| bb(i)))[25];
    let x26 = proveme(&BitVec::from_fn(|i| bb(i)))[26];
    let x27 = proveme(&BitVec::from_fn(|i| bb(i)))[27];
    let x28 = proveme(&BitVec::from_fn(|i| bb(i)))[28];
    let x29 = proveme(&BitVec::from_fn(|i| bb(i)))[29];
    let x30 = proveme(&BitVec::from_fn(|i| bb(i)))[30];
    let x31 = proveme(&BitVec::from_fn(|i| bb(i)))[31];
    let x32 = proveme(&BitVec::from_fn(|i| bb(i)))[32];
    let x33 = proveme(&BitVec::from_fn(|i| bb(i)))[33];
    let x34 = proveme(&BitVec::from_fn(|i| bb(i)))[34];
    let x35 = proveme(&BitVec::from_fn(|i| bb(i)))[35];
    let x36 = proveme(&BitVec::from_fn(|i| bb(i)))[36];
    let x37 = proveme(&BitVec::from_fn(|i| bb(i)))[37];
    let x38 = proveme(&BitVec::from_fn(|i| bb(i)))[38];
    let x39 = proveme(&BitVec::from_fn(|i| bb(i)))[39];
    let x40 = proveme(&BitVec::from_fn(|i| bb(i)))[40];
    let x41 = proveme(&BitVec::from_fn(|i| bb(i)))[41];
    let x42 = proveme(&BitVec::from_fn(|i| bb(i)))[42];
    let x43 = proveme(&BitVec::from_fn(|i| bb(i)))[43];
    let x44 = proveme(&BitVec::from_fn(|i| bb(i)))[44];
    let x45 = proveme(&BitVec::from_fn(|i| bb(i)))[45];
    let x46 = proveme(&BitVec::from_fn(|i| bb(i)))[46];
    let x47 = proveme(&BitVec::from_fn(|i| bb(i)))[47];
    let x48 = proveme(&BitVec::from_fn(|i| bb(i)))[48];
    let x49 = proveme(&BitVec::from_fn(|i| bb(i)))[49];
    let x50 = proveme(&BitVec::from_fn(|i| bb(i)))[50];
    let x51 = proveme(&BitVec::from_fn(|i| bb(i)))[51];
    let x52 = proveme(&BitVec::from_fn(|i| bb(i)))[52];
    let x53 = proveme(&BitVec::from_fn(|i| bb(i)))[53];
    let x54 = proveme(&BitVec::from_fn(|i| bb(i)))[54];
    let x55 = proveme(&BitVec::from_fn(|i| bb(i)))[55];
    let x56 = proveme(&BitVec::from_fn(|i| bb(i)))[56];
    let x57 = proveme(&BitVec::from_fn(|i| bb(i)))[57];
    let x58 = proveme(&BitVec::from_fn(|i| bb(i)))[58];
    let x59 = proveme(&BitVec::from_fn(|i| bb(i)))[59];
    let x60 = proveme(&BitVec::from_fn(|i| bb(i)))[60];
    let x61 = proveme(&BitVec::from_fn(|i| bb(i)))[61];
    let x62 = proveme(&BitVec::from_fn(|i| bb(i)))[62];
    let x63 = proveme(&BitVec::from_fn(|i| bb(i)))[63];
    let x64 = proveme(&BitVec::from_fn(|i| bb(i)))[64];
    let x65 = proveme(&BitVec::from_fn(|i| bb(i)))[65];
    let x66 = proveme(&BitVec::from_fn(|i| bb(i)))[66];
    let x67 = proveme(&BitVec::from_fn(|i| bb(i)))[67];
    let x68 = proveme(&BitVec::from_fn(|i| bb(i)))[68];
    let x69 = proveme(&BitVec::from_fn(|i| bb(i)))[69];
    let x70 = proveme(&BitVec::from_fn(|i| bb(i)))[70];
    let x71 = proveme(&BitVec::from_fn(|i| bb(i)))[71];
    let x72 = proveme(&BitVec::from_fn(|i| bb(i)))[72];
    let x73 = proveme(&BitVec::from_fn(|i| bb(i)))[73];
    let x74 = proveme(&BitVec::from_fn(|i| bb(i)))[74];
    let x75 = proveme(&BitVec::from_fn(|i| bb(i)))[75];
    let x76 = proveme(&BitVec::from_fn(|i| bb(i)))[76];
    let x77 = proveme(&BitVec::from_fn(|i| bb(i)))[77];
    let x78 = proveme(&BitVec::from_fn(|i| bb(i)))[78];
    let x79 = proveme(&BitVec::from_fn(|i| bb(i)))[79];
    let x80 = proveme(&BitVec::from_fn(|i| bb(i)))[80];
    let x81 = proveme(&BitVec::from_fn(|i| bb(i)))[81];
    let x82 = proveme(&BitVec::from_fn(|i| bb(i)))[82];
    let x83 = proveme(&BitVec::from_fn(|i| bb(i)))[83];
    let x84 = proveme(&BitVec::from_fn(|i| bb(i)))[84];
    let x85 = proveme(&BitVec::from_fn(|i| bb(i)))[85];
    let x86 = proveme(&BitVec::from_fn(|i| bb(i)))[86];
    let x87 = proveme(&BitVec::from_fn(|i| bb(i)))[87];
    let x88 = proveme(&BitVec::from_fn(|i| bb(i)))[88];
    let x89 = proveme(&BitVec::from_fn(|i| bb(i)))[89];
    let x90 = proveme(&BitVec::from_fn(|i| bb(i)))[90];
    let x91 = proveme(&BitVec::from_fn(|i| bb(i)))[91];
    let x92 = proveme(&BitVec::from_fn(|i| bb(i)))[92];
    let x93 = proveme(&BitVec::from_fn(|i| bb(i)))[93];
    let x94 = proveme(&BitVec::from_fn(|i| bb(i)))[94];
    let x95 = proveme(&BitVec::from_fn(|i| bb(i)))[95];
    let x96 = proveme(&BitVec::from_fn(|i| bb(i)))[96];
    let x97 = proveme(&BitVec::from_fn(|i| bb(i)))[97];
    let x98 = proveme(&BitVec::from_fn(|i| bb(i)))[98];
    let x99 = proveme(&BitVec::from_fn(|i| bb(i)))[99];
    let x100 = proveme(&BitVec::from_fn(|i| bb(i)))[100];
    let x101 = proveme(&BitVec::from_fn(|i| bb(i)))[101];
    let x102 = proveme(&BitVec::from_fn(|i| bb(i)))[102];
    let x103 = proveme(&BitVec::from_fn(|i| bb(i)))[103];
    let x104 = proveme(&BitVec::from_fn(|i| bb(i)))[104];
    let x105 = proveme(&BitVec::from_fn(|i| bb(i)))[105];
    let x106 = proveme(&BitVec::from_fn(|i| bb(i)))[106];
    let x107 = proveme(&BitVec::from_fn(|i| bb(i)))[107];
    let x108 = proveme(&BitVec::from_fn(|i| bb(i)))[108];
    let x109 = proveme(&BitVec::from_fn(|i| bb(i)))[109];
    let x110 = proveme(&BitVec::from_fn(|i| bb(i)))[110];
    let x111 = proveme(&BitVec::from_fn(|i| bb(i)))[111];
    let x112 = proveme(&BitVec::from_fn(|i| bb(i)))[112];
    let x113 = proveme(&BitVec::from_fn(|i| bb(i)))[113];
    let x114 = proveme(&BitVec::from_fn(|i| bb(i)))[114];
    let x115 = proveme(&BitVec::from_fn(|i| bb(i)))[115];
    let x116 = proveme(&BitVec::from_fn(|i| bb(i)))[116];
    let x117 = proveme(&BitVec::from_fn(|i| bb(i)))[117];
    let x118 = proveme(&BitVec::from_fn(|i| bb(i)))[118];
    let x119 = proveme(&BitVec::from_fn(|i| bb(i)))[119];
    let x120 = proveme(&BitVec::from_fn(|i| bb(i)))[120];
    let x121 = proveme(&BitVec::from_fn(|i| bb(i)))[121];
    let x122 = proveme(&BitVec::from_fn(|i| bb(i)))[122];
    let x123 = proveme(&BitVec::from_fn(|i| bb(i)))[123];
    let x124 = proveme(&BitVec::from_fn(|i| bb(i)))[124];
    let x125 = proveme(&BitVec::from_fn(|i| bb(i)))[125];
    let x126 = proveme(&BitVec::from_fn(|i| bb(i)))[126];
    let x127 = proveme(&BitVec::from_fn(|i| bb(i)))[127];

    hax_lib::fstar!(
        r#"
    
    let open FStar.Tactics in
    assert (
        [x0;x1;x2;x3;x4;x5;x6;x7;x8;x9;x10;x11;x12;x13;x14;x15;x16;x17;x18;x19;x20;x21;x22;x23;x24;x25;x26;x27;x28;x29;x30;x31;x32;x33;x34;x35;x36;x37;x38;x39;x40;x41;x42;x43;x44;x45;x46;x47;x48;x49;x50;x51;x52;x53;x54;x55;x56;x57;x58;x59;x60;x61;x62;x63;x64;x65;x66;x67;x68;x69;x70;x71;x72;x73;x74;x75;x76;x77;x78;x79;x80;x81;x82;x83;x84;x85;x86;x87;x88;x89;x90;x91;x92;x93;x94;x95;x96;x97;x98;x99;x100;x101;x102;x103;x104;x105;x106;x107;x108;x109;x110;x111;x112;x113;x114;x115;x116;x117;x118;x119;x120;x121;x122;x123;x124;x125;x126;x127] == magic ()
    ) by (
        norm [primops; iota; delta_namespace ["Core"; "Minicore"; "FStar.FunctionalExtensionality"; "Rust_primitives"]; zeta_full];
        compute ();
        norm [primops; iota; delta; zeta_full];
        fail "x"
    )
    "#
    )
}

// #[hax_lib::fstar::options("--ext context_pruning --split_queries always")]
#[hax_lib::requires(hax_lib::forall(|i: u64| implies(i < 256, i % 16 > 4 || (simd_unit[i] == Bit::Zero))))]
// #[hax_lib::ensures(|r|hax_lib::forall(|i: usize| implies(i < 4, r[i] == simd_unit[i])))]
// #[hax_lib::ensures(|r|
//     hax_lib::forall(|i: usize| i % 16 > 4 || (simd_unit[i] == Bit::Zero))
// )]
// #[hax_lib::requires(
//     fstar!(
//         r#"forall (i: nat{i < 256}). i % 16 < 4 || $simd_unit (mk_usize i) = ${Bit::Zero}"#
//     )
// )]
// #[hax_lib::ensures(|r| fstar!(r#"forall (i: nat{i < 64}). $r (mk_usize i) == $simd_unit (mk_usize ((i/4) * 16 + i%4))"#))]
#[inline(always)]
fn proveme(simd_unit: &__m256i) -> __m128i {
    // let mut serialized = [0u8; 19];
    let adjacent_2_combined = extra::mm256_sllv_epi32_u32(*simd_unit, 0, 28, 0, 28, 0, 28, 0, 28);
    let adjacent_2_combined = _mm256_srli_epi64::<28>(adjacent_2_combined);

    let adjacent_4_combined =
        extra::mm256_permutevar8x32_epi32_u32(adjacent_2_combined, 0, 0, 0, 0, 6, 2, 4, 0);
    let adjacent_4_combined = _mm256_castsi256_si128(adjacent_4_combined);
    let adjacent_4_combined = extra::mm_shuffle_epi8_u8(
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
    );
    adjacent_4_combined

    // mm_storeu_bytes_si128(&mut serialized[0..16], adjacent_4_combined);

    // out.copy_from_slice(&serialized[0..4]);
}

pub mod extra {
    use super::*;

    // #[hax_lib::fstar::before(
    //     r#"let bit_and_lt (t: uinttype) n x: Lemma (v (x &. mk_int #t n) < n) [SMTPat (x &. mk_int #t n)] = admit ()"#
    // )]
    pub fn mm256_sllv_epi32_u32_array(
        vector: BitVec<256>,
        counts: FunArray<8, u32>,
    ) -> BitVec<256> {
        BitVec::from_fn(|i| {
            let nth_bit = i % 32;
            let shift = counts[i / 32];
            if nth_bit as i128 >= shift as i128 {
                vector[i - shift as u64]
            } else {
                Bit::Zero
            }
        })
    }

    pub fn mm256_sllv_epi32_u32(
        vector: BitVec<256>,
        b7: u32,
        b6: u32,
        b5: u32,
        b4: u32,
        b3: u32,
        b2: u32,
        b1: u32,
        b0: u32,
    ) -> BitVec<256> {
        mm256_sllv_epi32_u32_array(
            vector,
            FunArray::from_fn(|i| match i {
                7 => b7,
                6 => b6,
                5 => b5,
                4 => b4,
                3 => b3,
                2 => b2,
                1 => b1,
                0 => b0,
                _ => unreachable!(),
            }),
        )
    }

    pub fn mm256_permutevar8x32_epi32_u32_array(
        a: BitVec<256>,
        b: FunArray<8, u32>,
    ) -> BitVec<256> {
        BitVec::from_fn(|i| {
            let j = i / 32;
            let index = ((b[j] % 7) as u64) * 32;
            a[index + i % 32]
        })
    }

    pub fn mm256_permutevar8x32_epi32_u32(
        vector: BitVec<256>,
        b7: u32,
        b6: u32,
        b5: u32,
        b4: u32,
        b3: u32,
        b2: u32,
        b1: u32,
        b0: u32,
    ) -> BitVec<256> {
        mm256_permutevar8x32_epi32_u32_array(
            vector,
            FunArray::from_fn(|i| match i {
                7 => b7,
                6 => b6,
                5 => b5,
                4 => b4,
                3 => b3,
                2 => b2,
                1 => b1,
                0 => b0,
                _ => unreachable!(),
            }),
        )
    }

    pub fn mm_shuffle_epi8_u8_array(vector: BitVec<128>, indexes: FunArray<16, u8>) -> BitVec<128> {
        BitVec::from_fn(|i| {
            let nth = i / 8;
            let index = indexes[nth];
            if index > 127 {
                Bit::Zero
            } else {
                let index = (index % 15) as u64;
                vector[index * 8 + i % 8]
            }
        })
    }

    pub fn mm_shuffle_epi8_u8(
        vector: BitVec<128>,
        b15: u8,
        b14: u8,
        b13: u8,
        b12: u8,
        b11: u8,
        b10: u8,
        b9: u8,
        b8: u8,
        b7: u8,
        b6: u8,
        b5: u8,
        b4: u8,
        b3: u8,
        b2: u8,
        b1: u8,
        b0: u8,
    ) -> BitVec<128> {
        let indexes = FunArray::from_fn(|i| match i {
            15 => b15,
            14 => b14,
            13 => b13,
            12 => b12,
            11 => b11,
            10 => b10,
            9 => b9,
            8 => b8,
            7 => b7,
            6 => b6,
            5 => b5,
            4 => b4,
            3 => b3,
            2 => b2,
            1 => b1,
            0 => b0,
            _ => unreachable!(),
        });
        mm_shuffle_epi8_u8_array(vector, indexes)
    }

    #[hax_lib::exclude]
    pub fn mm_storeu_bytes_si128(output: &mut [u8], vector: BitVec<128>) {
        output.copy_from_slice(&vector.to_vec()[..]);
    }
}

/// Tests of equivalence between `safe::*` and `upstream::*`.
#[cfg(all(test, any(target_arch = "x86", target_arch = "x86_64")))]
mod tests {
    use super::*;

    /// Number of tests to run for each function
    const N: usize = 1000;

    #[test]
    fn mm256_slli_epi16() {
        macro_rules! mk {
                ($($shift: literal)*) => {
                    $(for _ in 0..N {
                        let input = BitVec::<256>::rand();
                        assert_eq!(
                            super::_mm256_slli_epi16::<$shift>(input),
                            unsafe {upstream::_mm256_slli_epi16::<$shift>(input.into()).into()}
                        );
                    })*
                };
            }
        mk!(0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15);
    }

    #[test]
    fn mm256_srli_epi64() {
        macro_rules! mk {
                ($($shift: literal)*) => {
                    $(for _ in 0..N {
                        let input = BitVec::<256>::rand();
                        assert_eq!(
                            super::_mm256_srli_epi64::<$shift>(input),
                            unsafe{upstream::_mm256_srli_epi64::<$shift>(input.into()).into()}
                        );
                    })*
                };
            }
        mk!(0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31 32 33 34 35 36 37 38 39 40 41 42 43 44 45 46 47 48 49 50 51 52 53 54 55 56 57 58 59 60 61 62 63);
    }

    #[test]
    fn mm256_sllv_epi32() {
        for _ in 0..100 {
            let vector: BitVec<256> = BitVec::rand();
            let counts: BitVec<256> = BitVec::rand();
            assert_eq!(super::_mm256_sllv_epi32(vector, counts), unsafe {
                upstream::_mm256_sllv_epi32(vector.into(), counts.into()).into()
            });
        }
    }

    #[test]
    fn mm256_permutevar8x32_epi32() {
        for _ in 0..N {
            let vector: BitVec<256> = BitVec::rand();
            let counts: BitVec<256> = BitVec::rand();
            assert_eq!(super::_mm256_permutevar8x32_epi32(vector, counts), unsafe {
                upstream::_mm256_permutevar8x32_epi32(vector.into(), counts.into()).into()
            });
        }
    }

    #[test]
    fn mm256_castsi256_si128() {
        for _ in 0..N {
            let vector: BitVec<256> = BitVec::rand();
            assert_eq!(super::_mm256_castsi256_si128(vector), unsafe {
                upstream::_mm256_castsi256_si128(vector.into()).into()
            });
        }
    }

    #[test]
    fn mm_shuffle_epi8() {
        for _ in 0..N {
            let a: BitVec<128> = BitVec::rand();
            let _: upstream::__m128i = a.into();
            let b: BitVec<128> = BitVec::rand();
            assert_eq!(super::_mm_shuffle_epi8(a, b), unsafe {
                upstream::_mm_shuffle_epi8(a.into(), b.into()).into()
            });
        }
    }
}
