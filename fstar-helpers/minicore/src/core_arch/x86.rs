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
#[hax_lib::exclude]
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

#[hax_lib::fstar::replace(
    r#"
    unfold type t_e_ee_m256i = $:{__m256i}
    unfold type t_e_ee_m128i = $:{__m128i}
"#
)]
const _: () = {};

#[allow(non_camel_case_types)]
struct __m256(());

/// 256-bit wide integer vector type.
/// Models `core::arch::x86::__m256i` or `core::arch::x86_64::__m256i` (the __m256i type defined by Intel, representing a 256-bit SIMD register).
#[allow(non_camel_case_types)]
pub type __m256i = BitVec<256>;

/// 128-bit wide integer vector type.
/// Models `core::arch::x86::__m128i` or `core::arch::x86_64::__m128i` (the __m128i type defined by Intel, representing a 128-bit SIMD register).
#[allow(non_camel_case_types)]
pub type __m128i = BitVec<128>;

pub use ssse3::*;
pub mod ssse3 {
    use super::*;
    #[hax_lib::opaque]
    pub fn _mm_shuffle_epi8(vector: __m128i, indexes: __m128i) -> __m128i {
        let indexes = indexes.to_vec().try_into().unwrap();
        extra::mm_shuffle_epi8_u8_array(vector, indexes)
    }
}
pub use sse2::*;
pub mod sse2 {
    use super::*;
    #[hax_lib::opaque]
    pub fn _mm_set_epi8(
        e15: i8,
        e14: i8,
        e13: i8,
        e12: i8,
        e11: i8,
        e10: i8,
        e9: i8,
        e8: i8,
        e7: i8,
        e6: i8,
        e5: i8,
        e4: i8,
        e3: i8,
        e2: i8,
        e1: i8,
        e0: i8,
    ) -> __m128i {
        todo!()
    }
}

pub use avx::*;
pub mod avx {
    pub use super::*;
    pub fn _mm256_castsi256_si128(vector: __m256i) -> __m128i {
        BitVec::from_fn(|i| vector[i])
    }

    #[hax_lib::opaque]
    pub fn _mm256_set_epi32(
        e0: i32,
        e1: i32,
        e2: i32,
        e3: i32,
        e4: i32,
        e5: i32,
        e6: i32,
        e7: i32,
    ) -> __m256i {
        todo!()
    }
}
pub use avx2::*;
pub mod avx2 {
    use super::*;
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
        vector.chunked_shift::<16, 16>(FunArray::from_fn(|_| SHIFT_BY as i128))
    }

    #[hax_lib::requires(SHIFT_BY >= 0 && SHIFT_BY < 64)]
    pub fn _mm256_srli_epi64<const SHIFT_BY: i32>(vector: __m256i) -> __m256i {
        vector.chunked_shift::<64, 4>(FunArray::from_fn(|_| -(SHIFT_BY as i128)))
    }

    // pub fn _mm256_mullo_epi16(vector: __m256i, shifts: __m256i) -> __m256i {
    //     todo!()
    // }

    #[hax_lib::opaque]
    pub fn _mm256_sllv_epi32(vector: __m256i, counts: __m256i) -> __m256i {
        extra::mm256_sllv_epi32_u32_array(vector, counts.to_vec().try_into().unwrap())
    }

    #[hax_lib::opaque]
    pub fn _mm256_srlv_epi32(vector: __m256i, counts: __m256i) -> __m256i {
        extra::mm256_srlv_epi32_u32_array(vector, counts.to_vec().try_into().unwrap())
    }

    #[hax_lib::opaque]
    pub fn _mm256_permutevar8x32_epi32(a: __m256i, b: __m256i) -> __m256i {
        extra::mm256_permutevar8x32_epi32_u32_array(a, b.to_vec().try_into().unwrap())
    }

    pub fn _mm256_extracti128_si256<const IMM8: i32>(vector: __m256i) -> __m128i {
        BitVec::from_fn(|i| vector[i + if IMM8 == 0 { 0 } else { 128 }])
    }
}

/// Rewrite lemmas
const _: () = {
    #[hax_lib::fstar::before("[@@ $REWRITE_RULE ]")]
    #[hax_lib::lemma]
    #[hax_lib::opaque]
    fn _rw_mm256_sllv_epi32(
        vector: __m256i,
        b7: i32,
        b6: i32,
        b5: i32,
        b4: i32,
        b3: i32,
        b2: i32,
        b1: i32,
        b0: i32,
    ) -> Proof<
        {
            hax_lib::prop::eq(
                _mm256_sllv_epi32(vector, _mm256_set_epi32(b7, b6, b5, b4, b3, b2, b1, b0)),
                extra::mm256_sllv_epi32_u32(
                    vector, b7 as u32, b6 as u32, b5 as u32, b4 as u32, b3 as u32, b2 as u32,
                    b1 as u32, b0 as u32,
                ),
            )
        },
    > {
    }

    #[hax_lib::fstar::before("[@@ $REWRITE_RULE ]")]
    #[hax_lib::lemma]
    #[hax_lib::opaque]
    fn _rw_mm256_permutevar8x32_epi32(
        vector: __m256i,
        b7: i32,
        b6: i32,
        b5: i32,
        b4: i32,
        b3: i32,
        b2: i32,
        b1: i32,
        b0: i32,
    ) -> Proof<
        {
            hax_lib::prop::eq(
                _mm256_permutevar8x32_epi32(
                    vector,
                    _mm256_set_epi32(b7, b6, b5, b4, b3, b2, b1, b0),
                ),
                extra::mm256_permutevar8x32_epi32_u32(
                    vector, b7 as u32, b6 as u32, b5 as u32, b4 as u32, b3 as u32, b2 as u32,
                    b1 as u32, b0 as u32,
                ),
            )
        },
    > {
    }

    #[hax_lib::fstar::before("[@@ $REWRITE_RULE ]")]
    #[hax_lib::lemma]
    #[hax_lib::opaque]
    fn _rw_mm_shuffle_epi8(
        vector: __m128i,
        e15: i8,
        e14: i8,
        e13: i8,
        e12: i8,
        e11: i8,
        e10: i8,
        e9: i8,
        e8: i8,
        e7: i8,
        e6: i8,
        e5: i8,
        e4: i8,
        e3: i8,
        e2: i8,
        e1: i8,
        e0: i8,
    ) -> Proof<
        {
            hax_lib::prop::eq(
                _mm_shuffle_epi8(
                    vector,
                    _mm_set_epi8(
                        e15, e14, e13, e12, e11, e10, e9, e8, e7, e6, e5, e4, e3, e2, e1, e0,
                    ),
                ),
                extra::mm_shuffle_epi8_u8(
                    vector, e15 as u8, e14 as u8, e13 as u8, e12 as u8, e11 as u8, e10 as u8,
                    e9 as u8, e8 as u8, e7 as u8, e6 as u8, e5 as u8, e4 as u8, e3 as u8, e2 as u8,
                    e1 as u8, e0 as u8,
                ),
            )
        },
    > {
    }
};

pub mod extra {
    use super::*;

    pub fn mm256_sllv_epi32_u32_array(
        vector: BitVec<256>,
        counts: FunArray<8, u32>,
    ) -> BitVec<256> {
        vector.chunked_shift::<32, 8>(FunArray::from_fn(|i| counts[i] as i128))
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

    pub fn mm256_srlv_epi32_u32_array(
        vector: BitVec<256>,
        counts: FunArray<8, u32>,
    ) -> BitVec<256> {
        vector.chunked_shift::<32, 8>(FunArray::from_fn(|i| -(counts[i] as i128)))
    }

    pub fn mm256_srlv_epi32_u32(
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
        mm256_srlv_epi32_u32_array(
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
            let index = ((b[j] % 8) as u64) * 32;
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
                let index = (index % 16) as u64;
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

    // pub fn _mm256_mullo_epi16(a: __m256i, b: __m256i) -> __m256i {
    //     BitVec::from_fn(|i| {
    //         let nth_bit = i % 16;
    //         let nth_i16 = i / 16;

    //         let a_slice = FunArray::<16, Bit>::from_fn(|i| a[nth_i16 * 16 + i]);
    //         let b_slice = FunArray::<16, Bit>::from_fn(|i| b[nth_i16 * 16 + i]);

    //         match b_slice.log2() {
    //             Some(shift) => {
    //                 if nth_bit >= shift {
    //                     a_slice[i - shift]
    //                 } else {
    //                     Bit::Zero
    //                 }
    //             }
    //             None => BitVec::<64>::from_int(a_slice.to_u64().saturating_mul(b_slice.to_u64()))
    //                 [nth_bit],
    //         }
    //     })
    // }

    pub fn mm256_mullo_epi16_shifts(
        vector: __m256i,
        s15: u8,
        s14: u8,
        s13: u8,
        s12: u8,
        s11: u8,
        s10: u8,
        s9: u8,
        s8: u8,
        s7: u8,
        s6: u8,
        s5: u8,
        s4: u8,
        s3: u8,
        s2: u8,
        s1: u8,
        s0: u8,
    ) -> __m256i {
        let shifts = FunArray::<16, _>::from_fn(|i| match i {
            15 => s15,
            14 => s14,
            13 => s13,
            12 => s12,
            11 => s11,
            10 => s10,
            9 => s9,
            8 => s8,
            7 => s7,
            6 => s6,
            5 => s5,
            4 => s4,
            3 => s3,
            2 => s2,
            1 => s1,
            0 => s0,
            _ => unreachable!(),
        });
        mm256_mullo_epi16_shifts_array(vector, shifts)
    }
    pub fn mm256_mullo_epi16_shifts_array(vector: __m256i, shifts: FunArray<16, u8>) -> __m256i {
        BitVec::from_fn(|i| {
            let nth_bit = i % 16;
            let nth_i16 = i / 16;

            let shift = shifts[nth_i16] as u64;

            if nth_bit >= shift {
                vector[nth_i16 * 16 + nth_bit - shift]
            } else {
                Bit::Zero
            }
        })
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
        for _ in 0..N {
            let vector: BitVec<256> = BitVec::rand();
            let counts: BitVec<256> = BitVec::rand();
            assert_eq!(super::_mm256_sllv_epi32(vector, counts), unsafe {
                upstream::_mm256_sllv_epi32(vector.into(), counts.into()).into()
            });
        }
    }

    #[test]
    fn mm256_srlv_epi32() {
        for _ in 0..N {
            let vector: BitVec<256> = BitVec::rand();
            let counts: BitVec<256> = BitVec::rand();
            assert_eq!(super::_mm256_srlv_epi32(vector, counts), unsafe {
                upstream::_mm256_srlv_epi32(vector.into(), counts.into()).into()
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
    fn mm256_extracti128_si256() {
        for _ in 0..N {
            let vector: BitVec<256> = BitVec::rand();
            assert_eq!(super::_mm256_extracti128_si256::<0>(vector), unsafe {
                upstream::_mm256_extracti128_si256::<0>(vector.into()).into()
            });
            assert_eq!(super::_mm256_extracti128_si256::<1>(vector), unsafe {
                upstream::_mm256_extracti128_si256::<1>(vector.into()).into()
            });
        }
    }

    #[test]
    fn mm_shuffle_epi8() {
        for _ in 0..N {
            let a: BitVec<128> = BitVec::rand();
            let b: BitVec<128> = BitVec::rand();

            assert_eq!(super::_mm_shuffle_epi8(a, b), unsafe {
                upstream::_mm_shuffle_epi8(a.into(), b.into()).into()
            });
        }
    }
}
