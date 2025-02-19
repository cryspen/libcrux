/// This is a (partial) mirror of [`core::arch::x86`] and [`core::arch::x86_64`].
use crate::abstractions::{bit::*, bitvec::*};

pub(crate) mod upstream {
    #[cfg(target_arch = "x86")]
    pub use core::arch::x86::*;
    #[cfg(target_arch = "x86_64")]
    pub use core::arch::x86_64::*;
}

#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
/// Conversions impls between `BitVec<N>` and `__mNi` types.
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

#[allow(non_camel_case_types)]
type __m256i = BitVec<256>;
#[allow(non_camel_case_types)]
type __m128i = BitVec<128>;

pub fn _mm_storeu_si128(output: *mut __m128i, a: __m128i) {
    // This is equivalent to `*output = a`
    let mut out = [0u8; 128];
    extra::mm_storeu_bytes_si128(&mut out, a);
    unsafe {
        *(output.as_mut().unwrap()) = BitVec::from_slice(&mut out, 8);
    }
}

pub fn _mm256_slli_epi16<const SHIFT_BY: i32>(vector: BitVec<256>) -> BitVec<256> {
    debug_assert!(SHIFT_BY >= 0 && SHIFT_BY < 16);
    BitVec::from_fn(|i| {
        let nth_bit = i % 16;
        let shift = SHIFT_BY as usize;
        if nth_bit >= shift {
            vector[i - shift]
        } else {
            Bit::Zero
        }
    })
}

pub fn _mm256_srli_epi64<const SHIFT_BY: i32>(vector: BitVec<256>) -> BitVec<256> {
    debug_assert!(SHIFT_BY >= 0 && SHIFT_BY < 64);
    BitVec::from_fn(|i| {
        let nth_bit = i % 64;
        let shift = SHIFT_BY as usize;
        if nth_bit < 64 - shift {
            vector[i + shift]
        } else {
            Bit::Zero
        }
    })
}

pub fn _mm256_sllv_epi32(vector: BitVec<256>, counts: BitVec<256>) -> BitVec<256> {
    extra::mm256_sllv_epi32_u32_array(vector, counts.to_vec().try_into().unwrap())
}

pub fn _mm256_permutevar8x32_epi32(a: BitVec<256>, b: BitVec<256>) -> BitVec<256> {
    extra::mm256_permutevar8x32_epi32_u32_array(a, b.to_vec().try_into().unwrap())
}

pub fn _mm256_castsi256_si128(vector: BitVec<256>) -> BitVec<128> {
    BitVec::from_fn(|i| vector[i])
}

pub fn _mm_shuffle_epi8(vector: BitVec<128>, indexes: BitVec<128>) -> BitVec<128> {
    let indexes: [u8; 16] = indexes.to_vec().try_into().unwrap();
    extra::mm_shuffle_epi8_u8_array(vector, indexes)
}

mod extra {
    use super::*;

    pub fn mm256_sllv_epi32_u32_array(vector: BitVec<256>, counts: [u32; 8]) -> BitVec<256> {
        BitVec::from_fn(|i| {
            let nth_bit = i % 32;
            let shift = counts[i / 32];
            if nth_bit as i128 >= shift as i128 {
                vector[i - shift as usize]
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
        mm256_sllv_epi32_u32_array(vector, [b7, b6, b5, b4, b3, b2, b1, b0])
    }

    pub fn mm256_permutevar8x32_epi32_u32_array(a: BitVec<256>, b: [u32; 8]) -> BitVec<256> {
        BitVec::from_fn(|i| {
            let j = i / 32;
            let index = ((b[j] & 0b111) as usize) * 32;
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
        mm256_permutevar8x32_epi32_u32_array(vector, [b7, b6, b5, b4, b3, b2, b1, b0])
    }

    pub fn mm_shuffle_epi8_u8_array(vector: BitVec<128>, indexes: [u8; 16]) -> BitVec<128> {
        BitVec::from_fn(|i: usize| {
            let nth = i / 8;
            let index = indexes[nth];
            if index > 127 {
                Bit::Zero
            } else {
                let index = (index & 0b1111) as usize;
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
        let indexes = [
            b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0,
        ];
        mm_shuffle_epi8_u8_array(vector, indexes)
    }

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
