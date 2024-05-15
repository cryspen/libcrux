//! # SHA3
//!
//! A SHA3 implementation with optional simd optimisations.

#![no_std]

pub mod simd;

mod generic_keccak;
mod portable_keccak;
mod traits;

/// A SHA3 224 Digest
pub type Sha3_224Digest = [u8; 28];

/// A SHA3 256 Digest
pub type Sha3_256Digest = [u8; 32];

/// A SHA3 384 Digest
pub type Sha3_384Digest = [u8; 48];

/// A SHA3 512 Digest
pub type Sha3_512Digest = [u8; 64];

/// The Digest Algorithm.
#[derive(Copy, Clone, Debug, PartialEq)]
#[repr(u32)]
pub enum Algorithm {
    Sha224 = 1,
    Sha256 = 2,
    Sha384 = 3,
    Sha512 = 4,
}

impl From<u32> for Algorithm {
    fn from(v: u32) -> Algorithm {
        match v {
            1 => Algorithm::Sha224,
            2 => Algorithm::Sha256,
            3 => Algorithm::Sha384,
            4 => Algorithm::Sha512,
            _ => panic!("Unknown Digest mode {}", v),
        }
    }
}

impl From<Algorithm> for u32 {
    fn from(v: Algorithm) -> u32 {
        match v {
            Algorithm::Sha224 => 1,
            Algorithm::Sha256 => 2,
            Algorithm::Sha384 => 3,
            Algorithm::Sha512 => 4,
        }
    }
}

/// Returns the output size of a digest.
pub const fn digest_size(mode: Algorithm) -> usize {
    match mode {
        Algorithm::Sha224 => 28,
        Algorithm::Sha256 => 32,
        Algorithm::Sha384 => 48,
        Algorithm::Sha512 => 64,
    }
}

/// SHA3
pub fn hash<const LEN: usize>(algorithm: Algorithm, payload: &[u8]) -> [u8; LEN] {
    debug_assert!(payload.len() <= u32::MAX as usize);

    let mut out = [0u8; LEN];
    match algorithm {
        Algorithm::Sha224 => portable::sha224(&mut out, payload),
        Algorithm::Sha256 => portable::sha256(&mut out, payload),
        Algorithm::Sha384 => portable::sha384(&mut out, payload),
        Algorithm::Sha512 => portable::sha512(&mut out, payload),
    }
    out
}

/// SHA3 224
#[inline(always)]
pub fn sha224(data: &[u8]) -> Sha3_224Digest {
    let mut out = [0u8; 28];
    sha224_ema(&mut out, data);
    out
}

/// SHA3 224
///
/// Preconditions:
/// - `digest.len() == 28`
#[inline(always)]
pub fn sha224_ema(digest: &mut [u8], payload: &[u8]) {
    debug_assert!(payload.len() <= u32::MAX as usize);
    debug_assert!(digest.len() == 28);

    portable::sha224(digest, payload)
}

/// SHA3 256
#[inline(always)]
pub fn sha256(data: &[u8]) -> Sha3_256Digest {
    let mut out = [0u8; 32];
    sha256_ema(&mut out, data);
    out
}

/// SHA3 256
#[inline(always)]
pub fn sha256_ema(digest: &mut [u8], payload: &[u8]) {
    debug_assert!(payload.len() <= u32::MAX as usize);
    debug_assert!(digest.len() == 32);

    portable::sha256(digest, payload)
}

/// SHA3 384
#[inline(always)]
pub fn sha384(data: &[u8]) -> Sha3_384Digest {
    let mut out = [0u8; 48];
    sha384_ema(&mut out, data);
    out
}

/// SHA3 384
#[inline(always)]
pub fn sha384_ema(digest: &mut [u8], payload: &[u8]) {
    debug_assert!(payload.len() <= u32::MAX as usize);
    debug_assert!(digest.len() == 48);

    portable::sha384(digest, payload)
}

/// SHA3 512
#[inline(always)]
pub fn sha512(data: &[u8]) -> Sha3_512Digest {
    let mut out = [0u8; 64];
    sha512_ema(&mut out, data);
    out
}

/// SHA3 512
#[inline(always)]
pub fn sha512_ema(digest: &mut [u8], payload: &[u8]) {
    debug_assert!(payload.len() <= u32::MAX as usize);
    debug_assert!(digest.len() == 64);

    portable::sha512(digest, payload)
}

/// SHAKE 128
#[inline(always)]
pub fn shake128<const BYTES: usize>(data: &[u8]) -> [u8; BYTES] {
    let mut out = [0u8; BYTES];
    portable::shake128(&mut out, data);
    out
}

/// SHAKE 256
///
/// Note that the output length `BYTES` must fit into 32 bit. If it is longer,
/// the output will only return `u32::MAX` bytes.
#[inline(always)]
pub fn shake256<const BYTES: usize>(data: &[u8]) -> [u8; BYTES] {
    let mut out = [0u8; BYTES];
    portable::shake256(&mut out, data);
    out
}

mod incremental {}

//  === The portable instantiation === //

/// A portable SHA3 implementations without platform dependent optimisations.
pub mod portable {
    use super::*;
    use generic_keccak::{keccak, KeccakState};

    pub type KeccakState1 = KeccakState<1, u64>;

    #[inline(always)]
    fn keccakx1<const RATE: usize, const DELIM: u8>(data: [&[u8]; 1], out: [&mut [u8]; 1]) {
        keccak::<1, u64, RATE, DELIM>(data, out)
    }

    /// A portable SHA3 224 implementation.
    pub fn sha224(digest: &mut [u8], data: &[u8]) {
        keccakx1::<144, 0x06u8>([data], [digest]);
    }

    /// A portable SHA3 256 implementation.
    pub fn sha256(digest: &mut [u8], data: &[u8]) {
        keccakx1::<136, 0x06u8>([data], [digest]);
    }

    /// A portable SHA3 384 implementation.
    pub fn sha384(digest: &mut [u8], data: &[u8]) {
        keccakx1::<104, 0x06u8>([data], [digest]);
    }

    /// A portable SHA3 512 implementation.
    pub fn sha512(digest: &mut [u8], data: &[u8]) {
        keccakx1::<72, 0x06u8>([data], [digest]);
    }

    /// A portable SHAKE128 implementation.
    pub fn shake128<const LEN: usize>(digest: &mut [u8; LEN], data: &[u8]) {
        keccakx1::<168, 0x1fu8>([data], [digest]);
    }

    /// A portable SHAKE256 implementation.
    pub fn shake256<const LEN: usize>(digest: &mut [u8; LEN], data: &[u8]) {
        keccakx1::<136, 0x1fu8>([data], [digest]);
    }

    /// An incremental API for SHAKE
    pub mod incremental {
        use generic_keccak::{absorb_final, squeeze_first_three_blocks, squeeze_next_block};

        use super::*;

        /// Initialise the SHAKE state.
        pub fn shake128_init() -> KeccakState1 {
            KeccakState1::new()
        }

        /// Absorb
        pub fn shake128_absorb_final(s: &mut KeccakState1, data0: &[u8]) {
            absorb_final::<1, u64, 168, 0x1fu8>(s, [data0]);
        }

        /// Squeeze three blocks
        pub fn shake128_squeeze_first_three_blocks(s: &mut KeccakState1, out0: &mut [u8]) {
            squeeze_first_three_blocks::<1, u64, 168>(s, [out0])
        }

        /// Squeeze another block
        pub fn shake128_squeeze_next_block(s: &mut KeccakState1, out0: &mut [u8]) {
            squeeze_next_block::<1, u64, 168>(s, [out0])
        }
    }
}

/// A neon optimised implementation.
///
/// When this is compiled for non-neon architectures, the functions panic.
/// The caller must make sure to check for hardware feature before calling these
/// functions and compile them in.
///
/// Feature `simd128` enables the implementations in this module.
pub mod neon {
    #[cfg(feature = "simd128")]
    #[inline(always)]
    fn keccakx2<const RATE: usize, const DELIM: u8>(data: [&[u8]; 2], out: [&mut [u8]; 2]) {
        keccak::<2, core::arch::aarch64::uint64x2_t, RATE, DELIM>(data, out)
    }

    /// A portable SHA3 224 implementation.
    #[allow(unused_variables)]
    pub fn sha224(digest: &mut [u8], data: &[u8]) {
        #[cfg(not(feature = "simd128"))]
        unimplemented!("The target architecture does not support neon instructions.");
        #[cfg(feature = "simd128")]
        {
            let mut dummy = [0u8; 28];
            keccakx2::<144, 0x06u8>([data, data], [digest, &mut dummy]);
        }
    }

    /// A portable SHA3 256 implementation.
    #[allow(unused_variables)]
    pub fn sha256(digest: &mut [u8], data: &[u8]) {
        #[cfg(not(feature = "simd128"))]
        unimplemented!("The target architecture does not support neon instructions.");
        #[cfg(feature = "simd128")]
        {
            let mut dummy = [0u8; 32];
            keccakx2::<136, 0x06u8>([data, data], [digest, &mut dummy]);
        }
    }

    /// A portable SHA3 384 implementation.
    #[allow(unused_variables)]
    pub fn sha384(digest: &mut [u8], data: &[u8]) {
        #[cfg(not(feature = "simd128"))]
        unimplemented!("The target architecture does not support neon instructions.");
        #[cfg(feature = "simd128")]
        {
            let mut dummy = [0u8; 48];
            keccakx2::<104, 0x06u8>([data, data], [digest, &mut dummy]);
        }
    }

    /// A portable SHA3 512 implementation.
    #[allow(unused_variables)]
    pub fn sha512(digest: &mut [u8], data: &[u8]) {
        #[cfg(not(feature = "simd128"))]
        unimplemented!("The target architecture does not support neon instructions.");
        #[cfg(feature = "simd128")]
        {
            let mut dummy = [0u8; 64];
            keccakx2::<72, 0x06u8>([data, data], [digest, &mut dummy]);
        }
    }

    /// A portable SHAKE128 implementation.
    #[allow(unused_variables)]
    pub fn shake128<const LEN: usize>(digest: &mut [u8; LEN], data: &[u8]) {
        #[cfg(not(feature = "simd128"))]
        unimplemented!("The target architecture does not support neon instructions.");
        #[cfg(feature = "simd128")]
        {
            let mut dummy = [0u8; LEN];
            keccakx2::<168, 0x1fu8>([data, data], [digest, &mut dummy]);
        }
    }

    /// A portable SHAKE256 implementation.
    #[allow(unused_variables)]
    pub fn shake256<const LEN: usize>(digest: &mut [u8; LEN], data: &[u8]) {
        #[cfg(not(feature = "simd128"))]
        unimplemented!("The target architecture does not support neon instructions.");
        #[cfg(feature = "simd128")]
        {
            let mut dummy = [0u8; LEN];
            keccakx2::<136, 0x1fu8>([data, data], [digest, &mut dummy]);
        }
    }

    /// Performing 2 operations in parallel
    pub mod x2 {

        /// Run SHAKE256 on both inputs in parallel.
        ///
        /// Writes the two results into `out0` and `out1`
        #[allow(unused_variables)]
        pub fn shake256x2(input0: &[u8], input1: &[u8], out0: &mut [u8], out1: &mut [u8]) {
            // TODO: make argument ordering consistent
            #[cfg(not(feature = "simd128"))]
            unimplemented!("The target architecture does not support neon instructions.");
            #[cfg(feature = "simd128")]
            keccakx2::<136, 0x1fu8>([input0, input1], [out0, out1]);
        }

        /// An incremental API to perform 2 operations in parallel
        pub mod incremental {
            use crate::portable::KeccakState1;

            #[cfg(feature = "simd128")]
            pub type KeccakState2 = KeccakState<2, core::arch::aarch64::uint64x2_t>;
            #[cfg(not(feature = "simd128"))]
            pub type KeccakState2 = [KeccakState1; 2];

            pub fn shake128x2_init() -> KeccakState2 {
                #[cfg(not(feature = "simd128"))]
                unimplemented!("The target architecture does not support neon instructions.");
                // XXX: These functions could alternatively implement the same with
                //      the portable implementation
                // {
                //     let s0 = KeccakState1::new();
                //     let s1 = KeccakState1::new();
                //     [s0, s1]
                // }
                #[cfg(feature = "simd128")]
                KeccakState2::new()
            }

            #[allow(unused_variables)]
            pub fn shake128x2_absorb_final(s: &mut KeccakState2, data0: &[u8], data1: &[u8]) {
                #[cfg(not(feature = "simd128"))]
                unimplemented!("The target architecture does not support neon instructions.");
                // XXX: These functions could alternatively implement the same with
                //      the portable implementation
                // {
                //     let [mut s0, mut s1] = s;
                //     shake128_absorb_final(&mut s0, data0);
                //     shake128_absorb_final(&mut s1, data1);
                // }
                #[cfg(feature = "simd128")]
                absorb_final::<2, core::arch::aarch64::uint64x2_t, 168, 0x1fu8>(s, [data0, data1]);
            }

            #[allow(unused_variables)]
            pub fn shake128x2_squeeze_first_three_blocks(
                s: &mut KeccakState2,
                out0: &mut [u8],
                out1: &mut [u8],
            ) {
                #[cfg(not(feature = "simd128"))]
                unimplemented!("The target architecture does not support neon instructions.");
                // XXX: These functions could alternatively implement the same with
                //      the portable implementation
                // {
                //     let [mut s0, mut s1] = s;
                //     shake128_squeeze_first_three_blocks(&mut s0, out0);
                //     shake128_squeeze_first_three_blocks(&mut s1, out1);
                // }
                #[cfg(feature = "simd128")]
                squeeze_first_three_blocks::<2, core::arch::aarch64::uint64x2_t, 168>(
                    s,
                    [out0, out1],
                )
            }

            #[allow(unused_variables)]
            pub fn shake128x2_squeeze_next_block(
                s: &mut KeccakState2,
                out0: &mut [u8],
                out1: &mut [u8],
            ) {
                #[cfg(not(feature = "simd128"))]
                unimplemented!("The target architecture does not support neon instructions.");
                // XXX: These functions could alternatively implement the same with
                //      the portable implementation
                // {
                //     let [mut s0, mut s1] = s;
                //     shake128_squeeze_next_block(&mut s0, out0);
                //     shake128_squeeze_next_block(&mut s1, out1);
                // }
                #[cfg(feature = "simd128")]
                squeeze_next_block::<2, core::arch::aarch64::uint64x2_t, 168>(s, [out0, out1])
            }
        }
    }
}

/// An AVX2 optimised implementaiton.
///
/// When this is compiled for non-neon architectures, the functions panic.
/// The caller must make sure to check for hardware feature before calling these
/// functions and compile them in.
///
/// Feature `simd256` enables the implementations in this module.
pub mod avx2 {

    /// Performing 4 operations in parallel
    pub mod x4 {
        use crate::generic_keccak::keccak;

        /// Perform 4 SHAKE256 operations in parallel
        pub fn shake256x4(
            input0: &[u8],
            input1: &[u8],
            input2: &[u8],
            input3: &[u8],
            out0: &mut [u8],
            out1: &mut [u8],
            out2: &mut [u8],
            out3: &mut [u8],
        ) {
            #[cfg(not(feature = "simd256"))]
            unimplemented!("The target architecture does not support neon instructions.");
            // XXX: These functions could alternatively implement the same with
            //      the portable implementation
            // #[cfg(feature = "simd128")]
            // {
            //     keccakx2::<136, 0x1fu8>([input0, input1], [out0, out1]);
            //     keccakx2::<136, 0x1fu8>([input2, input3], [out2, out3]);
            // }
            // {
            //     keccakx1::<136, 0x1fu8>([input0], [out0]);
            //     keccakx1::<136, 0x1fu8>([input1], [out1]);
            //     keccakx1::<136, 0x1fu8>([input2], [out2]);
            //     keccakx1::<136, 0x1fu8>([input3], [out3]);
            // }
            #[cfg(feature = "simd256")]
            keccak::<4, core::arch::x86_64::__m256i, 136, 0x1fu8>(
                [input0, input1, input2, input3],
                [out0, out1, out2, out3],
            );
        }

        /// An incremental API to perform 4 operations in parallel
        pub mod incremental {
            use crate::generic_keccak::{
                absorb_final, squeeze_first_three_blocks, squeeze_next_block, KeccakState,
            };

            #[cfg(feature = "simd256")]
            pub type KeccakState4 = KeccakState<4, core::arch::x86_64::__m256i>;
            #[cfg(feature = "simd128")]
            pub type KeccakState4 = [KeccakState2; 2];
            #[cfg(not(any(feature = "simd256", feature = "simd128")))]
            pub type KeccakState4 = [KeccakState1; 4];

            pub fn shake128x4_init() -> KeccakState4 {
                #[cfg(not(feature = "simd256"))]
                unimplemented!("The target architecture does not support neon instructions.");
                // XXX: These functions could alternatively implement the same with
                //      the portable implementation
                // #[cfg(feature = "simd128")]
                // {
                //     let s0 = KeccakState2::new();
                //     let s1 = KeccakState2::new();
                //     [s0, s1]
                // }
                // #[cfg(not(any(feature = "simd128", feature = "simd256")))]
                // {
                //     let s0 = KeccakState1::new();
                //     let s1 = KeccakState1::new();
                //     let s2 = KeccakState1::new();
                //     let s3 = KeccakState1::new();
                //     [s0, s1, s2, s3]
                // }
                #[cfg(feature = "simd256")]
                KeccakState4::new()
            }

            pub fn shake128x4_absorb_final(
                s: &mut KeccakState4,
                data0: &[u8],
                data1: &[u8],
                data2: &[u8],
                data3: &[u8],
            ) {
                #[cfg(not(feature = "simd256"))]
                unimplemented!("The target architecture does not support neon instructions.");
                // XXX: These functions could alternatively implement the same with
                //      the portable implementation
                // #[cfg(feature = "simd128")]
                // {
                //     let [mut s0, mut s1] = s;
                //     absorb_final::<2, core::arch::aarch64::uint64x2_t, 168, 0x1fu8>(
                //         &mut s0,
                //         [data0, data1],
                //     );
                //     absorb_final::<2, core::arch::aarch64::uint64x2_t, 168, 0x1fu8>(
                //         &mut s1,
                //         [data2, data3],
                //     );
                // }
                // #[cfg(not(any(feature = "simd128", feature = "simd256")))]
                // {
                //     let [mut s0, mut s1, mut s2, mut s3] = s;
                //     shake128_absorb_final(&mut s0, data0);
                //     shake128_absorb_final(&mut s1, data1);
                //     shake128_absorb_final(&mut s2, data2);
                //     shake128_absorb_final(&mut s3, data3);
                // }
                #[cfg(feature = "simd256")]
                absorb_final::<4, core::arch::x86_64::__m256i, 168, 0x1fu8>(
                    s,
                    [data0, data1, data2, data3],
                );
            }

            pub fn shake128x4_squeeze_first_three_blocks(
                s: &mut KeccakState4,
                out0: &mut [u8],
                out1: &mut [u8],
                out2: &mut [u8],
                out3: &mut [u8],
            ) {
                #[cfg(not(feature = "simd256"))]
                unimplemented!("The target architecture does not support neon instructions.");
                // XXX: These functions could alternatively implement the same with
                //      the portable implementation
                // #[cfg(feature = "simd128")]
                // {
                //     let [mut s0, mut s1] = s;
                //     squeeze_first_three_blocks::<2, core::arch::aarch64::uint64x2_t, 168>(
                //         &mut s0,
                //         [out0, out1],
                //     );
                //     squeeze_first_three_blocks::<2, core::arch::aarch64::uint64x2_t, 168>(
                //         &mut s1,
                //         [out2, out3],
                //     );
                // }
                // #[cfg(not(any(feature = "simd128", feature = "simd256")))]
                // {
                //     let [mut s0, mut s1, mut s2, mut s3] = s;
                //     shake128_squeeze_first_three_blocks(&mut s0, out0);
                //     shake128_squeeze_first_three_blocks(&mut s1, out1);
                //     shake128_squeeze_first_three_blocks(&mut s2, out2);
                //     shake128_squeeze_first_three_blocks(&mut s3, out3);
                // }
                #[cfg(feature = "simd256")]
                squeeze_first_three_blocks::<4, core::arch::x86_64::__m256i, 168>(
                    s,
                    [out0, out1, out2, out3],
                );
            }

            pub fn shake128x4_squeeze_next_block(
                s: &mut KeccakState4,
                out0: &mut [u8],
                out1: &mut [u8],
                out2: &mut [u8],
                out3: &mut [u8],
            ) {
                #[cfg(not(feature = "simd256"))]
                unimplemented!("The target architecture does not support neon instructions.");
                // XXX: These functions could alternatively implement the same with
                //      the portable implementation
                // #[cfg(feature = "simd128")]
                // {
                //     let [mut s0, mut s1] = s;
                //     squeeze_next_block::<2, core::arch::aarch64::uint64x2_t, 168>(
                //         &mut s0,
                //         [out0, out1],
                //     );
                //     squeeze_next_block::<2, core::arch::aarch64::uint64x2_t, 168>(
                //         &mut s1,
                //         [out2, out3],
                //     );
                // }
                // #[cfg(not(any(feature = "simd128", feature = "simd256")))]
                // {
                //     let [mut s0, mut s1, mut s2, mut s3] = s;
                //     shake128_squeeze_next_block(&mut s0, out0);
                //     shake128_squeeze_next_block(&mut s1, out1);
                //     shake128_squeeze_next_block(&mut s2, out2);
                //     shake128_squeeze_next_block(&mut s3, out3);
                // }
                #[cfg(feature = "simd256")]
                squeeze_next_block::<4, core::arch::x86_64::__m256i, 168>(
                    s,
                    [out0, out1, out2, out3],
                );
            }
        }
    }
}
