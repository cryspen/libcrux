//! # SHA3
//!
//! A SHA3 implementation with optional simd optimisations.

#![no_std]
#![forbid(unsafe_code)]
#![deny(missing_docs)]

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
#[cfg_attr(not(eurydice), derive(Copy, Clone, Debug, PartialEq))]
#[repr(u32)]
pub enum Algorithm {
    /// SHA3 224
    Sha224 = 1,

    /// SHA3 256
    Sha256 = 2,

    /// SHA3 384
    Sha384 = 3,

    /// SHA3 512
    Sha512 = 4,
}

impl From<u32> for Algorithm {
    fn from(v: u32) -> Algorithm {
        match v {
            1 => Algorithm::Sha224,
            2 => Algorithm::Sha256,
            3 => Algorithm::Sha384,
            4 => Algorithm::Sha512,
            _ => panic!(),
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

/// SHA3
pub use hash as sha3;

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
///
/// Note that the output length `BYTES` must fit into 32 bit. If it is longer,
/// the output will only return `u32::MAX` bytes.
#[inline(always)]
pub fn shake128<const BYTES: usize>(data: &[u8]) -> [u8; BYTES] {
    let mut out = [0u8; BYTES];
    portable::shake128(&mut out, data);
    out
}

/// SHAKE 128
///
/// Writes `out.len()` bytes.
#[inline(always)]
pub fn shake128_ema(out: &mut [u8], data: &[u8]) {
    portable::shake128(out, data);
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

/// SHAKE 256
///
/// Writes `out.len()` bytes.
#[inline(always)]
pub fn shake256_ema(out: &mut [u8], data: &[u8]) {
    portable::shake256(out, data);
}

//  === The portable instantiation === //

/// A portable SHA3 implementation without platform dependent optimisations.
pub mod portable {
    use super::*;
    use generic_keccak::KeccakState as GenericState;

    /// The Keccak state for the incremental API.
    #[derive(Clone, Copy)]
    pub struct KeccakState {
        state: GenericState<1, u64>,
    }

    #[inline(always)]
    fn keccakx1<const RATE: usize, const DELIM: u8>(data: [&[u8]; 1], out: [&mut [u8]; 1]) {
        // generic_keccak::keccak_xof::<1, u64, RATE, DELIM>(data, out);
        // or
        generic_keccak::keccak::<1, u64, RATE, DELIM>(data, out);
    }

    /// A portable SHA3 224 implementation.
    #[inline(always)]
    pub fn sha224(digest: &mut [u8], data: &[u8]) {
        keccakx1::<144, 0x06u8>([data], [digest]);
    }

    /// A portable SHA3 256 implementation.
    #[inline(always)]
    pub fn sha256(digest: &mut [u8], data: &[u8]) {
        keccakx1::<136, 0x06u8>([data], [digest]);
    }

    /// A portable SHA3 384 implementation.
    #[inline(always)]
    pub fn sha384(digest: &mut [u8], data: &[u8]) {
        keccakx1::<104, 0x06u8>([data], [digest]);
    }

    /// A portable SHA3 512 implementation.
    #[inline(always)]
    pub fn sha512(digest: &mut [u8], data: &[u8]) {
        keccakx1::<72, 0x06u8>([data], [digest]);
    }

    /// A portable SHAKE128 implementation.
    #[inline(always)]
    pub fn shake128(digest: &mut [u8], data: &[u8]) {
        keccakx1::<168, 0x1fu8>([data], [digest]);
    }

    /// A portable SHAKE256 implementation.
    #[inline(always)]
    pub fn shake256(digest: &mut [u8], data: &[u8]) {
        keccakx1::<136, 0x1fu8>([data], [digest]);
    }

    /// An incremental API for SHAKE
    pub mod incremental {
        use generic_keccak::{
            absorb_final, squeeze_first_block, squeeze_first_five_blocks,
            squeeze_first_three_blocks, squeeze_next_block, KeccakXofState,
        };
        mod private {
            pub trait Sealed {}

            impl Sealed for super::Shake128Absorb {}
            impl Sealed for super::Shake128Squeeze {}
            impl Sealed for super::Shake256Absorb {}
            impl Sealed for super::Shake256Squeeze {}
        }
        use super::*;

        /// SHAKE128 in absorb state
        pub struct Shake128Absorb {
            state: KeccakXofState<1, 168, u64>,
        }
        /// SHAKE128 in squeeze state
        pub struct Shake128Squeeze {
            state: KeccakXofState<1, 168, u64>,
        }
        /// SHAKE256 in absorb state
        pub struct Shake256Absorb {
            state: KeccakXofState<1, 136, u64>,
        }
        /// SHAKE256 in squeeze state
        pub struct Shake256Squeeze {
            state: KeccakXofState<1, 136, u64>,
        }

        /// An XOF in absorb state
        pub trait XofAbsorb<const RATE: usize>: private::Sealed {
            /// The state after final input absorption
            type Squeeze;

            /// Create new absorb state
            fn new() -> Self;

            /// Absorb input
            fn absorb(&mut self, input: &[u8]);

            /// Absorb final input (may be empty)
            fn absorb_final(self, input: &[u8]) -> Self::Squeeze;
        }

        impl XofAbsorb<168> for Shake128Absorb {
            type Squeeze = Shake128Squeeze;
            fn new() -> Self {
                Self {
                    state: KeccakXofState::<1, 168, u64>::new(),
                }
            }

            fn absorb(&mut self, input: &[u8]) {
                self.state.absorb([input]);
            }

            fn absorb_final(mut self, input: &[u8]) -> Shake128Squeeze {
                self.state.absorb_final::<0x1fu8>([input]);
                Shake128Squeeze { state: self.state }
            }
        }
        /// An XOF in squeeze state
        pub trait XofSqueeze<const RATE: usize>: private::Sealed {
            /// Squeeze output bytes
            fn squeeze(&mut self, out: &mut [u8]);
        }

        /// Shake128 XOF in squeeze state
        impl XofSqueeze<168> for Shake128Squeeze {
            /// Shake128 squeeze
            fn squeeze(&mut self, out: &mut [u8]) {
                self.state.squeeze([out]);
            }
        }

        /// Shake256 XOF in absorb state
        impl XofAbsorb<136> for Shake256Absorb {
            type Squeeze = Shake256Squeeze;
            /// Shake256 new state
            fn new() -> Self {
                Self {
                    state: KeccakXofState::<1, 136, u64>::new(),
                }
            }

            /// Shake256 absorb
            fn absorb(&mut self, input: &[u8]) {
                self.state.absorb([input]);
            }

            /// Shake256 absorb final
            fn absorb_final(mut self, input: &[u8]) -> Shake256Squeeze {
                self.state.absorb_final::<0x1fu8>([input]);
                Shake256Squeeze { state: self.state }
            }
        }

        /// Shake256 XOF in squeeze state
        impl XofSqueeze<136> for Shake256Squeeze {
            /// Shake256 squeeze
            fn squeeze(&mut self, out: &mut [u8]) {
                self.state.squeeze([out]);
            }
        }

        /// Create a new SHAKE-128 state object.
        #[inline(always)]
        pub fn shake128_init() -> KeccakState {
            KeccakState {
                state: GenericState::<1, u64>::new(),
            }
        }

        /// Absorb
        #[inline(always)]
        pub fn shake128_absorb_final(s: &mut KeccakState, data0: &[u8]) {
            absorb_final::<1, u64, 168, 0x1fu8>(&mut s.state, [data0]);
        }

        /// Squeeze three blocks
        #[inline(always)]
        pub fn shake128_squeeze_first_three_blocks(s: &mut KeccakState, out0: &mut [u8]) {
            squeeze_first_three_blocks::<1, u64, 168>(&mut s.state, [out0])
        }

        /// Squeeze five blocks
        #[inline(always)]
        pub fn shake128_squeeze_first_five_blocks(s: &mut KeccakState, out0: &mut [u8]) {
            squeeze_first_five_blocks::<1, u64, 168>(&mut s.state, [out0])
        }

        /// Squeeze another block
        #[inline(always)]
        pub fn shake128_squeeze_next_block(s: &mut KeccakState, out0: &mut [u8]) {
            squeeze_next_block::<1, u64, 168>(&mut s.state, [out0])
        }

        /// Create a new SHAKE-256 state object.
        #[inline(always)]
        pub fn shake256_init() -> KeccakState {
            KeccakState {
                state: GenericState::<1, u64>::new(),
            }
        }

        /// Absorb some data for SHAKE-256 for the last time
        #[inline(always)]
        pub fn shake256_absorb_final(s: &mut KeccakState, data: &[u8]) {
            absorb_final::<1, u64, 136, 0x1fu8>(&mut s.state, [data]);
        }

        /// Squeeze the first SHAKE-256 block
        #[inline(always)]
        pub fn shake256_squeeze_first_block(s: &mut KeccakState, out: &mut [u8]) {
            squeeze_first_block::<1, u64, 136>(&mut s.state, [out])
        }

        /// Squeeze the next SHAKE-256 block
        #[inline(always)]
        pub fn shake256_squeeze_next_block(s: &mut KeccakState, out: &mut [u8]) {
            squeeze_next_block::<1, u64, 136>(&mut s.state, [out])
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
    use crate::generic_keccak::keccak;

    #[cfg(feature = "simd128")]
    #[inline(always)]
    fn keccakx2<const RATE: usize, const DELIM: u8>(data: [&[u8]; 2], out: [&mut [u8]; 2]) {
        keccak::<2, crate::simd::arm64::uint64x2_t, RATE, DELIM>(data, out)
    }

    /// A portable SHA3 224 implementation.
    #[allow(unused_variables)]
    #[inline(always)]
    pub fn sha224(digest: &mut [u8], data: &[u8]) {
        #[cfg(not(feature = "simd128"))]
        unimplemented!();
        #[cfg(feature = "simd128")]
        {
            let mut dummy = [0u8; 28];
            keccakx2::<144, 0x06u8>([data, data], [digest, &mut dummy]);
        }
    }

    /// A portable SHA3 256 implementation.
    #[allow(unused_variables)]
    #[inline(always)]
    pub fn sha256(digest: &mut [u8], data: &[u8]) {
        #[cfg(not(feature = "simd128"))]
        unimplemented!();
        #[cfg(feature = "simd128")]
        {
            let mut dummy = [0u8; 32];
            keccakx2::<136, 0x06u8>([data, data], [digest, &mut dummy]);
        }
    }

    /// A portable SHA3 384 implementation.
    #[allow(unused_variables)]
    #[inline(always)]
    pub fn sha384(digest: &mut [u8], data: &[u8]) {
        #[cfg(not(feature = "simd128"))]
        unimplemented!();
        #[cfg(feature = "simd128")]
        {
            let mut dummy = [0u8; 48];
            keccakx2::<104, 0x06u8>([data, data], [digest, &mut dummy]);
        }
    }

    /// A portable SHA3 512 implementation.
    #[allow(unused_variables)]
    #[inline(always)]
    pub fn sha512(digest: &mut [u8], data: &[u8]) {
        #[cfg(not(feature = "simd128"))]
        unimplemented!();
        #[cfg(feature = "simd128")]
        {
            let mut dummy = [0u8; 64];
            keccakx2::<72, 0x06u8>([data, data], [digest, &mut dummy]);
        }
    }

    /// A portable SHAKE128 implementation.
    #[allow(unused_variables)]
    #[inline(always)]
    pub fn shake128<const LEN: usize>(digest: &mut [u8; LEN], data: &[u8]) {
        #[cfg(not(feature = "simd128"))]
        unimplemented!();
        #[cfg(feature = "simd128")]
        {
            let mut dummy = [0u8; LEN];
            keccakx2::<168, 0x1fu8>([data, data], [digest, &mut dummy]);
        }
    }

    /// A portable SHAKE256 implementation.
    #[allow(unused_variables)]
    #[inline(always)]
    pub fn shake256<const LEN: usize>(digest: &mut [u8; LEN], data: &[u8]) {
        #[cfg(not(feature = "simd128"))]
        unimplemented!();
        #[cfg(feature = "simd128")]
        {
            let mut dummy = [0u8; LEN];
            keccakx2::<136, 0x1fu8>([data, data], [digest, &mut dummy]);
        }
    }

    /// Performing 2 operations in parallel
    pub mod x2 {
        #[cfg(feature = "simd128")]
        use super::*;

        /// Run SHAKE256 on both inputs in parallel.
        ///
        /// Writes the two results into `out0` and `out1`
        #[allow(unused_variables)]
        #[inline(always)]
        pub fn shake256(input0: &[u8], input1: &[u8], out0: &mut [u8], out1: &mut [u8]) {
            // TODO: make argument ordering consistent
            #[cfg(not(feature = "simd128"))]
            unimplemented!();
            #[cfg(feature = "simd128")]
            keccakx2::<136, 0x1fu8>([input0, input1], [out0, out1]);
        }

        /// Run up to 4 SHAKE256 operations in parallel.
        ///
        /// **PANICS** when `N` is not 2, 3, or 4.
        #[allow(non_snake_case)]
        #[inline(always)]
        fn _shake256xN<const LEN: usize, const N: usize>(input: &[[u8; 33]; N]) -> [[u8; LEN]; N] {
            debug_assert!(N == 2 || N == 3 || N == 4);

            let mut out = [[0u8; LEN]; N];
            match N {
                2 => {
                    let (out0, out1) = out.split_at_mut(1);
                    shake256(&input[0], &input[1], &mut out0[0], &mut out1[0]);
                }
                3 => {
                    let mut extra = [0u8; LEN];
                    let (out0, out12) = out.split_at_mut(1);
                    let (out1, out2) = out12.split_at_mut(1);
                    shake256(&input[0], &input[1], &mut out0[0], &mut out1[0]);
                    shake256(&input[2], &input[2], &mut out2[0], &mut extra);
                }
                4 => {
                    let (out0, out123) = out.split_at_mut(1);
                    let (out1, out23) = out123.split_at_mut(1);
                    let (out2, out3) = out23.split_at_mut(1);
                    shake256(&input[0], &input[1], &mut out0[0], &mut out1[0]);
                    shake256(&input[2], &input[3], &mut out2[0], &mut out3[0]);
                }
                _ => unreachable!("Only 2, 3, or 4 are supported for N"),
            }
            out
        }

        /// An incremental API to perform 2 operations in parallel
        pub mod incremental {
            #[cfg(feature = "simd128")]
            use crate::generic_keccak::{
                absorb_final, squeeze_first_block, squeeze_first_five_blocks,
                squeeze_first_three_blocks, squeeze_next_block, KeccakState as GenericState,
            };

            /// The Keccak state for the incremental API.
            #[cfg(feature = "simd128")]
            pub struct KeccakState {
                state: GenericState<2, crate::simd::arm64::uint64x2_t>,
            }

            #[cfg(feature = "simd128")]
            type KeccakState2Internal = GenericState<2, crate::simd::arm64::uint64x2_t>;

            /// The Keccak state for the incremental API.
            #[allow(dead_code)]
            #[cfg(not(feature = "simd128"))]
            pub struct KeccakState {
                state: [crate::portable::KeccakState; 2],
            }

            /// Initialise the `KeccakState2`.
            #[inline(always)]
            pub fn init() -> KeccakState {
                #[cfg(not(feature = "simd128"))]
                unimplemented!();
                // XXX: These functions could alternatively implement the same with
                //      the portable implementation
                // {
                //     let s0 = KeccakState::new();
                //     let s1 = KeccakState::new();
                //     [s0, s1]
                // }
                #[cfg(feature = "simd128")]
                KeccakState {
                    state: KeccakState2Internal::new(),
                }
            }

            /// Shake128 absorb `data0` and `data1` in the [`KeccakState`] `s`.
            #[inline(always)]
            #[allow(unused_variables)]
            pub fn shake128_absorb_final(s: &mut KeccakState, data0: &[u8], data1: &[u8]) {
                #[cfg(not(feature = "simd128"))]
                unimplemented!();
                // XXX: These functions could alternatively implement the same with
                //      the portable implementation
                // {
                //     let [mut s0, mut s1] = s;
                //     shake128_absorb_final(&mut s0, data0);
                //     shake128_absorb_final(&mut s1, data1);
                // }
                #[cfg(feature = "simd128")]
                absorb_final::<2, crate::simd::arm64::uint64x2_t, 168, 0x1fu8>(
                    &mut s.state,
                    [data0, data1],
                );
            }

            /// Shake256 absorb `data0` and `data1` in the [`KeccakState`] `s`.
            #[inline(always)]
            #[allow(unused_variables)]
            pub fn shake256_absorb_final(s: &mut KeccakState, data0: &[u8], data1: &[u8]) {
                #[cfg(not(feature = "simd128"))]
                unimplemented!();
                // XXX: These functions could alternatively implement the same with
                //      the portable implementation
                // {
                //     let [mut s0, mut s1] = s;
                //     shake128_absorb_final(&mut s0, data0);
                //     shake128_absorb_final(&mut s1, data1);
                // }
                #[cfg(feature = "simd128")]
                absorb_final::<2, crate::simd::arm64::uint64x2_t, 136, 0x1fu8>(
                    &mut s.state,
                    [data0, data1],
                );
            }

            /// Initialise the state and perform up to 4 absorbs at the same time,
            /// using two [`KeccakState2`].
            ///
            /// **PANICS** when `N` is not 2, 3, or 4.
            #[allow(unused_variables, non_snake_case)]
            #[inline(always)]
            fn _shake128_absorb_finalxN<const N: usize>(input: [[u8; 34]; N]) -> [KeccakState; 2] {
                debug_assert!(N == 2 || N == 3 || N == 4);
                let mut state = [init(), init()];

                match N {
                    2 => {
                        shake128_absorb_final(&mut state[0], &input[0], &input[1]);
                    }
                    3 => {
                        shake128_absorb_final(&mut state[0], &input[0], &input[1]);
                        shake128_absorb_final(&mut state[1], &input[2], &input[2]);
                    }
                    4 => {
                        shake128_absorb_final(&mut state[0], &input[0], &input[1]);
                        shake128_absorb_final(&mut state[1], &input[2], &input[3]);
                    }
                    _ => unreachable!("This function can only called be called with N = 2, 3, 4"),
                }

                state
            }

            /// Squeeze 2 times the first three blocks in parallel in the
            /// [`KeccakState`] and return the output in `out0` and `out1`.
            #[allow(unused_variables)]
            #[inline(always)]
            pub fn shake128_squeeze_first_three_blocks(
                s: &mut KeccakState,
                out0: &mut [u8],
                out1: &mut [u8],
            ) {
                #[cfg(not(feature = "simd128"))]
                unimplemented!();
                // XXX: These functions could alternatively implement the same with
                //      the portable implementation
                // {
                //     let [mut s0, mut s1] = s;
                //     shake128_squeeze_first_three_blocks(&mut s0, out0);
                //     shake128_squeeze_first_three_blocks(&mut s1, out1);
                // }
                #[cfg(feature = "simd128")]
                squeeze_first_three_blocks::<2, crate::simd::arm64::uint64x2_t, 168>(
                    &mut s.state,
                    [out0, out1],
                )
            }

            /// Squeeze five blocks
            #[allow(unused_variables)]
            #[inline(always)]
            pub fn shake128_squeeze_first_five_blocks(
                s: &mut KeccakState,
                out0: &mut [u8],
                out1: &mut [u8],
            ) {
                #[cfg(not(feature = "simd128"))]
                unimplemented!();
                #[cfg(feature = "simd128")]
                squeeze_first_five_blocks::<2, crate::simd::arm64::uint64x2_t, 168>(
                    &mut s.state,
                    [out0, out1],
                )
            }

            /// Squeeze block
            #[inline(always)]
            #[allow(unused_variables)] // TODO: decide if we want to fall back here
            pub fn shake256_squeeze_first_block(
                s: &mut KeccakState,
                out0: &mut [u8],
                out1: &mut [u8],
            ) {
                #[cfg(not(feature = "simd128"))]
                unimplemented!();
                #[cfg(feature = "simd128")]
                squeeze_first_block::<2, crate::simd::arm64::uint64x2_t, 136>(
                    &mut s.state,
                    [out0, out1],
                );
            }

            /// Squeeze next block
            #[inline(always)]
            #[allow(unused_variables)] // TODO: decide if we want to fall back here
            pub fn shake256_squeeze_next_block(
                s: &mut KeccakState,
                out0: &mut [u8],
                out1: &mut [u8],
            ) {
                #[cfg(not(feature = "simd128"))]
                unimplemented!();
                #[cfg(feature = "simd128")]
                squeeze_next_block::<2, crate::simd::arm64::uint64x2_t, 136>(
                    &mut s.state,
                    [out0, out1],
                );
            }

            /// Squeeze up to 3 x 4 (N) blocks in parallel, using two [`KeccakState2`].
            /// Each block is of size `LEN`.
            ///
            /// **PANICS** when `N` is not 2, 3, or 4.
            #[allow(unused_variables, non_snake_case)]
            #[inline(always)]
            fn _shake128_squeeze3xN<const LEN: usize, const N: usize>(
                state: &mut [KeccakState; 2],
            ) -> [[u8; LEN]; N] {
                debug_assert!(N == 2 || N == 3 || N == 4);

                let mut out = [[0u8; LEN]; N];
                match N {
                    2 => {
                        let (out0, out1) = out.split_at_mut(1);
                        shake128_squeeze_first_three_blocks(
                            &mut state[0],
                            &mut out0[0],
                            &mut out1[0],
                        );
                    }
                    3 => {
                        let mut extra = [0u8; LEN];
                        let (out0, out12) = out.split_at_mut(1);
                        let (out1, out2) = out12.split_at_mut(1);
                        shake128_squeeze_first_three_blocks(
                            &mut state[0],
                            &mut out0[0],
                            &mut out1[0],
                        );
                        shake128_squeeze_first_three_blocks(
                            &mut state[1],
                            &mut out2[0],
                            &mut extra,
                        );
                    }
                    4 => {
                        let (out0, out123) = out.split_at_mut(1);
                        let (out1, out23) = out123.split_at_mut(1);
                        let (out2, out3) = out23.split_at_mut(1);
                        shake128_squeeze_first_three_blocks(
                            &mut state[0],
                            &mut out0[0],
                            &mut out1[0],
                        );
                        shake128_squeeze_first_three_blocks(
                            &mut state[1],
                            &mut out2[0],
                            &mut out3[0],
                        );
                    }
                    _ => unreachable!("This function can only called be called with N = 2, 3, 4"),
                }
                out
            }

            /// Squeeze 2 times the next block in parallel in the
            /// [`KeccakState`] and return the output in `out0` and `out1`.
            #[allow(unused_variables)]
            #[inline(always)]
            pub fn shake128_squeeze_next_block(
                s: &mut KeccakState,
                out0: &mut [u8],
                out1: &mut [u8],
            ) {
                #[cfg(not(feature = "simd128"))]
                unimplemented!();
                // XXX: These functions could alternatively implement the same with
                //      the portable implementation
                // {
                //     let [mut s0, mut s1] = s;
                //     shake128_squeeze_next_block(&mut s0, out0);
                //     shake128_squeeze_next_block(&mut s1, out1);
                // }
                #[cfg(feature = "simd128")]
                squeeze_next_block::<2, crate::simd::arm64::uint64x2_t, 168>(
                    &mut s.state,
                    [out0, out1],
                )
            }

            /// Squeeze up to 4 (N) blocks in parallel, using two [`KeccakState2`].
            /// Each block is of size `LEN`.
            ///
            /// **PANICS** when `N` is not 2, 3, or 4.
            #[allow(unused_variables, non_snake_case)]
            #[inline(always)]
            fn _shake128_squeezexN<const LEN: usize, const N: usize>(
                state: &mut [KeccakState; 2],
            ) -> [[u8; LEN]; N] {
                debug_assert!(N == 2 || N == 3 || N == 4);

                let mut out = [[0u8; LEN]; N];
                match N {
                    2 => {
                        let mut out0 = [0u8; LEN];
                        let mut out1 = [0u8; LEN];
                        shake128_squeeze_next_block(&mut state[0], &mut out0, &mut out1);
                        out[0] = out0;
                        out[1] = out1;
                    }
                    3 => {
                        let mut out0 = [0u8; LEN];
                        let mut out1 = [0u8; LEN];
                        let mut out2 = [0u8; LEN];
                        let mut out3 = [0u8; LEN];
                        shake128_squeeze_next_block(&mut state[0], &mut out0, &mut out1);
                        shake128_squeeze_next_block(&mut state[1], &mut out2, &mut out3);
                        out[0] = out0;
                        out[1] = out1;
                        out[2] = out2;
                    }
                    4 => {
                        let mut out0 = [0u8; LEN];
                        let mut out1 = [0u8; LEN];
                        let mut out2 = [0u8; LEN];
                        let mut out3 = [0u8; LEN];
                        shake128_squeeze_next_block(&mut state[0], &mut out0, &mut out1);
                        shake128_squeeze_next_block(&mut state[1], &mut out2, &mut out3);
                        out[0] = out0;
                        out[1] = out1;
                        out[2] = out2;
                        out[3] = out3;
                    }
                    _ => unreachable!("This function is only called with N = 2, 3, 4"),
                }
                out
            }
        }
    }
}

/// An AVX2 optimised implementation.
///
/// When this is compiled for non-neon architectures, the functions panic.
/// The caller must make sure to check for hardware feature before calling these
/// functions and compile them in.
///
/// Feature `simd256` enables the implementations in this module.
pub mod avx2 {

    /// Performing 4 operations in parallel
    pub mod x4 {
        #[cfg(feature = "simd256")]
        use crate::generic_keccak::keccak;
        #[cfg(feature = "simd256")]
        use libcrux_intrinsics::avx2::*;

        /// Perform 4 SHAKE256 operations in parallel
        #[allow(unused_variables, clippy::too_many_arguments)] // TODO: decide if we want to fall back here
        #[inline(always)]
        pub fn shake256(
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
            unimplemented!();
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
            keccak::<4, Vec256, 136, 0x1fu8>(
                [input0, input1, input2, input3],
                [out0, out1, out2, out3],
            );
        }

        /// Run up to 4 SHAKE256 operations in parallel.
        ///
        /// **PANICS** when `N` is not 2, 3, or 4.
        #[allow(unused_variables, non_snake_case)]
        #[inline(always)]
        fn _shake256xN<const LEN: usize, const N: usize>(input: &[[u8; 33]; N]) -> [[u8; LEN]; N] {
            debug_assert!(N == 2 || N == 3 || N == 4);
            let mut out = [[0u8; LEN]; N];

            match N {
                2 => {
                    let mut dummy_out0 = [0u8; LEN];
                    let mut dummy_out1 = [0u8; LEN];
                    let (out0, out1) = out.split_at_mut(1);
                    shake256(
                        &input[0],
                        &input[1],
                        &input[0],
                        &input[0],
                        &mut out0[0],
                        &mut out1[0],
                        &mut dummy_out0,
                        &mut dummy_out1,
                    );
                }
                3 => {
                    let mut dummy_out0 = [0u8; LEN];
                    let (out0, out12) = out.split_at_mut(1);
                    let (out1, out2) = out12.split_at_mut(1);
                    shake256(
                        &input[0],
                        &input[1],
                        &input[2],
                        &input[0],
                        &mut out0[0],
                        &mut out1[0],
                        &mut out2[0],
                        &mut dummy_out0,
                    );
                }
                4 => {
                    let (out0, out123) = out.split_at_mut(1);
                    let (out1, out23) = out123.split_at_mut(1);
                    let (out2, out3) = out23.split_at_mut(1);
                    shake256(
                        &input[0],
                        &input[1],
                        &input[2],
                        &input[3],
                        &mut out0[0],
                        &mut out1[0],
                        &mut out2[0],
                        &mut out3[0],
                    );
                }
                _ => unreachable!("This function must only be called with N = 2, 3, 4"),
            }
            out
        }

        /// An incremental API to perform 4 operations in parallel
        pub mod incremental {
            #[cfg(feature = "simd256")]
            use crate::generic_keccak::{
                absorb_final, squeeze_first_three_blocks, squeeze_next_block,
                KeccakState as GenericState,
            };
            #[cfg(feature = "simd256")]
            use crate::generic_keccak::{squeeze_first_block, squeeze_first_five_blocks};
            #[cfg(feature = "simd256")]
            use libcrux_intrinsics::avx2::*;

            /// The Keccak state for the incremental API.
            #[cfg(feature = "simd256")]
            pub struct KeccakState {
                state: GenericState<4, Vec256>,
            }

            /// The Keccak state for the incremental API.
            #[allow(dead_code)]
            #[cfg(all(feature = "simd128", not(feature = "simd256")))]
            pub struct KeccakState {
                state: [crate::neon::x2::incremental::KeccakState; 2],
            }

            /// The Keccak state for the incremental API.
            #[cfg(not(any(feature = "simd256", feature = "simd128")))]
            pub type KeccakState = [crate::portable::KeccakState; 4];

            /// Initialise the [`KeccakState`].
            #[inline(always)]
            pub fn init() -> KeccakState {
                #[cfg(not(feature = "simd256"))]
                unimplemented!();
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
                //     let s0 = KeccakState::new();
                //     let s1 = KeccakState::new();
                //     let s2 = KeccakState::new();
                //     let s3 = KeccakState::new();
                //     [s0, s1, s2, s3]
                // }
                #[cfg(feature = "simd256")]
                KeccakState {
                    state: GenericState::new(),
                }
            }

            /// Absorb
            #[inline(always)]
            #[allow(unused_variables)] // TODO: decide if we want to fall back here
            pub fn shake128_absorb_final(
                s: &mut KeccakState,
                data0: &[u8],
                data1: &[u8],
                data2: &[u8],
                data3: &[u8],
            ) {
                #[cfg(not(feature = "simd256"))]
                unimplemented!();
                // XXX: These functions could alternatively implement the same with
                //      the portable implementation
                // #[cfg(feature = "simd128")]
                // {
                //     let [mut s0, mut s1] = s;
                //     absorb_final::<2, crate::simd::arm64::uint64x2_t, 168, 0x1fu8>(
                //         &mut s0,
                //         [data0, data1],
                //     );
                //     absorb_final::<2, crate::simd::arm64::uint64x2_t, 168, 0x1fu8>(
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
                absorb_final::<4, Vec256, 168, 0x1fu8>(&mut s.state, [data0, data1, data2, data3]);
            }

            /// Absorb
            #[inline(always)]
            #[allow(unused_variables)] // TODO: decide if we want to fall back here
            pub fn shake256_absorb_final(
                s: &mut KeccakState,
                data0: &[u8],
                data1: &[u8],
                data2: &[u8],
                data3: &[u8],
            ) {
                #[cfg(not(feature = "simd256"))]
                unimplemented!();
                #[cfg(feature = "simd256")]
                absorb_final::<4, Vec256, 136, 0x1fu8>(&mut s.state, [data0, data1, data2, data3]);
            }

            /// Squeeze block
            #[inline(always)]
            #[allow(unused_variables)] // TODO: decide if we want to fall back here
            pub fn shake256_squeeze_first_block(
                s: &mut KeccakState,
                out0: &mut [u8],
                out1: &mut [u8],
                out2: &mut [u8],
                out3: &mut [u8],
            ) {
                #[cfg(not(feature = "simd256"))]
                unimplemented!();
                #[cfg(feature = "simd256")]
                squeeze_first_block::<4, Vec256, 136>(&mut s.state, [out0, out1, out2, out3]);
            }

            /// Squeeze next block
            #[inline(always)]
            #[allow(unused_variables)] // TODO: decide if we want to fall back here
            pub fn shake256_squeeze_next_block(
                s: &mut KeccakState,
                out0: &mut [u8],
                out1: &mut [u8],
                out2: &mut [u8],
                out3: &mut [u8],
            ) {
                #[cfg(not(feature = "simd256"))]
                unimplemented!();
                #[cfg(feature = "simd256")]
                squeeze_next_block::<4, Vec256, 136>(&mut s.state, [out0, out1, out2, out3]);
            }

            /// Initialise the state and perform up to 4 absorbs at the same time,
            /// using two [`KeccakState`].
            ///
            /// **PANICS** when `N` is not 2, 3, or 4.
            #[inline(always)]
            #[allow(unused_variables, non_snake_case)]
            fn _shake128_absorb_finalxN<const N: usize>(input: [[u8; 34]; N]) -> KeccakState {
                debug_assert!(N == 2 || N == 3 || N == 4);
                let mut state = init();

                match N {
                    2 => {
                        shake128_absorb_final(
                            &mut state, &input[0], &input[1], &input[0], &input[0],
                        );
                    }
                    3 => {
                        shake128_absorb_final(
                            &mut state, &input[0], &input[1], &input[2], &input[0],
                        );
                    }
                    4 => {
                        shake128_absorb_final(
                            &mut state, &input[0], &input[1], &input[2], &input[3],
                        );
                    }
                    _ => unreachable!("This function must only be called with N = 2, 3, 4"),
                }

                state
            }

            /// Squeeze three blocks
            #[inline(always)]
            #[allow(unused_variables)] // TODO: decide if we want to fall back here
            pub fn shake128_squeeze_first_three_blocks(
                s: &mut KeccakState,
                out0: &mut [u8],
                out1: &mut [u8],
                out2: &mut [u8],
                out3: &mut [u8],
            ) {
                #[cfg(not(feature = "simd256"))]
                unimplemented!();
                // XXX: These functions could alternatively implement the same with
                //      the portable implementation
                // #[cfg(feature = "simd128")]
                // {
                //     let [mut s0, mut s1] = s;
                //     squeeze_first_three_blocks::<2, crate::simd::arm64::uint64x2_t, 168>(
                //         &mut s0,
                //         [out0, out1],
                //     );
                //     squeeze_first_three_blocks::<2, crate::simd::arm64::uint64x2_t, 168>(
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
                squeeze_first_three_blocks::<4, Vec256, 168>(
                    &mut s.state,
                    [out0, out1, out2, out3],
                );
            }

            /// Squeeze five blocks
            #[inline(always)]
            #[allow(unused_variables)] // TODO: decide if we want to fall back here
            pub fn shake128_squeeze_first_five_blocks(
                s: &mut KeccakState,
                out0: &mut [u8],
                out1: &mut [u8],
                out2: &mut [u8],
                out3: &mut [u8],
            ) {
                #[cfg(not(feature = "simd256"))]
                unimplemented!();
                #[cfg(feature = "simd256")]
                squeeze_first_five_blocks::<4, Vec256, 168>(&mut s.state, [out0, out1, out2, out3]);
            }

            /// Squeeze up to 3 x 4 (N) blocks in parallel, using two [`KeccakState`].
            /// Each block is of size `LEN`.
            ///
            /// **PANICS** when `N` is not 2, 3, or 4.
            #[inline(always)]
            #[allow(unused_variables, non_snake_case)]
            fn _shake128_squeeze3xN<const LEN: usize, const N: usize>(
                state: &mut KeccakState,
            ) -> [[u8; LEN]; N] {
                debug_assert!(N == 2 || N == 3 || N == 4);

                let mut out = [[0u8; LEN]; N];
                match N {
                    2 => {
                        let mut dummy_out0 = [0u8; LEN];
                        let mut dummy_out1 = [0u8; LEN];
                        let (out0, out1) = out.split_at_mut(1);
                        shake128_squeeze_first_three_blocks(
                            state,
                            &mut out0[0],
                            &mut out1[0],
                            &mut dummy_out0,
                            &mut dummy_out1,
                        );
                    }
                    3 => {
                        let mut dummy_out0 = [0u8; LEN];
                        let (out0, out12) = out.split_at_mut(1);
                        let (out1, out2) = out12.split_at_mut(1);
                        shake128_squeeze_first_three_blocks(
                            state,
                            &mut out0[0],
                            &mut out1[0],
                            &mut out2[0],
                            &mut dummy_out0,
                        );
                    }
                    4 => {
                        let (out0, out123) = out.split_at_mut(1);
                        let (out1, out23) = out123.split_at_mut(1);
                        let (out2, out3) = out23.split_at_mut(1);
                        shake128_squeeze_first_three_blocks(
                            state,
                            &mut out0[0],
                            &mut out1[0],
                            &mut out2[0],
                            &mut out3[0],
                        );
                    }
                    _ => unreachable!("This function must only be called with N = 2, 3, 4"),
                }
                out
            }

            /// Squeeze another block
            #[inline(always)]
            #[allow(unused_variables)] // TODO: decide if we want to fall back here
            pub fn shake128_squeeze_next_block(
                s: &mut KeccakState,
                out0: &mut [u8],
                out1: &mut [u8],
                out2: &mut [u8],
                out3: &mut [u8],
            ) {
                #[cfg(not(feature = "simd256"))]
                unimplemented!();
                // XXX: These functions could alternatively implement the same with
                //      the portable implementation
                // #[cfg(feature = "simd128")]
                // {
                //     let [mut s0, mut s1] = s;
                //     squeeze_next_block::<2, crate::simd::arm64::uint64x2_t, 168>(
                //         &mut s0,
                //         [out0, out1],
                //     );
                //     squeeze_next_block::<2, crate::simd::arm64::uint64x2_t, 168>(
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
                squeeze_next_block::<4, Vec256, 168>(&mut s.state, [out0, out1, out2, out3]);
            }

            /// Squeeze up to 4 (N) blocks in parallel, using two [`KeccakState`].
            /// Each block is of size `LEN`.
            ///
            /// **PANICS** when `N` is not 2, 3, or 4.
            #[allow(unused_variables, non_snake_case)]
            #[inline(always)]
            fn _shake128_squeezexN<const LEN: usize, const N: usize>(
                state: &mut KeccakState,
            ) -> [[u8; LEN]; N] {
                debug_assert!(N == 2 || N == 3 || N == 4);

                let mut out = [[0u8; LEN]; N];
                match N {
                    2 => {
                        let mut dummy_out0 = [0u8; LEN];
                        let mut dummy_out1 = [0u8; LEN];
                        let (out0, out1) = out.split_at_mut(1);
                        shake128_squeeze_next_block(
                            state,
                            &mut out0[0],
                            &mut out1[0],
                            &mut dummy_out0,
                            &mut dummy_out1,
                        );
                    }
                    3 => {
                        let mut dummy_out0 = [0u8; LEN];
                        let (out0, out12) = out.split_at_mut(1);
                        let (out1, out2) = out12.split_at_mut(1);
                        shake128_squeeze_next_block(
                            state,
                            &mut out0[0],
                            &mut out1[0],
                            &mut out2[0],
                            &mut dummy_out0,
                        );
                    }
                    4 => {
                        let (out0, out123) = out.split_at_mut(1);
                        let (out1, out23) = out123.split_at_mut(1);
                        let (out2, out3) = out23.split_at_mut(1);
                        shake128_squeeze_next_block(
                            state,
                            &mut out0[0],
                            &mut out1[0],
                            &mut out2[0],
                            &mut out3[0],
                        );
                    }
                    _ => unreachable!("This function is only called with 2, 3, 4"),
                }
                out
            }
        }
    }
}
