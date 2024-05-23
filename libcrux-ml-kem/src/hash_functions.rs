#![allow(non_snake_case)]

use crate::constants::{G_DIGEST_SIZE, H_DIGEST_SIZE};

/// The SHA3 block size.
pub(crate) const BLOCK_SIZE: usize = 168;

/// The size of 3 SHA3 blocks.
pub(crate) const THREE_BLOCKS: usize = BLOCK_SIZE * 3;

/// Abstraction for the hashing, to pick the fastest version depending on the
/// platform features available.
///
/// There are 3 instantiations of this trait right now, using the libcrux-sha3 crate.
/// - AVX2
/// - NEON
/// - Portable
pub(crate) trait Hash<const K: usize> {
    /// G aka SHA3 512
    fn G(input: &[u8]) -> [u8; G_DIGEST_SIZE];

    /// H aka SHA3 256
    fn H(input: &[u8]) -> [u8; H_DIGEST_SIZE];

    /// PRF aka SHAKE256
    fn PRF<const LEN: usize>(input: &[u8]) -> [u8; LEN];

    /// PRFxN aka N SHAKE256
    fn PRFxN<const LEN: usize>(input: &[[u8; 33]; K]) -> [[u8; LEN]; K];

    /// Create a SHAKE128 state and absorb the input.
    fn shake128_init_absorb(input: [[u8; 34]; K]) -> Self;

    /// Squeeze 3 blocks out of the SHAKE128 state.
    fn shake128_squeeze_three_blocks(&mut self) -> [[u8; THREE_BLOCKS]; K];

    /// Squeeze 1 block out of the SHAKE128 state.
    fn shake128_squeeze_block(&mut self) -> [[u8; BLOCK_SIZE]; K];
}

/// A portable implementation of [`Hash`]
pub(crate) mod portable {
    use super::*;
    use libcrux_sha3::portable::{
        self,
        incremental::{
            shake128_absorb_final, shake128_init, shake128_squeeze_first_three_blocks,
            shake128_squeeze_next_block,
        },
        KeccakState1,
    };

    /// The state.
    ///
    /// It's only used for SHAKE128.
    /// All other functions don't actually use any members.
    pub(crate) struct PortableHash<const K: usize> {
        shake128_state: [KeccakState1; K],
    }

    impl<const K: usize> Hash<K> for PortableHash<K> {
        #[inline(always)]
        fn G(input: &[u8]) -> [u8; G_DIGEST_SIZE] {
            let mut digest = [0u8; G_DIGEST_SIZE];
            portable::sha512(&mut digest, input);
            digest
        }

        #[inline(always)]
        fn H(input: &[u8]) -> [u8; H_DIGEST_SIZE] {
            let mut digest = [0u8; H_DIGEST_SIZE];
            portable::sha256(&mut digest, input);
            digest
        }

        #[inline(always)]
        fn PRF<const LEN: usize>(input: &[u8]) -> [u8; LEN] {
            let mut digest = [0u8; LEN];
            portable::shake256(&mut digest, input);
            digest
        }

        #[inline(always)]
        fn PRFxN<const LEN: usize>(input: &[[u8; 33]; K]) -> [[u8; LEN]; K] {
            debug_assert!(K == 2 || K == 3 || K == 4);

            let mut out = [[0u8; LEN]; K];
            for i in 0..K {
                portable::shake256::<LEN>(&mut out[i], &input[i]);
            }
            out
        }

        #[inline(always)]
        fn shake128_init_absorb(input: [[u8; 34]; K]) -> Self {
            debug_assert!(K == 2 || K == 3 || K == 4);

            let mut state = [shake128_init(); K];
            for i in 0..K {
                shake128_absorb_final(&mut state[i], &input[i]);
            }
            Self {
                shake128_state: state,
            }
        }

        #[inline(always)]
        fn shake128_squeeze_three_blocks(&mut self) -> [[u8; THREE_BLOCKS]; K] {
            debug_assert!(K == 2 || K == 3 || K == 4);

            let mut out = [[0u8; THREE_BLOCKS]; K];
            for i in 0..K {
                shake128_squeeze_first_three_blocks(&mut self.shake128_state[i], &mut out[i]);
            }
            out
        }

        #[inline(always)]
        fn shake128_squeeze_block(&mut self) -> [[u8; BLOCK_SIZE]; K] {
            debug_assert!(K == 2 || K == 3 || K == 4);

            let mut out = [[0u8; BLOCK_SIZE]; K];
            for i in 0..K {
                shake128_squeeze_next_block(&mut self.shake128_state[i], &mut out[i]);
            }
            out
        }
    }
}

/// A SIMD256 implementation of [`Hash`] for AVX2
pub(crate) mod avx2 {
    use super::*;
    use libcrux_sha3::{
        avx2::x4::{self, incremental::KeccakState4},
        portable,
    };

    /// The state.
    ///
    /// It's only used for SHAKE128.
    /// All other functions don't actually use any members.
    pub(crate) struct Simd256Hash {
        shake128_state: KeccakState4,
    }

    impl<const K: usize> Hash<K> for Simd256Hash {
        #[inline(always)]
        fn G(input: &[u8]) -> [u8; G_DIGEST_SIZE] {
            let mut digest = [0u8; G_DIGEST_SIZE];
            portable::sha512(&mut digest, input);
            digest
        }

        #[inline(always)]
        fn H(input: &[u8]) -> [u8; H_DIGEST_SIZE] {
            let mut digest = [0u8; H_DIGEST_SIZE];
            portable::sha256(&mut digest, input);
            digest
        }

        #[inline(always)]
        fn PRF<const LEN: usize>(input: &[u8]) -> [u8; LEN] {
            let mut digest = [0u8; LEN];
            portable::shake256(&mut digest, input);
            digest
        }

        #[inline(always)]
        fn PRFxN<const LEN: usize>(input: &[[u8; 33]; K]) -> [[u8; LEN]; K] {
            debug_assert!(K == 2 || K == 3 || K == 4);
            x4::shake256xN(input)
        }

        #[inline(always)]
        fn shake128_init_absorb(input: [[u8; 34]; K]) -> Self {
            debug_assert!(K == 2 || K == 3 || K == 4);
            let state = x4::incremental::shake128_absorb_finalxN(input);

            Self {
                shake128_state: state,
            }
        }

        #[inline(always)]
        fn shake128_squeeze_three_blocks(&mut self) -> [[u8; THREE_BLOCKS]; K] {
            debug_assert!(K == 2 || K == 3 || K == 4);
            x4::incremental::shake128_squeeze3xN(&mut self.shake128_state)
        }

        #[inline(always)]
        fn shake128_squeeze_block(&mut self) -> [[u8; BLOCK_SIZE]; K] {
            debug_assert!(K == 2 || K == 3 || K == 4);
            x4::incremental::shake128_squeezexN(&mut self.shake128_state)
        }
    }
}

/// A SIMD128 implementation of [`Hash`] for NEON
pub(crate) mod neon {
    use super::*;
    use libcrux_sha3::neon::x2::{self, incremental::KeccakState2};

    /// The state.
    ///
    /// It's only used for SHAKE128.
    /// All other functions don't actually use any members.
    pub(crate) struct Simd128Hash {
        shake128_state: [KeccakState2; 2],
    }

    impl<const K: usize> Hash<K> for Simd128Hash {
        #[inline(always)]
        fn G(input: &[u8]) -> [u8; G_DIGEST_SIZE] {
            let mut digest = [0u8; G_DIGEST_SIZE];
            libcrux_sha3::neon::sha512(&mut digest, input);
            digest
        }

        #[inline(always)]
        fn H(input: &[u8]) -> [u8; H_DIGEST_SIZE] {
            let mut digest = [0u8; H_DIGEST_SIZE];
            libcrux_sha3::neon::sha256(&mut digest, input);
            digest
        }

        #[inline(always)]
        fn PRF<const LEN: usize>(input: &[u8]) -> [u8; LEN] {
            let mut digest = [0u8; LEN];
            libcrux_sha3::neon::shake256(&mut digest, input);
            digest
        }

        #[inline(always)]
        fn PRFxN<const LEN: usize>(input: &[[u8; 33]; K]) -> [[u8; LEN]; K] {
            debug_assert!(K == 2 || K == 3 || K == 4);
            x2::shake256xN(input)
        }

        #[inline(always)]
        fn shake128_init_absorb(input: [[u8; 34]; K]) -> Self {
            debug_assert!(K == 2 || K == 3 || K == 4);
            let state = x2::incremental::shake128_absorb_finalxN(input);

            Self {
                shake128_state: state,
            }
        }

        #[inline(always)]
        fn shake128_squeeze_three_blocks(&mut self) -> [[u8; THREE_BLOCKS]; K] {
            debug_assert!(K == 2 || K == 3 || K == 4);
            x2::incremental::shake128_squeeze3xN(&mut self.shake128_state)
        }

        #[inline(always)]
        fn shake128_squeeze_block(&mut self) -> [[u8; BLOCK_SIZE]; K] {
            debug_assert!(K == 2 || K == 3 || K == 4);
            x2::incremental::shake128_squeezexN(&mut self.shake128_state)
        }
    }
}
