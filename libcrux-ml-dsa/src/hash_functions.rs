#![allow(non_snake_case)]

/// Abstraction and platform multiplexing for SHAKE 256
pub(crate) mod shake256 {
    pub(crate) const BLOCK_SIZE: usize = 136;

    pub(crate) trait Xof {
        fn shake256<const OUTPUT_LENGTH: usize>(input: &[u8]) -> [u8; OUTPUT_LENGTH];
        fn init_absorb(input: &[u8]) -> Self;
        // TODO: There should only be a `squeeze_block`
        fn squeeze_first_block(&mut self) -> [u8; BLOCK_SIZE];
        fn squeeze_next_block(&mut self) -> [u8; BLOCK_SIZE];
    }
}

/// Abstraction and platform multiplexing for SHAKE 128
pub(crate) mod shake128 {
    pub(crate) const BLOCK_SIZE: usize = 168;
    pub(crate) const FIVE_BLOCKS_SIZE: usize = BLOCK_SIZE * 5;

    pub(crate) trait Xof {
        fn init_absorb(input: &[u8]) -> Self;
        // TODO:
        // - There should only be a `squeeze_block` and `squeeze_five_blocks`
        // - Use mutable out instead if performance is better
        fn squeeze_first_five_blocks(&mut self) -> [u8; FIVE_BLOCKS_SIZE];
        fn squeeze_next_block(&mut self) -> [u8; BLOCK_SIZE];
    }
}

/// A portable implementation of [`shake128::Xof`] and [`shake256::Xof`].
pub(crate) mod portable {
    use libcrux_sha3::portable::{
        incremental::{self, shake128_absorb_final, shake128_init},
        shake256, KeccakState,
    };

    use super::{shake128, shake256};

    /// Portable SHAKE 128 state
    pub(crate) struct PortableShake128 {
        state: KeccakState,
    }

    impl shake128::Xof for PortableShake128 {
        #[inline(always)]
        fn init_absorb(input: &[u8]) -> Self {
            let mut state = shake128_init();
            shake128_absorb_final(&mut state, &input);

            Self { state }
        }

        #[inline(always)]
        fn squeeze_first_five_blocks(&mut self) -> [u8; shake128::FIVE_BLOCKS_SIZE] {
            let mut out = [0u8; shake128::FIVE_BLOCKS_SIZE];
            incremental::shake128_squeeze_first_five_blocks(&mut self.state, &mut out);
            out
        }

        #[inline(always)]
        fn squeeze_next_block(&mut self) -> [u8; shake128::BLOCK_SIZE] {
            let mut out = [0u8; shake128::BLOCK_SIZE];
            incremental::shake128_squeeze_next_block(&mut self.state, &mut out);
            out
        }
    }

    /// Portable SHAKE 256 state
    pub(crate) struct PortableShake256 {
        state: KeccakState,
    }
    impl shake256::Xof for PortableShake256 {
        fn shake256<const OUTPUT_LENGTH: usize>(input: &[u8]) -> [u8; OUTPUT_LENGTH] {
            let mut out = [0u8; OUTPUT_LENGTH];
            shake256(&mut out, input);
            out
        }

        fn init_absorb(input: &[u8]) -> Self {
            let mut state = incremental::shake256_init();
            incremental::shake256_absorb_final(&mut state, input);

            Self { state }
        }

        fn squeeze_first_block(&mut self) -> [u8; shake256::BLOCK_SIZE] {
            let mut out = [0u8; shake256::BLOCK_SIZE];
            incremental::shake256_squeeze_first_block(&mut self.state, &mut out);
            out
        }

        fn squeeze_next_block(&mut self) -> [u8; shake256::BLOCK_SIZE] {
            let mut out = [0u8; shake256::BLOCK_SIZE];
            incremental::shake256_squeeze_next_block(&mut self.state, &mut out);
            out
        }
    }
}

/// A SIMD256 implementation of [`shake128::Xof`] and [`shake256::Xof`] for AVX2.
pub(crate) mod simd256 {
    // FIXME: This is only a portable implementation for now.

    use libcrux_sha3::portable::{
        incremental::{self, shake128_absorb_final, shake128_init},
        shake256, KeccakState,
    };

    use super::{shake128, shake256};

    /// Portable SHAKE 128 state
    pub(crate) struct PortableShake128 {
        state: KeccakState,
    }

    impl shake128::Xof for PortableShake128 {
        #[inline(always)]
        fn init_absorb(input: &[u8]) -> Self {
            let mut state = shake128_init();
            shake128_absorb_final(&mut state, &input);

            Self { state }
        }

        #[inline(always)]
        fn squeeze_first_five_blocks(&mut self) -> [u8; shake128::FIVE_BLOCKS_SIZE] {
            let mut out = [0u8; shake128::FIVE_BLOCKS_SIZE];
            incremental::shake128_squeeze_first_five_blocks(&mut self.state, &mut out);
            out
        }

        #[inline(always)]
        fn squeeze_next_block(&mut self) -> [u8; shake128::BLOCK_SIZE] {
            let mut out = [0u8; shake128::BLOCK_SIZE];
            incremental::shake128_squeeze_next_block(&mut self.state, &mut out);
            out
        }
    }

    /// Portable SHAKE 256 state
    pub(crate) struct PortableShake256 {
        state: KeccakState,
    }
    impl shake256::Xof for PortableShake256 {
        fn shake256<const OUTPUT_LENGTH: usize>(input: &[u8]) -> [u8; OUTPUT_LENGTH] {
            let mut out = [0u8; OUTPUT_LENGTH];
            shake256(&mut out, input);
            out
        }

        fn init_absorb(input: &[u8]) -> Self {
            let mut state = incremental::shake256_init();
            incremental::shake256_absorb_final(&mut state, input);

            Self { state }
        }

        fn squeeze_first_block(&mut self) -> [u8; shake256::BLOCK_SIZE] {
            let mut out = [0u8; shake256::BLOCK_SIZE];
            incremental::shake256_squeeze_first_block(&mut self.state, &mut out);
            out
        }

        fn squeeze_next_block(&mut self) -> [u8; shake256::BLOCK_SIZE] {
            let mut out = [0u8; shake256::BLOCK_SIZE];
            incremental::shake256_squeeze_next_block(&mut self.state, &mut out);
            out
        }
    }
}

/// A SIMD256 implementation of [`shake128::Xof`] and [`shake256::Xof`] for Neon.
pub(crate) mod neon {
    // FIXME: This is only a portable implementation for now.

    use libcrux_sha3::portable::{
        incremental::{self, shake128_absorb_final, shake128_init},
        shake256, KeccakState,
    };

    use super::{shake128, shake256};

    /// Portable SHAKE 128 state
    pub(crate) struct PortableShake128 {
        state: KeccakState,
    }

    impl shake128::Xof for PortableShake128 {
        #[inline(always)]
        fn init_absorb(input: &[u8]) -> Self {
            let mut state = shake128_init();
            shake128_absorb_final(&mut state, &input);

            Self { state }
        }

        #[inline(always)]
        fn squeeze_first_five_blocks(&mut self) -> [u8; shake128::FIVE_BLOCKS_SIZE] {
            let mut out = [0u8; shake128::FIVE_BLOCKS_SIZE];
            incremental::shake128_squeeze_first_five_blocks(&mut self.state, &mut out);
            out
        }

        #[inline(always)]
        fn squeeze_next_block(&mut self) -> [u8; shake128::BLOCK_SIZE] {
            let mut out = [0u8; shake128::BLOCK_SIZE];
            incremental::shake128_squeeze_next_block(&mut self.state, &mut out);
            out
        }
    }

    /// Portable SHAKE 256 state
    pub(crate) struct PortableShake256 {
        state: KeccakState,
    }
    impl shake256::Xof for PortableShake256 {
        fn shake256<const OUTPUT_LENGTH: usize>(input: &[u8]) -> [u8; OUTPUT_LENGTH] {
            let mut out = [0u8; OUTPUT_LENGTH];
            shake256(&mut out, input);
            out
        }

        fn init_absorb(input: &[u8]) -> Self {
            let mut state = incremental::shake256_init();
            incremental::shake256_absorb_final(&mut state, input);

            Self { state }
        }

        fn squeeze_first_block(&mut self) -> [u8; shake256::BLOCK_SIZE] {
            let mut out = [0u8; shake256::BLOCK_SIZE];
            incremental::shake256_squeeze_first_block(&mut self.state, &mut out);
            out
        }

        fn squeeze_next_block(&mut self) -> [u8; shake256::BLOCK_SIZE] {
            let mut out = [0u8; shake256::BLOCK_SIZE];
            incremental::shake256_squeeze_next_block(&mut self.state, &mut out);
            out
        }
    }
}
