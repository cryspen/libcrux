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

    /// When sampling matrix A we always want to do 4 absorb/squeeze calls in
    /// parallel.
    pub(crate) trait XofX4 {
        fn init_absorb_four(input0: &[u8], input1: &[u8], input2: &[u8], input3: &[u8]) -> Self;
        fn squeeze_four_times_five_blocks(
            &mut self,
        ) -> (
            [u8; FIVE_BLOCKS_SIZE],
            [u8; FIVE_BLOCKS_SIZE],
            [u8; FIVE_BLOCKS_SIZE],
            [u8; FIVE_BLOCKS_SIZE],
        );
        fn squeeze_four_times_one_block(
            &mut self,
        ) -> (
            [u8; BLOCK_SIZE],
            [u8; BLOCK_SIZE],
            [u8; BLOCK_SIZE],
            [u8; BLOCK_SIZE],
        );
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
    pub(crate) struct Shake128 {
        state: KeccakState,
    }

    impl shake128::Xof for Shake128 {
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

    /// Portable SHAKE 128 x4 state.
    ///
    /// We're using a portable implementation so this is actually sequential.
    pub(crate) struct Shake128X4 {
        state0: KeccakState,
        state1: KeccakState,
        state2: KeccakState,
        state3: KeccakState,
    }

    impl shake128::XofX4 for Shake128X4 {
        fn init_absorb_four(input0: &[u8], input1: &[u8], input2: &[u8], input3: &[u8]) -> Self {
            #[inline(always)]
            fn init_absorb(input: &[u8]) -> KeccakState {
                let mut state = shake128_init();
                shake128_absorb_final(&mut state, &input);

                state
            }

            let state0 = init_absorb(input0);
            let state1 = init_absorb(input1);
            let state2 = init_absorb(input2);
            let state3 = init_absorb(input3);

            Self {
                state0,
                state1,
                state2,
                state3,
            }
        }

        fn squeeze_four_times_five_blocks(
            &mut self,
        ) -> (
            [u8; shake128::FIVE_BLOCKS_SIZE],
            [u8; shake128::FIVE_BLOCKS_SIZE],
            [u8; shake128::FIVE_BLOCKS_SIZE],
            [u8; shake128::FIVE_BLOCKS_SIZE],
        ) {
            let mut out0 = [0u8; shake128::FIVE_BLOCKS_SIZE];
            incremental::shake128_squeeze_first_five_blocks(&mut self.state0, &mut out0);
            let mut out1 = [0u8; shake128::FIVE_BLOCKS_SIZE];
            incremental::shake128_squeeze_first_five_blocks(&mut self.state1, &mut out1);
            let mut out2 = [0u8; shake128::FIVE_BLOCKS_SIZE];
            incremental::shake128_squeeze_first_five_blocks(&mut self.state2, &mut out2);
            let mut out3 = [0u8; shake128::FIVE_BLOCKS_SIZE];
            incremental::shake128_squeeze_first_five_blocks(&mut self.state3, &mut out3);

            (out0, out1, out2, out3)
        }

        fn squeeze_four_times_one_block(
            &mut self,
        ) -> (
            [u8; shake128::BLOCK_SIZE],
            [u8; shake128::BLOCK_SIZE],
            [u8; shake128::BLOCK_SIZE],
            [u8; shake128::BLOCK_SIZE],
        ) {
            let mut out0 = [0u8; shake128::BLOCK_SIZE];
            incremental::shake128_squeeze_next_block(&mut self.state0, &mut out0);
            let mut out1 = [0u8; shake128::BLOCK_SIZE];
            incremental::shake128_squeeze_next_block(&mut self.state1, &mut out1);
            let mut out2 = [0u8; shake128::BLOCK_SIZE];
            incremental::shake128_squeeze_next_block(&mut self.state2, &mut out2);
            let mut out3 = [0u8; shake128::BLOCK_SIZE];
            incremental::shake128_squeeze_next_block(&mut self.state3, &mut out3);

            (out0, out1, out2, out3)
        }
    }

    /// Portable SHAKE 256 state
    pub(crate) struct Shake256 {
        state: KeccakState,
    }
    impl shake256::Xof for Shake256 {
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

#[cfg(feature = "simd256")]
/// A SIMD256 implementation of [`shake128::XofX4`] and [`shake256::Xof`] for AVX2.
pub(crate) mod simd256 {

    use libcrux_sha3::{
        avx2::x4::{self, incremental::KeccakState},
        portable,
    };

    use super::{shake128, shake256};

    /// AVX2 SHAKE 128 state
    ///
    /// This only implements the XofX4 API. For the single Xof, the portable
    /// version is used.
    pub(crate) struct Shake128 {
        state: KeccakState,
    }

    impl shake128::XofX4 for Shake128 {
        /// Init the state and absorb 4 blocks in parallel.
        fn init_absorb_four(input0: &[u8], input1: &[u8], input2: &[u8], input3: &[u8]) -> Self {
            let mut state = x4::incremental::shake128_init();
            x4::incremental::shake128_absorb_final(&mut state, &input0, &input1, &input2, &input3);
            Self { state }
        }

        fn squeeze_four_times_five_blocks(
            &mut self,
        ) -> (
            [u8; shake128::FIVE_BLOCKS_SIZE],
            [u8; shake128::FIVE_BLOCKS_SIZE],
            [u8; shake128::FIVE_BLOCKS_SIZE],
            [u8; shake128::FIVE_BLOCKS_SIZE],
        ) {
            let mut out0 = [0u8; shake128::FIVE_BLOCKS_SIZE];
            let mut out1 = [0u8; shake128::FIVE_BLOCKS_SIZE];
            let mut out2 = [0u8; shake128::FIVE_BLOCKS_SIZE];
            let mut out3 = [0u8; shake128::FIVE_BLOCKS_SIZE];
            x4::incremental::shake128_squeeze_first_five_blocks(
                &mut self.state,
                &mut out0,
                &mut out1,
                &mut out2,
                &mut out3,
            );

            (out0, out1, out2, out3)
        }

        fn squeeze_four_times_one_block(
            &mut self,
        ) -> (
            [u8; shake128::BLOCK_SIZE],
            [u8; shake128::BLOCK_SIZE],
            [u8; shake128::BLOCK_SIZE],
            [u8; shake128::BLOCK_SIZE],
        ) {
            let mut out0 = [0u8; shake128::BLOCK_SIZE];
            let mut out1 = [0u8; shake128::BLOCK_SIZE];
            let mut out2 = [0u8; shake128::BLOCK_SIZE];
            let mut out3 = [0u8; shake128::BLOCK_SIZE];
            x4::incremental::shake128_squeeze_next_block(
                &mut self.state,
                &mut out0,
                &mut out1,
                &mut out2,
                &mut out3,
            );

            (out0, out1, out2, out3)
        }
    }

    // TODO: Shake256 is only portable for now. If we don't want to change that,
    // we should use the portable Xof impelmentation above.

    /// AVX2 SHAKE 256 state
    pub(crate) struct Shake256 {
        state: portable::KeccakState,
    }
    impl shake256::Xof for Shake256 {
        fn shake256<const OUTPUT_LENGTH: usize>(input: &[u8]) -> [u8; OUTPUT_LENGTH] {
            let mut out = [0u8; OUTPUT_LENGTH];
            portable::shake256(&mut out, input);
            out
        }

        fn init_absorb(input: &[u8]) -> Self {
            let mut state = portable::incremental::shake256_init();
            portable::incremental::shake256_absorb_final(&mut state, input);

            Self { state }
        }

        fn squeeze_first_block(&mut self) -> [u8; shake256::BLOCK_SIZE] {
            let mut out = [0u8; shake256::BLOCK_SIZE];
            portable::incremental::shake256_squeeze_first_block(&mut self.state, &mut out);
            out
        }

        fn squeeze_next_block(&mut self) -> [u8; shake256::BLOCK_SIZE] {
            let mut out = [0u8; shake256::BLOCK_SIZE];
            portable::incremental::shake256_squeeze_next_block(&mut self.state, &mut out);
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

    // TODO:
    // - measure if neon is faster or slower for the sequential shakes.

    /// Neon SHAKE 128 state
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

    impl shake128::XofX4 for PortableShake128 {
        /// Init the state and absorb 4 blocks in parallel.
        /// We're using a portable implementation so this is actually sequential.
        fn init_absorb_four(input0: &[u8], input1: &[u8], input2: &[u8], input3: &[u8]) -> Self {
            todo!()
        }

        fn squeeze_four_times_five_blocks(
            &mut self,
        ) -> (
            [u8; shake128::FIVE_BLOCKS_SIZE],
            [u8; shake128::FIVE_BLOCKS_SIZE],
            [u8; shake128::FIVE_BLOCKS_SIZE],
            [u8; shake128::FIVE_BLOCKS_SIZE],
        ) {
            todo!()
        }

        fn squeeze_four_times_one_block(
            &mut self,
        ) -> (
            [u8; shake128::BLOCK_SIZE],
            [u8; shake128::BLOCK_SIZE],
            [u8; shake128::BLOCK_SIZE],
            [u8; shake128::BLOCK_SIZE],
        ) {
            todo!()
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
