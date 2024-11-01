#![allow(non_snake_case)]

/// Abstraction and platform multiplexing for SHAKE 256
pub(crate) mod shake256 {
    pub(crate) const BLOCK_SIZE: usize = 136;

    pub(crate) trait Xof {
        fn shake256<const OUTPUT_LENGTH: usize>(input: &[u8], out: &mut [u8; OUTPUT_LENGTH]);
        fn init_absorb(input: &[u8]) -> Self;
        // TODO: There should only be a `squeeze_block`
        fn squeeze_first_block(&mut self) -> [u8; BLOCK_SIZE];
        fn squeeze_next_block(&mut self) -> [u8; BLOCK_SIZE];
    }

    pub(crate) trait XofX4 {
        fn shake256<const OUT_LEN: usize>(
            input0: &[u8],
            input1: &[u8],
            input2: &[u8],
            input3: &[u8],
            out0: &mut [u8; OUT_LEN],
            out1: &mut [u8; OUT_LEN],
            out2: &mut [u8; OUT_LEN],
            out3: &mut [u8; OUT_LEN],
        );
        fn init_absorb(input0: &[u8], input1: &[u8], input2: &[u8], input3: &[u8]) -> Self;
        fn squeeze_first_block(
            &mut self,
        ) -> (
            [u8; BLOCK_SIZE],
            [u8; BLOCK_SIZE],
            [u8; BLOCK_SIZE],
            [u8; BLOCK_SIZE],
        );
        fn squeeze_next_block(
            &mut self,
        ) -> (
            [u8; BLOCK_SIZE],
            [u8; BLOCK_SIZE],
            [u8; BLOCK_SIZE],
            [u8; BLOCK_SIZE],
        );
    }
}

/// Abstraction and platform multiplexing for SHAKE 128
pub(crate) mod shake128 {
    pub(crate) const BLOCK_SIZE: usize = 168;
    pub(crate) const FIVE_BLOCKS_SIZE: usize = BLOCK_SIZE * 5;

    pub(crate) trait Xof {
        fn shake128<const OUTPUT_LENGTH: usize>(input: &[u8], out: &mut [u8; OUTPUT_LENGTH]);
    }

    /// When sampling matrix A we always want to do 4 absorb/squeeze calls in
    /// parallel.
    pub(crate) trait XofX4 {
        fn init_absorb(input0: &[u8], input1: &[u8], input2: &[u8], input3: &[u8]) -> Self;
        fn squeeze_first_five_blocks(
            &mut self,
            out0: &mut [u8; FIVE_BLOCKS_SIZE],
            out1: &mut [u8; FIVE_BLOCKS_SIZE],
            out2: &mut [u8; FIVE_BLOCKS_SIZE],
            out3: &mut [u8; FIVE_BLOCKS_SIZE],
        );
        fn squeeze_next_block(
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
        shake128, shake256, KeccakState,
    };

    use super::{shake128, shake256};

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
        fn init_absorb(input0: &[u8], input1: &[u8], input2: &[u8], input3: &[u8]) -> Self {
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

        fn squeeze_first_five_blocks(
            &mut self,
            out0: &mut [u8; shake128::FIVE_BLOCKS_SIZE],
            out1: &mut [u8; shake128::FIVE_BLOCKS_SIZE],
            out2: &mut [u8; shake128::FIVE_BLOCKS_SIZE],
            out3: &mut [u8; shake128::FIVE_BLOCKS_SIZE],
        ) {
            incremental::shake128_squeeze_first_five_blocks(&mut self.state0, out0);
            incremental::shake128_squeeze_first_five_blocks(&mut self.state1, out1);
            incremental::shake128_squeeze_first_five_blocks(&mut self.state2, out2);
            incremental::shake128_squeeze_first_five_blocks(&mut self.state3, out3);
        }

        fn squeeze_next_block(
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

    /// Portable SHAKE 128 state
    pub(crate) struct Shake128 {}

    impl shake128::Xof for Shake128 {
        fn shake128<const OUTPUT_LENGTH: usize>(input: &[u8], out: &mut [u8; OUTPUT_LENGTH]) {
            shake128(out, input);
        }
    }

    /// Portable SHAKE 256 state
    pub(crate) struct Shake256 {
        state: KeccakState,
    }
    impl shake256::Xof for Shake256 {
        fn shake256<const OUTPUT_LENGTH: usize>(input: &[u8], out: &mut [u8; OUTPUT_LENGTH]) {
            shake256(out, input);
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

    /// Portable SHAKE 256 x4 state.
    ///
    /// We're using a portable implementation so this is actually sequential.
    pub(crate) struct Shake256X4 {
        state0: KeccakState,
        state1: KeccakState,
        state2: KeccakState,
        state3: KeccakState,
    }

    impl shake256::XofX4 for Shake256X4 {
        fn init_absorb(input0: &[u8], input1: &[u8], input2: &[u8], input3: &[u8]) -> Self {
            let mut state0 = incremental::shake256_init();
            incremental::shake256_absorb_final(&mut state0, input0);

            let mut state1 = incremental::shake256_init();
            incremental::shake256_absorb_final(&mut state1, input1);

            let mut state2 = incremental::shake256_init();
            incremental::shake256_absorb_final(&mut state2, input2);

            let mut state3 = incremental::shake256_init();
            incremental::shake256_absorb_final(&mut state3, input3);

            Self {
                state0,
                state1,
                state2,
                state3,
            }
        }

        fn squeeze_first_block(
            &mut self,
        ) -> (
            [u8; shake256::BLOCK_SIZE],
            [u8; shake256::BLOCK_SIZE],
            [u8; shake256::BLOCK_SIZE],
            [u8; shake256::BLOCK_SIZE],
        ) {
            let mut out0 = [0u8; shake256::BLOCK_SIZE];
            incremental::shake256_squeeze_first_block(&mut self.state0, &mut out0);
            let mut out1 = [0u8; shake256::BLOCK_SIZE];
            incremental::shake256_squeeze_first_block(&mut self.state1, &mut out1);
            let mut out2 = [0u8; shake256::BLOCK_SIZE];
            incremental::shake256_squeeze_first_block(&mut self.state2, &mut out2);
            let mut out3 = [0u8; shake256::BLOCK_SIZE];
            incremental::shake256_squeeze_first_block(&mut self.state3, &mut out3);

            (out0, out1, out2, out3)
        }

        fn squeeze_next_block(
            &mut self,
        ) -> (
            [u8; shake256::BLOCK_SIZE],
            [u8; shake256::BLOCK_SIZE],
            [u8; shake256::BLOCK_SIZE],
            [u8; shake256::BLOCK_SIZE],
        ) {
            let mut out0 = [0u8; shake256::BLOCK_SIZE];
            incremental::shake256_squeeze_next_block(&mut self.state0, &mut out0);
            let mut out1 = [0u8; shake256::BLOCK_SIZE];
            incremental::shake256_squeeze_next_block(&mut self.state1, &mut out1);
            let mut out2 = [0u8; shake256::BLOCK_SIZE];
            incremental::shake256_squeeze_next_block(&mut self.state2, &mut out2);
            let mut out3 = [0u8; shake256::BLOCK_SIZE];
            incremental::shake256_squeeze_next_block(&mut self.state3, &mut out3);

            (out0, out1, out2, out3)
        }

        fn shake256<const OUT_LEN: usize>(
            input0: &[u8],
            input1: &[u8],
            input2: &[u8],
            input3: &[u8],
            out0: &mut [u8; OUT_LEN],
            out1: &mut [u8; OUT_LEN],
            out2: &mut [u8; OUT_LEN],
            out3: &mut [u8; OUT_LEN],
        ) {
            shake256(out0, input0);
            shake256(out1, input1);
            shake256(out2, input2);
            shake256(out3, input3);
        }
    }
}

/// A SIMD256 implementation of [`shake128::XofX4`] and [`shake256::Xof`] for AVX2.
#[cfg(feature = "simd256")]
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
    pub(crate) struct Shake128x4 {
        state: KeccakState,
    }

    impl shake128::XofX4 for Shake128x4 {
        /// Init the state and absorb 4 blocks in parallel.
        fn init_absorb(input0: &[u8], input1: &[u8], input2: &[u8], input3: &[u8]) -> Self {
            let mut state = x4::incremental::init();
            x4::incremental::shake128_absorb_final(&mut state, &input0, &input1, &input2, &input3);
            Self { state }
        }

        fn squeeze_first_five_blocks(
            &mut self,
            out0: &mut [u8; shake128::FIVE_BLOCKS_SIZE],
            out1: &mut [u8; shake128::FIVE_BLOCKS_SIZE],
            out2: &mut [u8; shake128::FIVE_BLOCKS_SIZE],
            out3: &mut [u8; shake128::FIVE_BLOCKS_SIZE],
        ) {
            x4::incremental::shake128_squeeze_first_five_blocks(
                &mut self.state,
                out0,
                out1,
                out2,
                out3,
            );
        }

        fn squeeze_next_block(
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
        fn shake256<const OUTPUT_LENGTH: usize>(input: &[u8], out: &mut [u8; OUTPUT_LENGTH]) {
            portable::shake256(out, input);
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

    /// AVX2 SHAKE 256 x4 state.
    pub(crate) struct Shake256x4 {
        state: KeccakState,
    }

    impl shake256::XofX4 for Shake256x4 {
        fn init_absorb(input0: &[u8], input1: &[u8], input2: &[u8], input3: &[u8]) -> Self {
            let mut state = x4::incremental::init();
            x4::incremental::shake256_absorb_final(&mut state, &input0, &input1, &input2, &input3);
            Self { state }
        }

        fn squeeze_first_block(
            &mut self,
        ) -> (
            [u8; shake256::BLOCK_SIZE],
            [u8; shake256::BLOCK_SIZE],
            [u8; shake256::BLOCK_SIZE],
            [u8; shake256::BLOCK_SIZE],
        ) {
            let mut out0 = [0u8; shake256::BLOCK_SIZE];
            let mut out1 = [0u8; shake256::BLOCK_SIZE];
            let mut out2 = [0u8; shake256::BLOCK_SIZE];
            let mut out3 = [0u8; shake256::BLOCK_SIZE];
            x4::incremental::shake256_squeeze_first_block(
                &mut self.state,
                &mut out0,
                &mut out1,
                &mut out2,
                &mut out3,
            );

            (out0, out1, out2, out3)
        }

        fn squeeze_next_block(
            &mut self,
        ) -> (
            [u8; shake256::BLOCK_SIZE],
            [u8; shake256::BLOCK_SIZE],
            [u8; shake256::BLOCK_SIZE],
            [u8; shake256::BLOCK_SIZE],
        ) {
            let mut out0 = [0u8; shake256::BLOCK_SIZE];
            let mut out1 = [0u8; shake256::BLOCK_SIZE];
            let mut out2 = [0u8; shake256::BLOCK_SIZE];
            let mut out3 = [0u8; shake256::BLOCK_SIZE];
            x4::incremental::shake256_squeeze_next_block(
                &mut self.state,
                &mut out0,
                &mut out1,
                &mut out2,
                &mut out3,
            );

            (out0, out1, out2, out3)
        }

        fn shake256<const OUT_LEN: usize>(
            input0: &[u8],
            input1: &[u8],
            input2: &[u8],
            input3: &[u8],
            out0: &mut [u8; OUT_LEN],
            out1: &mut [u8; OUT_LEN],
            out2: &mut [u8; OUT_LEN],
            out3: &mut [u8; OUT_LEN],
        ) {
            x4::shake256(input0, input1, input2, input3, out0, out1, out2, out3);
        }
    }
}

/// A SIMD256 implementation of [`shake128::Xof`] and [`shake256::Xof`] for Neon.
#[cfg(feature = "simd128")]
pub(crate) mod neon {

    use libcrux_sha3::neon::x2::{self, incremental::KeccakState};

    use super::{shake128, shake256};

    pub(crate) struct Shake128x4 {
        state: [KeccakState; 2],
    }

    impl shake128::XofX4 for Shake128x4 {
        /// Init the state and absorb 4 blocks in parallel.
        fn init_absorb(input0: &[u8], input1: &[u8], input2: &[u8], input3: &[u8]) -> Self {
            let mut state = [x2::incremental::init(), x2::incremental::init()];
            x2::incremental::shake128_absorb_final(&mut state[0], &input0, &input1);
            x2::incremental::shake128_absorb_final(&mut state[1], &input2, &input3);
            Self { state }
        }

        fn squeeze_first_five_blocks(
            &mut self,
            out0: &mut [u8; shake128::FIVE_BLOCKS_SIZE],
            out1: &mut [u8; shake128::FIVE_BLOCKS_SIZE],
            out2: &mut [u8; shake128::FIVE_BLOCKS_SIZE],
            out3: &mut [u8; shake128::FIVE_BLOCKS_SIZE],
        ) {
            x2::incremental::shake128_squeeze_first_five_blocks(&mut self.state[0], out0, out1);
            x2::incremental::shake128_squeeze_first_five_blocks(&mut self.state[1], out2, out3);
        }

        fn squeeze_next_block(
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
            x2::incremental::shake128_squeeze_next_block(&mut self.state[0], &mut out0, &mut out1);
            x2::incremental::shake128_squeeze_next_block(&mut self.state[1], &mut out2, &mut out3);

            (out0, out1, out2, out3)
        }
    }

    /// Neon SHAKE 256 x4 state
    pub(crate) struct Shake256x4 {
        state: [KeccakState; 2],
    }

    impl shake256::XofX4 for Shake256x4 {
        fn init_absorb(input0: &[u8], input1: &[u8], input2: &[u8], input3: &[u8]) -> Self {
            let mut state = [x2::incremental::init(), x2::incremental::init()];
            x2::incremental::shake256_absorb_final(&mut state[0], &input0, &input1);
            x2::incremental::shake256_absorb_final(&mut state[1], &input2, &input3);
            Self { state }
        }

        fn squeeze_first_block(
            &mut self,
        ) -> (
            [u8; shake256::BLOCK_SIZE],
            [u8; shake256::BLOCK_SIZE],
            [u8; shake256::BLOCK_SIZE],
            [u8; shake256::BLOCK_SIZE],
        ) {
            let mut out0 = [0u8; shake256::BLOCK_SIZE];
            let mut out1 = [0u8; shake256::BLOCK_SIZE];
            let mut out2 = [0u8; shake256::BLOCK_SIZE];
            let mut out3 = [0u8; shake256::BLOCK_SIZE];
            x2::incremental::shake256_squeeze_first_block(&mut self.state[0], &mut out0, &mut out1);
            x2::incremental::shake256_squeeze_first_block(&mut self.state[1], &mut out2, &mut out3);

            (out0, out1, out2, out3)
        }

        fn squeeze_next_block(
            &mut self,
        ) -> (
            [u8; shake256::BLOCK_SIZE],
            [u8; shake256::BLOCK_SIZE],
            [u8; shake256::BLOCK_SIZE],
            [u8; shake256::BLOCK_SIZE],
        ) {
            let mut out0 = [0u8; shake256::BLOCK_SIZE];
            let mut out1 = [0u8; shake256::BLOCK_SIZE];
            let mut out2 = [0u8; shake256::BLOCK_SIZE];
            let mut out3 = [0u8; shake256::BLOCK_SIZE];
            x2::incremental::shake256_squeeze_next_block(&mut self.state[0], &mut out0, &mut out1);
            x2::incremental::shake256_squeeze_next_block(&mut self.state[1], &mut out2, &mut out3);

            (out0, out1, out2, out3)
        }

        fn shake256<const OUT_LEN: usize>(
            input0: &[u8],
            input1: &[u8],
            input2: &[u8],
            input3: &[u8],
            out0: &mut [u8; OUT_LEN],
            out1: &mut [u8; OUT_LEN],
            out2: &mut [u8; OUT_LEN],
            out3: &mut [u8; OUT_LEN],
        ) {
            x2::shake256(input0, input1, out0, out1);
            x2::shake256(input2, input3, out2, out3);
        }
    }
}
