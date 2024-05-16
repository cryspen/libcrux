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
        fn G(input: &[u8]) -> [u8; G_DIGEST_SIZE] {
            let mut digest = [0u8; G_DIGEST_SIZE];
            portable::sha512(&mut digest, input);
            digest
        }

        fn H(input: &[u8]) -> [u8; H_DIGEST_SIZE] {
            let mut digest = [0u8; H_DIGEST_SIZE];
            portable::sha256(&mut digest, input);
            digest
        }

        fn PRF<const LEN: usize>(input: &[u8]) -> [u8; LEN] {
            let mut digest = [0u8; LEN];
            portable::shake256(&mut digest, input);
            digest
        }

        fn PRFxN<const LEN: usize>(input: &[[u8; 33]; K]) -> [[u8; LEN]; K] {
            debug_assert!(K == 2 || K == 3 || K == 4);

            let mut out = [[0u8; LEN]; K];
            for i in 0..K {
                portable::shake256::<LEN>(&mut out[i], &input[i]);
            }
            out
        }

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

        fn shake128_squeeze_three_blocks(&mut self) -> [[u8; THREE_BLOCKS]; K] {
            debug_assert!(K == 2 || K == 3 || K == 4);

            let mut out = [[0u8; THREE_BLOCKS]; K];
            for i in 0..K {
                shake128_squeeze_first_three_blocks(&mut self.shake128_state[i], &mut out[i]);
            }
            out
        }

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
        fn G(input: &[u8]) -> [u8; G_DIGEST_SIZE] {
            let mut digest = [0u8; G_DIGEST_SIZE];
            portable::sha512(&mut digest, input);
            digest
        }

        fn H(input: &[u8]) -> [u8; H_DIGEST_SIZE] {
            let mut digest = [0u8; H_DIGEST_SIZE];
            portable::sha256(&mut digest, input);
            digest
        }

        fn PRF<const LEN: usize>(input: &[u8]) -> [u8; LEN] {
            let mut digest = [0u8; LEN];
            portable::shake256(&mut digest, input);
            digest
        }

        fn PRFxN<const LEN: usize>(input: &[[u8; 33]; K]) -> [[u8; LEN]; K] {
            debug_assert!(K == 2 || K == 3 || K == 4);
            let mut out = [[0u8; LEN]; K];

            match K {
                2 => {
                    let mut dummy_out0 = [0u8; LEN];
                    let mut dummy_out1 = [0u8; LEN];
                    let (out0, out1) = out.split_at_mut(1);
                    x4::shake256(
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
                    x4::shake256(
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
                    x4::shake256(
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
                _ => unreachable!("This function is only called with 2, 3, 4"),
            }
            out
        }

        fn shake128_init_absorb(input: [[u8; 34]; K]) -> Self {
            debug_assert!(K == 2 || K == 3 || K == 4);
            let mut state = x4::incremental::shake128_init();

            match K {
                2 => {
                    x4::incremental::shake128_absorb_final(
                        &mut state, &input[0], &input[1], &input[0], &input[0],
                    );
                }
                3 => {
                    x4::incremental::shake128_absorb_final(
                        &mut state, &input[0], &input[1], &input[2], &input[0],
                    );
                }
                4 => {
                    x4::incremental::shake128_absorb_final(
                        &mut state, &input[0], &input[1], &input[2], &input[3],
                    );
                }
                _ => unreachable!("This function is only called with 2, 3, 4"),
            }
            Self {
                shake128_state: state,
            }
        }

        fn shake128_squeeze_three_blocks(&mut self) -> [[u8; THREE_BLOCKS]; K] {
            debug_assert!(K == 2 || K == 3 || K == 4);

            let mut out = [[0u8; THREE_BLOCKS]; K];
            match K {
                2 => {
                    let mut dummy_out0 = [0u8; THREE_BLOCKS];
                    let mut dummy_out1 = [0u8; THREE_BLOCKS];
                    let (out0, out1) = out.split_at_mut(1);
                    x4::incremental::shake128_squeeze_first_three_blocks(
                        &mut self.shake128_state,
                        &mut out0[0],
                        &mut out1[0],
                        &mut dummy_out0,
                        &mut dummy_out1,
                    );
                }
                3 => {
                    let mut dummy_out0 = [0u8; THREE_BLOCKS];
                    let (out0, out12) = out.split_at_mut(1);
                    let (out1, out2) = out12.split_at_mut(1);
                    x4::incremental::shake128_squeeze_first_three_blocks(
                        &mut self.shake128_state,
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
                    x4::incremental::shake128_squeeze_first_three_blocks(
                        &mut self.shake128_state,
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

        fn shake128_squeeze_block(&mut self) -> [[u8; BLOCK_SIZE]; K] {
            debug_assert!(K == 2 || K == 3 || K == 4);

            let mut dummy_out0 = [0u8; BLOCK_SIZE];
            let mut dummy_out1 = [0u8; BLOCK_SIZE];

            let mut out = [[0u8; BLOCK_SIZE]; K];

            match K {
                2 => {
                    let (out0, out1) = out.split_at_mut(1);
                    x4::incremental::shake128_squeeze_next_block(
                        &mut self.shake128_state,
                        &mut out0[0],
                        &mut out1[0],
                        &mut dummy_out0,
                        &mut dummy_out1,
                    );
                }
                3 => {
                    let (out0, out12) = out.split_at_mut(1);
                    let (out1, out2) = out12.split_at_mut(1);
                    x4::incremental::shake128_squeeze_next_block(
                        &mut self.shake128_state,
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
                    x4::incremental::shake128_squeeze_next_block(
                        &mut self.shake128_state,
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

// #[inline(always)]
// pub(crate) fn G(input: &[u8]) -> [u8; 64] {
//     simd::sha3_512(input)
// }

// #[inline(always)]
// pub(crate) fn H(input: &[u8]) -> [u8; H_DIGEST_SIZE] {
//     simd::sha3_256(input)
// }

// #[inline(always)]
// pub(crate) fn PRF<const LEN: usize>(input: &[u8]) -> [u8; LEN] {
//     simd::shake256::<LEN>(input)
// }

// #[cfg(feature = "simd128")]
// #[inline(always)]
// pub(crate) fn PRFxN<const LEN: usize, const K: usize>(input: &[[u8; 33]; K]) -> [[u8; LEN]; K] {
//     let mut out = [[0u8; LEN]; K];
//     let mut extra = [0u8; LEN];

//     match K {
//         2 => {
//             let (out0, out1) = out.split_at_mut(1);
//             simd::shake256x2(&input[0], &input[1], &mut out0[0], &mut out1[0]);
//         }
//         3 => {
//             let (out0, out12) = out.split_at_mut(1);
//             let (out1, out2) = out12.split_at_mut(1);
//             simd::shake256x2(&input[0], &input[1], &mut out0[0], &mut out1[0]);
//             simd::shake256x2(&input[2], &input[2], &mut out2[0], &mut extra);
//         }
//         _ => {
//             let (out0, out123) = out.split_at_mut(1);
//             let (out1, out23) = out123.split_at_mut(1);
//             let (out2, out3) = out23.split_at_mut(1);
//             simd::shake256x2(&input[0], &input[1], &mut out0[0], &mut out1[0]);
//             simd::shake256x2(&input[2], &input[3], &mut out2[0], &mut out3[0]);
//         }
//     }
//     out
// }

// #[cfg(not(any(feature = "simd128", feature = "simd256")))]
// #[inline(always)]
// pub(crate) fn PRFxN<const LEN: usize, const K: usize>(input: &[[u8; 33]; K]) -> [[u8; LEN]; K] {
//     core::array::from_fn(|i| simd::shake256::<LEN>(&input[i]))
// }

// #[cfg(feature = "simd128")]
// pub(crate) type Shake128x4State = KeccakState4;

// #[cfg(feature = "simd128")]
// #[inline(always)]
// pub(crate) fn absorb<const K: usize>(input: [[u8; 34]; K]) -> Shake128x4State {
//     debug_assert!(K == 2 || K == 3 || K == 4);

//     let mut states = simd::shake128x4_init();
//     match K {
//         2 => {
//             simd::shake128x2_absorb_final(&mut states[0], &input[0], &input[1]);
//         }
//         3 => {
//             simd::shake128x2_absorb_final(&mut states[0], &input[0], &input[1]);
//             simd::shake128x2_absorb_final(&mut states[1], &input[2], &input[2]);
//         }
//         _ => {
//             simd::shake128x2_absorb_final(&mut states[0], &input[0], &input[1]);
//             simd::shake128x2_absorb_final(&mut states[1], &input[2], &input[3]);
//         }
//     }
//     states
// }

// #[cfg(feature = "simd128")]
// #[inline(always)]
// pub(crate) fn squeeze_three_blocks<const K: usize>(
//     state: &mut Shake128x4State,
// ) -> [[u8; THREE_BLOCKS]; K] {
//     let mut out = [[0u8; THREE_BLOCKS]; K];
//     let mut extra = [0u8; THREE_BLOCKS];

//     match K {
//         2 => {
//             let (out0, out1) = out.split_at_mut(1);
//             simd::shake128x2_squeeze_first_three_blocks(&mut state[0], &mut out0[0], &mut out1[0]);
//         }
//         3 => {
//             let (out0, out12) = out.split_at_mut(1);
//             let (out1, out2) = out12.split_at_mut(1);
//             simd::shake128x2_squeeze_first_three_blocks(&mut state[0], &mut out0[0], &mut out1[0]);
//             simd::shake128x2_squeeze_first_three_blocks(&mut state[1], &mut out2[0], &mut extra);
//         }
//         _ => {
//             let (out0, out123) = out.split_at_mut(1);
//             let (out1, out23) = out123.split_at_mut(1);
//             let (out2, out3) = out23.split_at_mut(1);
//             simd::shake128x2_squeeze_first_three_blocks(&mut state[0], &mut out0[0], &mut out1[0]);
//             simd::shake128x2_squeeze_first_three_blocks(&mut state[1], &mut out2[0], &mut out3[0]);
//         }
//     }
//     out
// }

// #[cfg(feature = "simd128")]
// #[inline(always)]
// pub(crate) fn squeeze_block<const K: usize>(state: &mut Shake128x4State) -> [[u8; BLOCK_SIZE]; K] {
//     let mut out0 = [0u8; BLOCK_SIZE];
//     let mut out1 = [0u8; BLOCK_SIZE];
//     let mut out2 = [0u8; BLOCK_SIZE];
//     let mut out3 = [0u8; BLOCK_SIZE];

//     let mut out = [[0u8; BLOCK_SIZE]; K];

//     match K {
//         2 => {
//             simd::shake128x2_squeeze_next_block(&mut state[0], &mut out0, &mut out1);
//             out[0] = out0;
//             out[1] = out1;
//         }
//         3 => {
//             simd::shake128x2_squeeze_next_block(&mut state[0], &mut out0, &mut out1);
//             simd::shake128x2_squeeze_next_block(&mut state[1], &mut out2, &mut out3);
//             out[0] = out0;
//             out[1] = out1;
//             out[2] = out2;
//         }
//         _ => {
//             simd::shake128x2_squeeze_next_block(&mut state[0], &mut out0, &mut out1);
//             simd::shake128x2_squeeze_next_block(&mut state[1], &mut out2, &mut out3);
//             out[0] = out0;
//             out[1] = out1;
//             out[2] = out2;
//             out[3] = out3;
//         }
//     }
//     out
// }

// /// Free the memory of the state.
// ///
// /// **NOTE:** That this needs to be done manually for now.
// #[cfg(not(any(feature = "simd256", feature = "simd128")))]
// #[inline(always)]
// pub(crate) fn free_state<const K: usize>(_xof_state: [simd::KeccakState1; K]) {}

// /// Free the memory of the state.
// ///
// /// **NOTE:** That this needs to be done manually for now.
// #[cfg(any(feature = "simd256", feature = "simd128"))]
// #[inline(always)]
// pub(crate) fn free_state(_xof_state: KeccakState4) {}
