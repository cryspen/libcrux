#![allow(non_snake_case)]
//! This module contains the hash functions needed by ML-KEM
//! Verification Status: Interface-Only, Lax

// TODO: Extract and verify the code, not just the interface, by relating to libcrux-sha3
// Related Issue: https://github.com/cryspen/libcrux/issues/395 for extracting/checking libcrux-sha3
// TODO: We need to manually pull out the code for G, H, PRFxN, etc. in each module to allow
// them to be properly abstracted in F*. We would like hax to do this automatically.
// Related Issue: https://github.com/hacspec/hax/issues/616

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
#[hax_lib::attributes]
pub(crate) trait Hash {
    /// G aka SHA3 512
    #[requires(true)]
    #[ensures(|result|
        fstar!(r#"$result == Spec.Utils.v_G $input"#))
    ]
    fn G(input: &[u8], output: &mut [u8; G_DIGEST_SIZE]);

    /// H aka SHA3 256
    #[requires(true)]
    #[ensures(|result|
        fstar!(r#"$result == Spec.Utils.v_H $input"#))
    ]
    fn H(input: &[u8], output: &mut [u8; H_DIGEST_SIZE]);

    /// PRF aka SHAKE256
    #[requires(fstar!(r#"v $LEN < pow2 32"#))]
    #[ensures(|result|
        // We need to repeat the pre-condition here because of https://github.com/hacspec/hax/issues/784
        fstar!(r#"v $LEN < pow2 32 ==> $result == Spec.Utils.v_PRF $LEN $input"#))
    ]
    fn PRF(input: &[u8], output: &mut [u8]);

    /// PRFxN aka N SHAKE256
    #[requires(fstar!(r#"v $LEN < pow2 32 /\ (v $K == 2 \/ v $K == 3 \/ v $K == 4)"#))]
    #[ensures(|result|
        // We need to repeat the pre-condition here because of https://github.com/hacspec/hax/issues/784
        fstar!(r#"(v $LEN < pow2 32 /\ (v $K == 2 \/ v $K == 3 \/ v $K == 4)) ==>
            $result == Spec.Utils.v_PRFxN $K $LEN $input"#))
    ]
    // fn PRFxN<const LEN: usize>(input: &[[u8; 33]; K]) -> [[u8; LEN]; K];
    fn PRFxN(input: &[[u8; 33]], outputs: &mut [&mut [u8]], out_len: usize);

    /// Create a SHAKE128 state and absorb the input.
    #[requires(true)]
    fn shake128_init_absorb_final(input: &[[u8; 34]]) -> Self;

    /// Squeeze 3 blocks out of the SHAKE128 state.
    #[requires(true)]
    fn shake128_squeeze_first_three_blocks(&mut self, output: &mut [[u8; THREE_BLOCKS]]);

    /// Squeeze 1 block out of the SHAKE128 state.
    #[requires(true)]
    fn shake128_squeeze_next_block(&mut self, output: &mut [[u8; BLOCK_SIZE]]);
}

/// A portable implementation of [`Hash`]
pub(crate) mod portable {
    use super::*;
    use libcrux_sha3::portable::{self, incremental, KeccakState};

    /// The state.
    ///
    /// It's only used for SHAKE128.
    /// All other functions don't actually use any members.
    #[cfg_attr(hax, hax_lib::opaque)]
    pub(crate) struct PortableHash {
        shake128_state: [KeccakState; 4],
    }

    #[hax_lib::ensures(|result|
        fstar!(r#"$result == Spec.Utils.v_G $input"#))
    ]
    #[inline(always)]
    fn G(input: &[u8], output: &mut [u8; G_DIGEST_SIZE]) {
        portable::sha512(output, input);
    }

    #[hax_lib::ensures(|result|
        fstar!(r#"$result == Spec.Utils.v_H $input"#))
    ]
    #[inline(always)]
    fn H(input: &[u8], output: &mut [u8; H_DIGEST_SIZE]) {
        portable::sha256(output, input);
    }

    #[hax_lib::requires(fstar!(r#"v $LEN < pow2 32"#))]
    #[hax_lib::ensures(|result|
        fstar!(r#"$result == Spec.Utils.v_PRF $LEN $input"#))
    ]
    #[inline(always)]
    fn PRF(input: &[u8], output: &mut [u8]) {
        portable::shake256(output, input);
    }

    #[hax_lib::requires(fstar!(r#"v $LEN < pow2 32 /\ (v $K == 2 \/ v $K == 3 \/ v $K == 4)"#))]
    #[hax_lib::ensures(|result|
        fstar!(r#"$result == Spec.Utils.v_PRFxN $K $LEN $input"#))
    ]
    #[inline(always)]
    fn PRFxN(input: &[[u8; 33]], outputs: &mut [u8], out_len: usize) {
        for i in 0..input.len() {
            portable::shake256(&mut outputs[i * out_len..(i + 1) * out_len], &input[i]);
        }
    }

    #[inline(always)]
    fn shake128_init_absorb_final(input: &[[u8; 34]]) -> PortableHash {
        debug_assert!(input.len() == 2 || input.len() == 3 || input.len() == 4);

        let mut shake128_state = [incremental::shake128_init(); 4];
        for i in 0..input.len() {
            incremental::shake128_absorb_final(&mut shake128_state[i], &input[i]);
        }
        PortableHash { shake128_state }
    }

    #[inline(always)]
    fn shake128_squeeze_first_three_blocks(
        st: &mut PortableHash,
        outputs: &mut [[u8; THREE_BLOCKS]],
    ) {
        debug_assert!(outputs.len() == 2 || outputs.len() == 3 || outputs.len() == 4);

        for i in 0..outputs.len() {
            incremental::shake128_squeeze_first_three_blocks(
                &mut st.shake128_state[i],
                &mut outputs[i],
            );
        }
    }

    #[inline(always)]
    fn shake128_squeeze_next_block(st: &mut PortableHash, outputs: &mut [[u8; BLOCK_SIZE]]) {
        debug_assert!(outputs.len() == 2 || outputs.len() == 3 || outputs.len() == 4);

        for i in 0..outputs.len() {
            incremental::shake128_squeeze_next_block(&mut st.shake128_state[i], &mut outputs[i]);
        }
    }

    #[hax_lib::attributes]
    impl Hash for PortableHash {
        #[ensures(|out|
            fstar!(r#"$out == Spec.Utils.v_G $input"#))
        ]
        #[inline(always)]
        fn G(input: &[u8], output: &mut [u8; G_DIGEST_SIZE]) {
            G(input, output)
        }

        #[ensures(|out|
            fstar!(r#"$out == Spec.Utils.v_H $input"#))
        ]
        #[inline(always)]
        fn H(input: &[u8], output: &mut [u8; H_DIGEST_SIZE]) {
            H(input, output)
        }

        #[requires(fstar!(r#"v $LEN < pow2 32"#))]
        #[ensures(|out|
            // We need to repeat the pre-condition here because of https://github.com/hacspec/hax/issues/784
            fstar!(r#"v $LEN < pow2 32 ==> $out == Spec.Utils.v_PRF $LEN $input"#))
        ]
        #[inline(always)]
        fn PRF(input: &[u8], output: &mut [u8]) {
            PRF(input, output)
        }

        #[requires(fstar!(r#"v $LEN < pow2 32 /\ (v $K == 2 \/ v $K == 3 \/ v $K == 4)"#))]
        #[ensures(|out|
            fstar!(r#"(v $LEN < pow2 32 /\ (v $K == 2 \/ v $K == 3 \/ v $K == 4)) ==>
                $out == Spec.Utils.v_PRFxN $K $LEN $input"#))
        ]
        #[inline(always)]
        fn PRFxN(input: &[[u8; 33]], outputs: &mut [u8], out_len: usize) {
            PRFxN(input, outputs, out_len)
        }

        #[inline(always)]
        fn shake128_init_absorb_final(input: &[[u8; 34]]) -> Self {
            shake128_init_absorb_final(input)
        }

        #[inline(always)]
        fn shake128_squeeze_first_three_blocks(&mut self, output: &mut [[u8; THREE_BLOCKS]]) {
            shake128_squeeze_first_three_blocks(self, output)
        }

        #[inline(always)]
        fn shake128_squeeze_next_block(&mut self, output: &mut [[u8; BLOCK_SIZE]]) {
            shake128_squeeze_next_block(self, output)
        }
    }
}

/// A SIMD256 implementation of [`Hash`] for AVX2
#[cfg(feature = "simd256")]
pub(crate) mod avx2 {
    use super::*;
    use libcrux_sha3::{
        avx2::x4::{self, incremental::KeccakState},
        portable,
    };

    /// The state.
    ///
    /// It's only used for SHAKE128.
    /// All other functions don't actually use any members.
    #[cfg_attr(hax, hax_lib::opaque)]
    pub(crate) struct Simd256Hash {
        shake128_state: KeccakState,
    }

    #[hax_lib::ensures(|result|
        fstar!(r#"$result == Spec.Utils.v_G $input"#))
    ]
    #[inline(always)]
    fn G(input: &[u8], output: &mut [u8; G_DIGEST_SIZE]) {
        portable::sha512(output, input);
    }

    #[hax_lib::ensures(|result|
        fstar!(r#"$result == Spec.Utils.v_H $input"#))
    ]
    #[inline(always)]
    fn H(input: &[u8], output: &mut [u8; H_DIGEST_SIZE]) {
        portable::sha256(output, input);
    }

    #[hax_lib::requires(fstar!(r#"v $LEN < pow2 32"#))]
    #[hax_lib::ensures(|result|
        fstar!(r#"$result == Spec.Utils.v_PRF $LEN $input"#))
    ]
    #[inline(always)]
    fn PRF(input: &[u8], output: &mut [u8]) {
        portable::shake256(output, input);
    }

    #[hax_lib::requires(fstar!(r#"v $LEN < pow2 32 /\ (v $K == 2 \/ v $K == 3 \/ v $K == 4)"#))]
    #[hax_lib::ensures(|result|
        fstar!(r#"$result == Spec.Utils.v_PRFxN $K $LEN $input"#))
    ]
    #[inline(always)]
    fn PRFxN(input: &[[u8; 33]], outputs: &mut [&mut [u8]], out_len: usize) {
        // XXX: The buffer sizes here are the maximum that we will
        // need. PRFxN is called to fill N buffers of size
        // `ETA1/2_RANDOMNESS_SIZE`. The maximum value for
        // `ETA1/2_RANDOMNESS_SIZE` is in ML-KEM 512 with `ETA1 = 3`
        // and `ETA1_RANDOMNESS_SIZE = ETA1 * 64`.  This means,
        // unfortunately, that we overallocate and oversample in the
        // other cases.
        let mut out0 = [0u8; 3 * 64];
        let mut out1 = [0u8; 3 * 64];
        let mut out2 = [0u8; 3 * 64];
        let mut out3 = [0u8; 3 * 64];

        match input.len() as u8 {
            2 => {
                x4::shake256(
                    &input[0], &input[1], &input[0], &input[0], &mut out0, &mut out1, &mut out2,
                    &mut out3,
                );
                outputs[0..out_len].copy_from_slice(&out0[..out_len]);
                outputs[out_len..2 * out_len].copy_from_slice(&out1[..out_len]);
            }
            3 => {
                x4::shake256(
                    &input[0], &input[1], &input[2], &input[0], &mut out0, &mut out1, &mut out2,
                    &mut out3,
                );
                outputs[0 * out_len..1 * out_len].copy_from_slice(&out0[..out_len]);
                outputs[1 * out_len..2 * out_len].copy_from_slice(&out1[..out_len]);
                outputs[2 * out_len..3 * out_len].copy_from_slice(&out2[..out_len]);
            }
            4 => {
                x4::shake256(
                    &input[0], &input[1], &input[2], &input[3], &mut out0, &mut out1, &mut out2,
                    &mut out3,
                );
                outputs[0 * out_len..1 * out_len].copy_from_slice(&out0[..out_len]);
                outputs[1 * out_len..2 * out_len].copy_from_slice(&out1[..out_len]);
                outputs[2 * out_len..3 * out_len].copy_from_slice(&out2[..out_len]);
                outputs[3 * out_len..4 * out_len].copy_from_slice(&out3[..out_len]);
            }
            _ => unreachable!("This function must only be called with N = 2, 3, 4"),
        }
    }

    #[inline(always)]
    fn shake128_init_absorb_final(input: &[[u8; 34]]) -> Simd256Hash {
        debug_assert!(input.len() == 2 || input.len() == 3 || input.len() == 4);
        let mut state = x4::incremental::init();

        match input.len() as u8 {
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
            _ => unreachable!("This function must only be called with N = 2, 3, 4"),
        }

        Simd256Hash {
            shake128_state: state,
        }
    }

    #[inline(always)]
    fn shake128_squeeze_first_three_blocks(
        st: &mut Simd256Hash,
        outputs: &mut [[u8; THREE_BLOCKS]],
    ) {
        debug_assert!(outputs.len() == 2 || outputs.len() == 3 || outputs.len() == 4);
        let mut out0 = [0u8; THREE_BLOCKS];
        let mut out1 = [0u8; THREE_BLOCKS];
        let mut out2 = [0u8; THREE_BLOCKS];
        let mut out3 = [0u8; THREE_BLOCKS];
        x4::incremental::shake128_squeeze_first_three_blocks(
            &mut st.shake128_state,
            &mut out0,
            &mut out1,
            &mut out2,
            &mut out3,
        );
        match outputs.len() as u8 {
            2 => {
                outputs[0] = out0;
                outputs[1] = out1;
            }
            3 => {
                outputs[0] = out0;
                outputs[1] = out1;
                outputs[2] = out2;
            }
            4 => {
                outputs[0] = out0;
                outputs[1] = out1;
                outputs[2] = out2;
                outputs[3] = out3;
            }
            _ => unreachable!("This function must only be called with N = 2, 3, 4"),
        }
    }

    #[inline(always)]
    fn shake128_squeeze_next_block(st: &mut Simd256Hash, outputs: &mut [[u8; BLOCK_SIZE]]) {
        debug_assert!(outputs.len() == 2 || outputs.len() == 3 || outputs.len() == 4);
        let mut out0 = [0u8; BLOCK_SIZE];
        let mut out1 = [0u8; BLOCK_SIZE];
        let mut out2 = [0u8; BLOCK_SIZE];
        let mut out3 = [0u8; BLOCK_SIZE];
        x4::incremental::shake128_squeeze_next_block(
            &mut st.shake128_state,
            &mut out0,
            &mut out1,
            &mut out2,
            &mut out3,
        );
        match outputs.len() as u8 {
            2 => {
                outputs[0] = out0;
                outputs[1] = out1;
            }
            3 => {
                outputs[0] = out0;
                outputs[1] = out1;
                outputs[2] = out2;
            }
            4 => {
                outputs[0] = out0;
                outputs[1] = out1;
                outputs[2] = out2;
                outputs[3] = out3;
            }
            _ => unreachable!("This function is only called with 2, 3, 4"),
        }
    }

    #[hax_lib::attributes]
    impl Hash for Simd256Hash {
        #[ensures(|out|
            fstar!(r#"$out == Spec.Utils.v_G $input"#))
        ]
        #[inline(always)]
        fn G(input: &[u8], output: &mut [u8; G_DIGEST_SIZE]) {
            G(input, output)
        }

        #[ensures(|out|
            fstar!(r#"$out == Spec.Utils.v_H $input"#))
        ]
        #[inline(always)]
        fn H(input: &[u8], output: &mut [u8; H_DIGEST_SIZE]) {
            H(input, output)
        }

        #[requires(fstar!(r#"v $LEN < pow2 32"#))]
        #[hax_lib::ensures(|out|
            // We need to repeat the pre-condition here because of https://github.com/hacspec/hax/issues/784
            fstar!(r#"v $LEN < pow2 32 ==> $out == Spec.Utils.v_PRF $LEN $input"#))
        ]
        #[inline(always)]
        fn PRF(input: &[u8], output: &mut [u8]) {
            PRF(input, output)
        }

        #[requires(fstar!(r#"v $LEN < pow2 32 /\ (v $K == 2 \/ v $K == 3 \/ v $K == 4)"#))]
        #[ensures(|out|
            fstar!(r#"(v $LEN < pow2 32 /\ (v $K == 2 \/ v $K == 3 \/ v $K == 4)) ==>
                $out == Spec.Utils.v_PRFxN $K $LEN $input"#))
        ]
        #[inline(always)]
        fn PRFxN(input: &[[u8; 33]], output: &mut [u8], out_len: usize) {
            PRFxN(input, output, out_len)
        }

        #[inline(always)]
        fn shake128_init_absorb_final(input: &[[u8; 34]]) -> Self {
            shake128_init_absorb_final(input)
        }

        #[inline(always)]
        fn shake128_squeeze_first_three_blocks(&mut self, outputs: &mut [[u8; THREE_BLOCKS]]) {
            shake128_squeeze_first_three_blocks(self, outputs);
        }

        #[inline(always)]
        fn shake128_squeeze_next_block(&mut self, outputs: &mut [[u8; BLOCK_SIZE]]) {
            shake128_squeeze_next_block(self, outputs);
        }
    }
}

/// A SIMD128 implementation of [`Hash`] for NEON
#[cfg(feature = "simd128")]
pub(crate) mod neon {
    use super::*;
    use libcrux_sha3::neon::x2::{self, incremental::KeccakState};

    /// The state.
    ///
    /// It's only used for SHAKE128.
    /// All other functions don't actually use any members.
    #[cfg_attr(hax, hax_lib::opaque)]
    pub(crate) struct Simd128Hash {
        shake128_state: [KeccakState; 2],
    }

    #[hax_lib::ensures(|result|
        fstar!(r#"$result == Spec.Utils.v_G $input"#))
    ]
    #[inline(always)]
    fn G(input: &[u8]) -> [u8; G_DIGEST_SIZE] {
        let mut digest = [0u8; G_DIGEST_SIZE];
        libcrux_sha3::neon::sha512(&mut digest, input);
        digest
    }

    #[hax_lib::ensures(|result|
        fstar!(r#"$result == Spec.Utils.v_H $input"#))
    ]
    #[inline(always)]
    fn H(input: &[u8]) -> [u8; H_DIGEST_SIZE] {
        let mut digest = [0u8; H_DIGEST_SIZE];
        libcrux_sha3::neon::sha256(&mut digest, input);
        digest
    }

    #[hax_lib::requires(fstar!(r#"v $LEN < pow2 32"#))]
    #[hax_lib::ensures(|result|
        fstar!(r#"$result == Spec.Utils.v_PRF $LEN $input"#))
    ]
    #[inline(always)]
    fn PRF(input: &[u8], output: &mut [u8]) {
        let mut dummy = [0u8; LEN];
        x2::shake256(input, input, output, &mut dummy);
    }

    #[hax_lib::requires(fstar!(r#"v $LEN < pow2 32 /\ (v $K == 2 \/ v $K == 3 \/ v $K == 4)"#))]
    #[hax_lib::ensures(|result|
        fstar!(r#"$result == Spec.Utils.v_PRFxN $K $LEN $input"#))
    ]
    #[inline(always)]
    fn PRFxN<const K: usize, const LEN: usize>(input: &[[u8; 33]; K]) -> [[u8; LEN]; K] {
        debug_assert!(K == 2 || K == 3 || K == 4);
        let mut out = [[0u8; LEN]; K];
        let mut out0 = [0u8; LEN];
        let mut out1 = [0u8; LEN];
        let mut out2 = [0u8; LEN];
        let mut out3 = [0u8; LEN];
        match K as u8 {
            2 => {
                x2::shake256(&input[0], &input[1], &mut out0, &mut out1);
                out[0] = out0;
                out[1] = out1;
            }
            3 => {
                x2::shake256(&input[0], &input[1], &mut out0, &mut out1);
                x2::shake256(&input[2], &input[2], &mut out2, &mut out3);
                out[0] = out0;
                out[1] = out1;
                out[2] = out2;
            }
            4 => {
                x2::shake256(&input[0], &input[1], &mut out0, &mut out1);
                x2::shake256(&input[2], &input[3], &mut out2, &mut out3);
                out[0] = out0;
                out[1] = out1;
                out[2] = out2;
                out[3] = out3;
            }
            _ => unreachable!("Only 2, 3, or 4 are supported for N"),
        }
        out
    }

    #[inline(always)]
    fn shake128_init_absorb_final<const K: usize>(input: [[u8; 34]; K]) -> Simd128Hash {
        debug_assert!(K == 2 || K == 3 || K == 4);
        let mut state = [x2::incremental::init(), x2::incremental::init()];
        match K as u8 {
            2 => {
                x2::incremental::shake128_absorb_final(&mut state[0], &input[0], &input[1]);
            }
            3 => {
                x2::incremental::shake128_absorb_final(&mut state[0], &input[0], &input[1]);
                x2::incremental::shake128_absorb_final(&mut state[1], &input[2], &input[2]);
            }
            4 => {
                x2::incremental::shake128_absorb_final(&mut state[0], &input[0], &input[1]);
                x2::incremental::shake128_absorb_final(&mut state[1], &input[2], &input[3]);
            }
            _ => unreachable!("This function can only called be called with N = 2, 3, 4"),
        }

        Simd128Hash {
            shake128_state: state,
        }
    }

    #[inline(always)]
    fn shake128_squeeze_first_three_blocks<const K: usize>(
        st: &mut Simd128Hash,
    ) -> [[u8; THREE_BLOCKS]; K] {
        debug_assert!(K == 2 || K == 3 || K == 4);

        let mut out = [[0u8; THREE_BLOCKS]; K];
        let mut out0 = [0u8; THREE_BLOCKS];
        let mut out1 = [0u8; THREE_BLOCKS];
        let mut out2 = [0u8; THREE_BLOCKS];
        let mut out3 = [0u8; THREE_BLOCKS];

        match K as u8 {
            2 => {
                x2::incremental::shake128_squeeze_first_three_blocks(
                    &mut st.shake128_state[0],
                    &mut out0,
                    &mut out1,
                );
                out[0] = out0;
                out[1] = out1;
            }
            3 => {
                x2::incremental::shake128_squeeze_first_three_blocks(
                    &mut st.shake128_state[0],
                    &mut out0,
                    &mut out1,
                );
                x2::incremental::shake128_squeeze_first_three_blocks(
                    &mut st.shake128_state[1],
                    &mut out2,
                    &mut out3,
                );
                out[0] = out0;
                out[1] = out1;
                out[2] = out2;
            }
            4 => {
                x2::incremental::shake128_squeeze_first_three_blocks(
                    &mut st.shake128_state[0],
                    &mut out0,
                    &mut out1,
                );
                x2::incremental::shake128_squeeze_first_three_blocks(
                    &mut st.shake128_state[1],
                    &mut out2,
                    &mut out3,
                );
                out[0] = out0;
                out[1] = out1;
                out[2] = out2;
                out[3] = out3;
            }
            _ => unreachable!("This function can only called be called with N = 2, 3, 4"),
        }
        out
    }

    #[inline(always)]
    fn shake128_squeeze_next_block<const K: usize>(st: &mut Simd128Hash) -> [[u8; BLOCK_SIZE]; K] {
        debug_assert!(K == 2 || K == 3 || K == 4);

        let mut out = [[0u8; BLOCK_SIZE]; K];
        let mut out0 = [0u8; BLOCK_SIZE];
        let mut out1 = [0u8; BLOCK_SIZE];
        let mut out2 = [0u8; BLOCK_SIZE];
        let mut out3 = [0u8; BLOCK_SIZE];

        match K as u8 {
            2 => {
                x2::incremental::shake128_squeeze_next_block(
                    &mut st.shake128_state[0],
                    &mut out0,
                    &mut out1,
                );
                out[0] = out0;
                out[1] = out1;
            }
            3 => {
                x2::incremental::shake128_squeeze_next_block(
                    &mut st.shake128_state[0],
                    &mut out0,
                    &mut out1,
                );
                x2::incremental::shake128_squeeze_next_block(
                    &mut st.shake128_state[1],
                    &mut out2,
                    &mut out3,
                );
                out[0] = out0;
                out[1] = out1;
                out[2] = out2;
            }
            4 => {
                x2::incremental::shake128_squeeze_next_block(
                    &mut st.shake128_state[0],
                    &mut out0,
                    &mut out1,
                );
                x2::incremental::shake128_squeeze_next_block(
                    &mut st.shake128_state[1],
                    &mut out2,
                    &mut out3,
                );
                out[0] = out0;
                out[1] = out1;
                out[2] = out2;
                out[3] = out3;
            }
            _ => unreachable!("This function is only called with N = 2, 3, 4"),
        }
        out
    }

    #[hax_lib::attributes]
    impl<const K: usize> Hash<K> for Simd128Hash {
        #[ensures(|out|
            fstar!(r#"$out == Spec.Utils.v_G $input"#))
        ]
        #[inline(always)]
        fn G(input: &[u8]) -> [u8; G_DIGEST_SIZE] {
            G(input)
        }

        #[ensures(|out|
            fstar!(r#"$out == Spec.Utils.v_H $input"#))
        ]
        #[inline(always)]
        fn H(input: &[u8]) -> [u8; H_DIGEST_SIZE] {
            H(input)
        }

        #[requires(fstar!(r#"v $LEN < pow2 32"#))]
        #[ensures(|out|
            // We need to repeat the pre-condition here because of https://github.com/hacspec/hax/issues/784
            fstar!(r#"v $LEN < pow2 32 ==> $out == Spec.Utils.v_PRF $LEN $input"#))
        ]
        #[inline(always)]
        fn PRF(input: &[u8], output: &mut [u8]) {
            PRF(input, output)
        }

        #[requires(fstar!(r#"v $LEN < pow2 32 /\ (v $K == 2 \/ v $K == 3 \/ v $K == 4)"#))]
        #[ensures(|out|
            // We need to repeat the pre-condition here because of https://github.com/hacspec/hax/issues/784
            fstar!(r#"(v $LEN < pow2 32 /\ (v $K == 2 \/ v $K == 3 \/ v $K == 4)) ==>
                $out == Spec.Utils.v_PRFxN $K $LEN $input"#))
        ]
        #[inline(always)]
        fn PRFxN<const LEN: usize>(input: &[[u8; 33]; K]) -> [[u8; LEN]; K] {
            PRFxN::<K, LEN>(input)
        }

        #[inline(always)]
        fn shake128_init_absorb_final(input: [[u8; 34]; K]) -> Self {
            shake128_init_absorb_final(input)
        }

        #[inline(always)]
        fn shake128_squeeze_first_three_blocks(&mut self) -> [[u8; THREE_BLOCKS]; K] {
            shake128_squeeze_first_three_blocks(self)
        }

        #[inline(always)]
        fn shake128_squeeze_next_block(&mut self) -> [[u8; BLOCK_SIZE]; K] {
            shake128_squeeze_next_block(self)
        }
    }
}
