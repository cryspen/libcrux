#![allow(non_snake_case)]

use super::constants::H_DIGEST_SIZE;
const G_DIGEST_SIZE: usize = 64;

use libcrux_sha3::portable::{
    self,
    incremental::{
        shake128_absorb_final, shake128_init, shake128_squeeze_first_three_blocks,
        shake128_squeeze_next_block,
    },
    KeccakState,
};
pub(crate) fn G(input: &[u8]) -> [u8; G_DIGEST_SIZE] {
    let mut digest = [0u8; G_DIGEST_SIZE];
    portable::sha512(&mut digest, input);
    digest
}

pub(crate) fn H(input: &[u8]) -> [u8; H_DIGEST_SIZE] {
    let mut digest = [0u8; H_DIGEST_SIZE];
    portable::sha256(&mut digest, input);
    digest
}

pub(crate) fn PRF<const LEN: usize>(input: &[u8]) -> [u8; LEN] {
    let mut digest = [0u8; LEN];
    portable::shake256(&mut digest, input);
    digest
}

// #[inline(always)]
// pub(crate) fn absorb<const K: usize>(input: [[u8; 34]; K]) -> Shake128StateX4 {
//     debug_assert!(K == 2 || K == 3 || K == 4);

//     let mut state = Shake128StateX4::new();
//     // XXX: We need to do this dance to get it through hax and eurydice for now.
//     let mut data: [&[u8]; K] = [&[0u8]; K];
//     for i in 0..K {
//         data[i] = &input[i] as &[u8];
//     }
//     state.absorb_final(data);
//     state
// }

#[inline(always)]
pub(crate) fn absorb<const K: usize>(input: [[u8; 34]; K]) -> [KeccakState; K] {
    debug_assert!(K == 2 || K == 3 || K == 4);

    let mut state = [shake128_init(); K];
    for i in 0..K {
        shake128_absorb_final(&mut state[i], &input[i]);
    }
    state
}

const BLOCK_SIZE: usize = 168;
const THREE_BLOCKS: usize = BLOCK_SIZE * 3;

// #[inline(always)]
// pub(crate) fn squeeze_three_blocks<const K: usize>(
//     xof_state: &mut Shake128StateX4,
// ) -> [[u8; THREE_BLOCKS]; K] {
//     let output: [[u8; THREE_BLOCKS]; K] = xof_state.squeeze_blocks();
//     let mut out = [[0u8; THREE_BLOCKS]; K];
//     for i in 0..K {
//         out[i] = output[i];
//     }
//     out
// }

#[inline(always)]
pub(crate) fn squeeze_three_blocks<const K: usize>(
    xof_state: &mut [KeccakState; K],
) -> [[u8; THREE_BLOCKS]; K] {
    debug_assert!(K == 2 || K == 3 || K == 4);

    let mut out = [[0u8; THREE_BLOCKS]; K];
    for i in 0..K {
        shake128_squeeze_first_three_blocks(&mut xof_state[i], &mut out[i]);
    }
    out
}

// #[inline(always)]
// pub(crate) fn squeeze_block<const K: usize>(
//     xof_state: &mut Shake128StateX4,
// ) -> [[u8; BLOCK_SIZE]; K] {
//     let output: [[u8; BLOCK_SIZE]; K] = xof_state.squeeze_blocks();
//     let mut out = [[0u8; BLOCK_SIZE]; K];
//     for i in 0..K {
//         out[i] = output[i];
//     }
//     out
// }

#[inline(always)]
pub(crate) fn squeeze_block<const K: usize>(
    xof_state: &mut [KeccakState; K],
) -> [[u8; BLOCK_SIZE]; K] {
    debug_assert!(K == 2 || K == 3 || K == 4);

    let mut out = [[0u8; BLOCK_SIZE]; K];
    for i in 0..K {
        shake128_squeeze_next_block(&mut xof_state[i], &mut out[i]);
    }
    out
}

/// Free the memory of the state.
///
/// **NOTE:** That this needs to be done manually for now.
#[inline(always)]
pub(crate) fn free_state<const K: usize>(_xof_state: [KeccakState; K]) {
    // xof_state.free_memory();
}
