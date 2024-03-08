#![allow(non_snake_case)]

use super::constants::H_DIGEST_SIZE;
use crate::digest::{self, digest_size, Algorithm};
use crate::sha3::incremental_x4::Shake128StateX4;

pub(crate) fn G(input: &[u8]) -> [u8; digest_size(Algorithm::Sha3_512)] {
    digest::sha3_512(input)
}

pub(crate) fn H(input: &[u8]) -> [u8; H_DIGEST_SIZE] {
    digest::sha3_256(input)
}

pub(crate) fn PRF<const LEN: usize>(input: &[u8]) -> [u8; LEN] {
    digest::shake256::<LEN>(input)
}

#[inline(always)]
pub(crate) fn absorb<const K: usize>(input: [[u8; 34]; K]) -> Shake128StateX4 {
    debug_assert!(K == 2 || K == 3 || K == 4);

    let mut state = Shake128StateX4::new();
    let data = [
        &input[0] as &[u8],
        &input[1] as &[u8],
        if K > 2 { &input[2] as &[u8] } else { &[] },
        if K > 3 { &input[3] as &[u8] } else { &[] },
    ];
    state.absorb_final(data);
    state
}

const BLOCK_SIZE: usize = 168;
const THREE_BLOCKS: usize = BLOCK_SIZE * 3;

#[inline(always)]
pub(crate) fn squeeze_three_blocks<const K: usize>(
    xof_state: &mut Shake128StateX4,
) -> [[u8; THREE_BLOCKS]; K] {
    let output: [[u8; THREE_BLOCKS]; 4] = xof_state.squeeze_nblocks();
    let mut out = [[0u8; THREE_BLOCKS]; K];
    for i in 0..K {
        out[i] = output[i];
    }
    out
}

#[inline(always)]
pub(crate) fn squeeze_block<const K: usize>(
    xof_state: &mut Shake128StateX4,
) -> [[u8; BLOCK_SIZE]; K] {
    let output: [[u8; BLOCK_SIZE]; 4] = xof_state.squeeze_nblocks();
    let mut out = [[0u8; BLOCK_SIZE]; K];
    for i in 0..K {
        out[i] = output[i];
    }
    out
}

/// Free the memory of the state.
///
/// **NOTE:** That this needs to be done manually for now.
#[inline(always)]
pub(crate) fn free(xof_state: Shake128StateX4) {
    xof_state.free();
}
