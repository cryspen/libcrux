#![allow(non_snake_case)]

use super::constants::H_DIGEST_SIZE;
use libcrux_sha3::{x4::Shake128StateX4, *};

pub(crate) fn G(input: &[u8]) -> [u8; digest_size(Algorithm::Sha3_512)] {
    sha512(input)
}

pub(crate) fn H(input: &[u8]) -> [u8; H_DIGEST_SIZE] {
    sha256(input)
}

pub(crate) fn PRF<const LEN: usize>(input: &[u8]) -> [u8; LEN] {
    shake256::<LEN>(input)
}

#[inline(always)]
pub(crate) fn absorb<const K: usize>(input: [[u8; 34]; K]) -> Shake128StateX4 {
    debug_assert!(K == 2 || K == 3 || K == 4);

    let mut state = Shake128StateX4::new();
    // XXX: We need to do this dance to get it through hax and eurydice for now.
    let mut data: [&[u8]; K] = [&[0u8]; K];
    for i in 0..K {
        data[i] = &input[i] as &[u8];
    }
    state.absorb_final(data);
    state
}

const BLOCK_SIZE: usize = 168;
const THREE_BLOCKS: usize = BLOCK_SIZE * 3;

#[inline(always)]
pub(crate) fn squeeze_three_blocks<const K: usize>(
    xof_state: &mut Shake128StateX4,
) -> [[u8; THREE_BLOCKS]; K] {
    let output: [[u8; THREE_BLOCKS]; K] = xof_state.squeeze_blocks();
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
    let output: [[u8; BLOCK_SIZE]; K] = xof_state.squeeze_blocks();
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
pub(crate) fn free_state(xof_state: Shake128StateX4) {
    xof_state.free_memory();
}
