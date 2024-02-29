#![allow(non_snake_case)]

use crate::digest::{self, digest_size, Algorithm, Shake128State};

use super::constants::H_DIGEST_SIZE;

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
pub(crate) fn XOF_absorb<const K: usize>(input: [[u8; 34]; K]) -> [Shake128State; K] {
    let mut state: [Shake128State; K] = core::array::from_fn(|_| Shake128State::new());
    for i in 0..K {
        state[i].absorb_final(&input[i]);
    }
    state
}

#[inline(always)]
pub(crate) fn XOF_squeeze_three_blocks<const K: usize>(
    mut xof_state: [Shake128State; K],
) -> ([[u8; 168 * 3]; K], [Shake128State; K]) {
    let mut output = [[0; 168 * 3]; K];
    for i in 0..K {
        output[i] = xof_state[i].squeeze_nblocks();
    }
    (output, xof_state)
}

#[inline(always)]
pub(crate) fn XOF_squeeze_block<const K: usize>(
    mut xof_state: [Shake128State; K],
) -> ([[u8; 168]; K], [Shake128State; K]) {
    let mut out = [[0u8; 168]; K];
    for i in 0..K {
        out[i] = xof_state[i].squeeze_nblocks();
    }

    (out, xof_state)
}
