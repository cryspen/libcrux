#![allow(non_snake_case)]

use super::constants::H_DIGEST_SIZE;
use crate::{
    digest::{self, digest_size, Algorithm},
    sha3,
};

pub(crate) fn G(input: &[u8]) -> [u8; digest_size(Algorithm::Sha3_512)] {
    digest::sha3_512(input)
}

pub(crate) fn H(input: &[u8]) -> [u8; H_DIGEST_SIZE] {
    digest::sha3_256(input)
}

pub(crate) fn PRF<const LEN: usize>(input: &[u8]) -> [u8; LEN] {
    digest::shake256::<LEN>(input)
}

pub(crate) struct Shake128State<const K: usize> {
    #[cfg(not(simd256))]
    state: [sha3::incremental::Shake128State; K],
    #[cfg(simd256)]
    state: [sha3::incremental_x4::Shake128State; K],
}

impl<const K: usize> Shake128State<K> {
    fn new() -> Self {
        #[cfg(simd256)]
        if simd256_support() {
            Self {
                state: core::array::from_fn(|_| sha3::incremental_x4::Shake128State::new()),
            }
        } else {
            Self {
                state: core::array::from_fn(|_| sha3::incremental::Shake128State::new()),
            }
        }
        #[cfg(not(simd256))]
        Self {
            state: core::array::from_fn(|_| sha3::incremental::Shake128State::new()),
        }
    }
}

#[inline(always)]
pub(crate) fn absorb<const K: usize>(input: [[u8; 34]; K]) -> Shake128State<K> {
    debug_assert!(K == 2 || K == 3 || K == 4);

    let mut states = Shake128State::new();
    for i in 0..K {
        states.state[i].absorb_final(&input[i]);
    }
    states
}

const BLOCK_SIZE: usize = 168;
const THREE_BLOCKS: usize = BLOCK_SIZE * 3;

#[inline(always)]
pub(crate) fn squeeze_three_blocks<const K: usize>(
    xof_state: &mut Shake128State<K>,
) -> [[u8; THREE_BLOCKS]; K] {
    let mut out = [[0u8; THREE_BLOCKS]; K];
    for i in 0..K {
        out[i] = xof_state.state[i].squeeze_nblocks();
    }
    out
}

#[inline(always)]
pub(crate) fn squeeze_block<const K: usize>(
    xof_state: &mut Shake128State<K>,
) -> [[u8; BLOCK_SIZE]; K] {
    let mut out = [[0u8; BLOCK_SIZE]; K];
    for i in 0..K {
        out[i] = xof_state.state[i].squeeze_nblocks();
    }
    out
}

/// Free the memory of the state.
///
/// **NOTE:** That this needs to be done manually for now.
#[inline(always)]
pub(crate) fn free<const K: usize>(mut xof_state: Shake128State<K>) {
    for i in 0..K {
        xof_state.state[i].free();
    }
}
