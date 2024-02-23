#![allow(non_snake_case)]

use digest::{shake128_absorb_final, shake128_init, shake128_squeeze_nblocks, Shake128State};
#[cfg(simd256)]
use digest::{
    shake128_absorb_final_x4, shake128_init_x4, shake128_squeeze_nblocks_x4, Shake128StateX4,
};
// use libcrux_platform::simd256_support;

use crate::digest::{self, digest_size, Algorithm};

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

// The following API uses the repeated squeeze API
// The first version uses Scalar SHAKE 128
#[cfg(not(simd256))]
pub(crate) struct XofState<const K: usize> {
    states: [Shake128State; K],
}

#[cfg(not(simd256))]
#[inline(always)]
pub(crate) fn XOF_absorb<const K: usize>(input: [[u8; 34]; K]) -> XofState<K> {
    let mut states = core::array::from_fn(|_| shake128_init());
    for i in 0..K {
        shake128_absorb_final(&mut states[i], &input[i]);
    }
    XofState { states }
}

#[cfg(not(simd256))]
#[inline(always)]
pub(crate) fn XOF_squeeze_three_blocks<const K: usize>(
    xof_state: &mut XofState<K>,
) -> [[u8; 168 * 3]; K] {
    let mut blocks = [[0; 168 * 3]; K];
    for i in 0..K {
        blocks[i] = shake128_squeeze_nblocks(&mut xof_state.states[i]);
    }
    blocks
}

#[cfg(not(simd256))]
#[inline(always)]
pub(crate) fn XOF_squeeze_block<const K: usize>(xof_state: &mut XofState<K>) -> [[u8; 168]; K] {
    let mut block: [[u8; 168]; K] = [[0; 168]; K];
    for i in 0..K {
        block[i] = shake128_squeeze_nblocks(&mut xof_state.states[i]);
    }
    block
}

// The following API uses the repeated squeeze API
// The second version uses SIMD256 SHAKE 128
#[cfg(simd256)]
type XofState<const K: usize> = X4(crate::digest::Shake128StateX4);

#[cfg(simd256)]
#[inline(always)]
pub(crate) fn XOF_absorb<const K: usize>(input: [[u8; 34]; K]) -> XofState<K> {
    let mut state: Shake128StateX4 = shake128_init_x4();
    match K {
        2 => {
            shake128_absorb_final_x4(&mut state, input[0], input[1], input[0], input[0]);
            state
        }
        3 => {
            shake128_absorb_final_x4(&mut state, input[0], input[1], input[2], input[0]);
            state
        }
        4 => {
            shake128_absorb_final_x4(&mut state, input[0], input[1], input[2], input[3]);
            state
        }
        _ => {
            unreachable!()
        }
    }
}

#[cfg(simd256)]
#[inline(always)]
pub(crate) fn XOF_squeeze_three_blocks<const K: usize>(
    state: &mut XofState<K>,
) -> [[u8; 168 * 3]; K] {
    let mut output = [[0; 168 * 3]; K];
    let mut tmp = [[0; 168 * 3]; 2];
    match K {
        2 => {
            shake128_squeeze_nblocks_x4(
                &mut state,
                &mut output[0],
                &mut output[1],
                &mut tmp[0],
                &mut tmp[1],
            );
            output
        }
        3 => {
            shake128_squeeze_nblocks_x4(
                &mut state,
                &mut output[0],
                &mut output[1],
                &mut output[2],
                &mut tmp[1],
            );
            output
        }
        4 => {
            shake128_squeeze_nblocks_x4(
                &mut state,
                &mut output[0],
                &mut output[1],
                &mut output[2],
                &mut output[3],
            );
            output
        }
        _ => {
            unreachable!()
        }
    }
}

#[cfg(simd256)]
#[inline(always)]
pub(crate) fn XOF_squeeze_block<const K: usize>(state: &mut XofState<K>) -> [[u8; 168]; K] {
    let mut output: [[u8; 168]; K] = [[0; 168]; K];
    let mut tmp = [[0; 168 * 3]; 2];
    match K {
        2 => {
            shake128_squeeze_nblocks_x4(
                &mut state,
                &mut output[0],
                &mut output[1],
                &mut tmp[0],
                &mut tmp[1],
            );
            output
        }
        3 => {
            shake128_squeeze_nblocks_x4(
                &mut state,
                &mut output[0],
                &mut output[1],
                &mut output[2],
                &mut tmp[1],
            );
            output
        }
        4 => {
            shake128_squeeze_nblocks_x4(
                &mut state,
                &mut output[0],
                &mut output[1],
                &mut output[2],
                &mut output[3],
            );
            output
        }
        _ => {
            unreachable!()
        }
    }
}
