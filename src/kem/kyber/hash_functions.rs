#![allow(non_snake_case)]
#![allow(non_camel_case_types)]

use libcrux_platform::simd256_support;

use crate::digest::{self, digest_size, Algorithm};

use super::constants::{H_DIGEST_SIZE, REJECTION_SAMPLING_SEED_SIZE};

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
pub(crate) fn XOFx4<const K: usize>(
    input: [[u8; 34]; K],
) -> [[u8; REJECTION_SAMPLING_SEED_SIZE]; K] {
    let mut out = [[0u8; REJECTION_SAMPLING_SEED_SIZE]; K];

    if !simd256_support() || !cfg!(simd256) {
        // Without SIMD256 support we fake it and call shak128 4 times.
        // While shak128x4 does this too, this is faster because we only do the
        // required number of invocations (K).
        for i in 0..K {
            out[i] = digest::shake128::<REJECTION_SAMPLING_SEED_SIZE>(&input[i]);
        }
    } else {
        // Always do 4 SHA3 at a time even if we need less.
        // XXX: Cast for hax extraction
        match K as u8 {
            2 => {
                let (d0, d1, _, _) = digest::shake128x4::<REJECTION_SAMPLING_SEED_SIZE>(
                    &input[0], &input[1], &input[0], &input[1],
                );
                out[0] = d0;
                out[1] = d1;
            }
            3 => {
                let (d0, d1, d2, _) = digest::shake128x4::<REJECTION_SAMPLING_SEED_SIZE>(
                    &input[0], &input[1], &input[2], &input[0],
                );
                out[0] = d0;
                out[1] = d1;
                out[2] = d2;
            }
            4 => {
                let (d0, d1, d2, d3) = digest::shake128x4::<REJECTION_SAMPLING_SEED_SIZE>(
                    &input[0], &input[1], &input[2], &input[3],
                );
                out[0] = d0;
                out[1] = d1;
                out[2] = d2;
                out[3] = d3;
            }
            _ => unreachable!(),
        };
    }

    out
}

// The following API uses the repeated squeeze API
// Currently it only supports Scalar SHAKE, adapting it to SIMD SHAKE is a todo
type XOF_state = crate::digest::incremental::AbsorbOnceSqueezeManyShake128;

#[inline(always)]
pub(crate) fn XOF_absorb<const K: usize>(input: [[u8; 34]; K]) -> [XOF_state; K] {
    let mut out =
        core::array::from_fn(|_| crate::digest::incremental::AbsorbOnceSqueezeManyShake128::new());

    for i in 0..K {
        out[i].absorb(&input[i]);
    }
    out
}

#[inline(always)]
pub(crate) fn XOF_squeeze_three_blocks<const K: usize>(state: &mut [XOF_state; K]) -> [[u8;168*3];K] {
    let mut out = [[0; 168 * 3];K];
       
    for i in 0..K {
        out[i] = state[i].squeeze_nblocks();
    }
    out
}

#[inline(always)]
pub(crate) fn XOF_squeeze_block<const K: usize>(state: &mut [XOF_state; K]) -> [[u8;168];K] {
    let mut out = [[0; 168];K];
       
    for i in 0..K {
        out[i] = state[i].squeeze_nblocks();
    }
    out
}
