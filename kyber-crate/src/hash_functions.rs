#![allow(non_snake_case)]

use libcrux_platform::simd256_support;

use libcrux::digest::{self, digest_size, Algorithm};

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
        if K == 2 {
            let (d0, d1, _, _) = digest::shake128x4::<REJECTION_SAMPLING_SEED_SIZE>(
                &input[0], &input[1], &input[0], &input[1],
            );
            out[0] = d0;
            out[1] = d1;
        } else if K == 3 {
            let (d0, d1, d2, _) = digest::shake128x4::<REJECTION_SAMPLING_SEED_SIZE>(
                &input[0], &input[1], &input[2], &input[0],
            );
            out[0] = d0;
            out[1] = d1;
            out[2] = d2;
        } else if K == 4 {
            let (d0, d1, d2, d3) = digest::shake128x4::<REJECTION_SAMPLING_SEED_SIZE>(
                &input[0], &input[1], &input[2], &input[3],
            );
            out[0] = d0;
            out[1] = d1;
            out[2] = d2;
            out[3] = d3;
        } else {
            unreachable!()
        };
    }

    out
}
