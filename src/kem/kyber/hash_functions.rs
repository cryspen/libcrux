#![allow(non_snake_case)]

use crate::digest::{self, digest_size, Algorithm};

use super::constants::{H_DIGEST_SIZE, REJECTION_SAMPLING_SEED_SIZE};

pub(crate) fn G(input: &[u8]) -> [u8; digest_size(Algorithm::Sha3_512)] {
    crate::digest::sha3_512(input)
}

pub(crate) fn H(input: &[u8]) -> [u8; H_DIGEST_SIZE] {
    crate::digest::sha3_256(input)
}

pub(crate) fn PRF<const LEN: usize>(input: &[u8]) -> [u8; LEN] {
    digest::shake256::<LEN>(input)
}

#[inline(always)]
pub(crate) fn XOFx4<const K: usize>(
    input: [[u8; 34]; K],
) -> [[u8; REJECTION_SAMPLING_SEED_SIZE]; K] {
    let mut out = [[0u8; REJECTION_SAMPLING_SEED_SIZE]; K];

    #[cfg(not(simd256))]
    {
        for i in 0..K {
            out[i] = digest::shake128::<REJECTION_SAMPLING_SEED_SIZE>(&input[i]);
        }
        out
    }

    #[cfg(simd256)]
    {
        // Always do 4 SHA3 at a time even if we need less.
        match K {
            2 => {
                let (d0, d1, _, _) = crate::hacl::sha3::simd256::shake128::<
                    REJECTION_SAMPLING_SEED_SIZE,
                >(&input[0], &input[1], &input[0], &input[1]);
                out[0] = d0;
                out[1] = d1;
                out
            }
            3 => {
                let (d0, d1, d2, _) = crate::hacl::sha3::simd256::shake128::<
                    REJECTION_SAMPLING_SEED_SIZE,
                >(&input[0], &input[1], &input[2], &input[0]);
                out[0] = d0;
                out[1] = d1;
                out[2] = d2;
                out
            }
            4 => {
                let (d0, d1, d2, d3) = crate::hacl::sha3::simd256::shake128::<
                    REJECTION_SAMPLING_SEED_SIZE,
                >(&input[0], &input[1], &input[2], &input[3]);
                out[0] = d0;
                out[1] = d1;
                out[2] = d2;
                out[3] = d3;
                out
            }
            _ => unreachable!(),
        }
    }
}
