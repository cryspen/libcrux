#![allow(non_snake_case)]

use crate::digest::{self, digest_size, Algorithm};

use super::constants::H_DIGEST_SIZE;

pub(crate) fn G(input: &[u8]) -> [u8; digest_size(Algorithm::Sha3_512)] {
    crate::digest::sha3_512(input)
}

pub(crate) fn H(input: &[u8]) -> [u8; H_DIGEST_SIZE] {
    crate::digest::sha3_256(input)
}

pub(crate) fn PRF<const LEN: usize>(input: &[u8]) -> [u8; LEN] {
    digest::shake256::<LEN>(input)
}

// At the moment, this function is just a stub, and does not actually implement
// 4xKeccak. Implementation of 4xKeccak is being tracked in:
// https://github.com/cryspen/libcrux/issues/102
pub(crate) fn XOFx4<const LEN: usize, const K: usize>(input: [[u8; 34]; K]) -> [[u8; LEN]; K] {
    let mut out = [[0u8; LEN]; K];
    for i in 0..K {
        out[i] = digest::shake128::<LEN>(&input[i]);
    }
    out
}

pub(crate) fn KDF<const LEN: usize>(input: &[u8]) -> [u8; LEN] {
    digest::shake256::<LEN>(input)
}
