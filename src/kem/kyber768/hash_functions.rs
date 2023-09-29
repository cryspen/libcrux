#![allow(non_snake_case)]

use crate::digest::{self, digest_size, Algorithm};

pub(crate) fn G(input: &[u8]) -> [u8; digest_size(Algorithm::Sha3_512)] {
    crate::digest::sha3_512(input)
}

pub(crate) const H_DIGEST_SIZE: usize = digest_size(Algorithm::Sha3_256);
pub(crate) fn H(input: &[u8]) -> [u8; H_DIGEST_SIZE] {
    crate::digest::sha3_256(input)
}

pub(crate) fn PRF<const LEN: usize>(input: &[u8]) -> [u8; LEN] {
    digest::shake256::<LEN>(input)
}

pub(crate) fn XOF<const LEN: usize>(input: &[u8]) -> [u8; LEN] {
    digest::shake128::<LEN>(input)
}

pub(crate) fn KDF<const LEN: usize>(input: &[u8]) -> [u8; LEN] {
    digest::shake256::<LEN>(input)
}
