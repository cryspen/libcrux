use crate::hacl;

#[derive(Debug)]
pub enum Error {
    InvalidStateFinished,
    ModeUnsupportedForStreaming,
}

/// The Digest Algorithm.
#[derive(Copy, Clone, Debug, PartialEq)]
#[repr(u32)]
pub enum Algorithm {
    Sha1 = 1,
    Sha224 = 2,
    Sha256 = 3,
    Sha384 = 4,
    Sha512 = 5,
    Blake2s = 6,
    Blake2b = 7,
    Sha3_224 = 8,
    Sha3_256 = 9,
    Sha3_384 = 10,
    Sha3_512 = 11,
}

impl From<u32> for Algorithm {
    fn from(v: u32) -> Algorithm {
        match v {
            1 => Algorithm::Sha1,
            2 => Algorithm::Sha224,
            3 => Algorithm::Sha256,
            4 => Algorithm::Sha384,
            5 => Algorithm::Sha512,
            6 => Algorithm::Blake2s,
            7 => Algorithm::Blake2b,
            8 => Algorithm::Sha3_224,
            9 => Algorithm::Sha3_256,
            10 => Algorithm::Sha3_384,
            11 => Algorithm::Sha3_512,
            _ => panic!("Unknown Digest mode {}", v),
        }
    }
}

impl From<Algorithm> for u32 {
    fn from(v: Algorithm) -> u32 {
        match v {
            Algorithm::Sha1 => 1,
            Algorithm::Sha224 => 2,
            Algorithm::Sha256 => 3,
            Algorithm::Sha384 => 4,
            Algorithm::Sha512 => 5,
            Algorithm::Blake2s => 6,
            Algorithm::Blake2b => 7,
            Algorithm::Sha3_224 => 8,
            Algorithm::Sha3_256 => 9,
            Algorithm::Sha3_384 => 10,
            Algorithm::Sha3_512 => 11,
        }
    }
}

/// Returns the output size of a digest.
pub const fn digest_size(mode: Algorithm) -> usize {
    match mode {
        Algorithm::Sha1 => 20,
        Algorithm::Sha224 => 28,
        Algorithm::Sha256 => 32,
        Algorithm::Sha384 => 48,
        Algorithm::Sha512 => 64,
        Algorithm::Blake2s => 32,
        Algorithm::Blake2b => 64,
        Algorithm::Sha3_224 => 28,
        Algorithm::Sha3_256 => 32,
        Algorithm::Sha3_384 => 48,
        Algorithm::Sha3_512 => 64,
    }
}

impl Algorithm {
    pub fn size(self) -> usize {
        digest_size(self)
    }
}

pub type Sha2_224Digest = [u8; digest_size(Algorithm::Sha3_224)];
pub type Sha2_256Digest = [u8; digest_size(Algorithm::Sha3_256)];
pub type Sha2_384Digest = [u8; digest_size(Algorithm::Sha3_384)];
pub type Sha2_512Digest = [u8; digest_size(Algorithm::Sha3_512)];

pub type Sha3_224Digest = [u8; digest_size(Algorithm::Sha3_224)];
pub type Sha3_256Digest = [u8; digest_size(Algorithm::Sha3_256)];
pub type Sha3_384Digest = [u8; digest_size(Algorithm::Sha3_384)];
pub type Sha3_512Digest = [u8; digest_size(Algorithm::Sha3_512)];
// Single-shot API

/// Create the digest for the given `data` and mode `alg`.
/// The output has length `get_digest_size(alg)`.
pub fn hash<const LEN: usize>(alg: Algorithm, _payload: &[u8]) -> [u8; LEN] {
    assert!(LEN == digest_size(alg));
    match alg {
        Algorithm::Sha1 => todo!(),
        Algorithm::Sha224 => todo!(),
        Algorithm::Sha256 => todo!(),
        Algorithm::Sha384 => todo!(),
        Algorithm::Sha512 => todo!(),
        Algorithm::Blake2s => todo!(),
        Algorithm::Blake2b => todo!(),
        Algorithm::Sha3_224 => todo!(),
        Algorithm::Sha3_256 => todo!(),
        Algorithm::Sha3_384 => todo!(),
        Algorithm::Sha3_512 => todo!(),
    }
}

// SHAKE messages from SHA 3

/// SHAKE 128
pub fn shake128(data: &[u8], out_len: usize) -> Vec<u8> {
    hacl::hash::shake128(data, out_len)
}

/// SHAKE 256
pub fn shake256(data: &[u8], out_len: usize) -> Vec<u8> {
    hacl::hash::shake256(data, out_len)
}
