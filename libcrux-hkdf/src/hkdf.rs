//! HKDF
//!
//! This crate implements HKDF on SHA 1 and SHA 2 (except for SHA 224).

pub(crate) mod hacl_hkdf;

use hacl_hkdf::{HkdfMode, HkdfSha2_256, HkdfSha2_384, HkdfSha2_512};

/// The HKDF algorithm defining the used hash function.
#[derive(Copy, Clone, Debug, PartialEq)]
pub enum Algorithm {
    Sha256,
    Sha384,
    Sha512,
}

impl Algorithm {
    /// Returns the length of the underlying hash function.
    pub const fn hash_len(self) -> usize {
        match self {
            Algorithm::Sha256 => 32,
            Algorithm::Sha384 => 48,
            Algorithm::Sha512 => 64,
        }
    }
}

/// HKDF Errors
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Error {
    /// The requested output key material in expand was too large for the used
    /// hash function.
    OkmTooLarge,
    /// At least one function argument has been too large to process.
    ArgumentsTooLarge,
}

/// HKDF extract using hash function `mode`, `salt`, and the input key material `ikm`.
/// Returns the pre-key material in a vector of tag length.
pub fn extract(alg: Algorithm, salt: impl AsRef<[u8]>, ikm: impl AsRef<[u8]>) -> Vec<u8> {
    let salt = salt.as_ref();
    let ikm = ikm.as_ref();
    match alg {
        Algorithm::Sha256 => allocbuf(|prk| HkdfSha2_256::extract(prk, salt, ikm)),
        Algorithm::Sha384 => allocbuf(|prk| HkdfSha2_384::extract(prk, salt, ikm)),
        Algorithm::Sha512 => allocbuf(|prk| HkdfSha2_512::extract(prk, salt, ikm)),
    }
}

/// HKDF expand using hash function `mode`, pre-key material `prk`, `info`, and output length `okm_len`.
/// Returns the key material in a vector of length `okm_len` or [`Error::OkmLengthTooLarge`]
/// if the requested output length is too large.
pub fn expand(
    alg: Algorithm,
    prk: impl AsRef<[u8]>,
    info: impl AsRef<[u8]>,
    okm_len: usize,
) -> Result<Vec<u8>, Error> {
    let prk = prk.as_ref();
    let info = info.as_ref();
    match alg {
        Algorithm::Sha256 => HkdfSha2_256::expand_vec(prk, info, okm_len),
        Algorithm::Sha384 => HkdfSha2_384::expand_vec(prk, info, okm_len),
        Algorithm::Sha512 => HkdfSha2_512::expand_vec(prk, info, okm_len),
    }
}

/// HKDF using hash function `mode`, `salt`, input key material `ikm`, `info`, and output length `okm_len`.
/// Calls `extract` and `expand` with the given input.
/// Returns the key material in a vector of length `okm_len` or [`Error::OkmLengthTooLarge`]
/// if the requested output length is too large.
pub fn hkdf(
    mode: Algorithm,
    salt: impl AsRef<[u8]>,
    ikm: impl AsRef<[u8]>,
    info: impl AsRef<[u8]>,
    okm_len: usize,
) -> Result<Vec<u8>, Error> {
    let salt = salt.as_ref();
    let ikm = ikm.as_ref();
    let info = info.as_ref();

    match mode {
        Algorithm::Sha256 => HkdfSha2_256::hkdf_vec(salt, ikm, info, okm_len),
        Algorithm::Sha384 => HkdfSha2_384::hkdf_vec(salt, ikm, info, okm_len),
        Algorithm::Sha512 => HkdfSha2_512::hkdf_vec(salt, ikm, info, okm_len),
    }
}

fn allocbuf<const N: usize, F: Fn(&mut [u8; N])>(f: F) -> Vec<u8> {
    let mut buf = [0u8; N];
    f(&mut buf);
    buf.into()
}
