//! HKDF
//!
//! This crate implements HKDF on SHA 1 and SHA 2 (except for SHA 224).

pub(crate) mod hacl_hkdf;

/// The HKDF algorithm defining the used hash function.
#[derive(Copy, Clone, Debug, PartialEq)]
pub enum Algorithm {
    Sha256,
    Sha384,
    Sha512,
}

/// HKDF Errors
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Error {
    OkmLengthTooLarge,
}

/// HKDF extract using hash function `mode`, `salt`, and the input key material `ikm`.
/// Returns the pre-key material in a vector of tag length.
pub fn extract(alg: Algorithm, salt: impl AsRef<[u8]>, ikm: impl AsRef<[u8]>) -> Vec<u8> {
    match alg {
        Algorithm::Sha256 => {
            crate::hacl_hkdf::sha2_256::extract(salt.as_ref(), ikm.as_ref()).into()
        }
        Algorithm::Sha384 => {
            crate::hacl_hkdf::sha2_384::extract(salt.as_ref(), ikm.as_ref()).into()
        }
        Algorithm::Sha512 => {
            crate::hacl_hkdf::sha2_512::extract(salt.as_ref(), ikm.as_ref()).into()
        }
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
    match alg {
        Algorithm::Sha256 => {
            crate::hacl_hkdf::sha2_256::vec::expand(prk.as_ref(), info.as_ref(), okm_len)
                .map_err(|_| Error::OkmLengthTooLarge)
        }
        Algorithm::Sha384 => {
            crate::hacl_hkdf::sha2_384::vec::expand(prk.as_ref(), info.as_ref(), okm_len)
                .map_err(|_| Error::OkmLengthTooLarge)
        }
        Algorithm::Sha512 => {
            crate::hacl_hkdf::sha2_512::vec::expand(prk.as_ref(), info.as_ref(), okm_len)
                .map_err(|_| Error::OkmLengthTooLarge)
        }
    }
}

/// HKDF using hash function `mode`, `salt`, input key material `ikm`, `info`, and output length `okm_len`.
/// Calls `extract` and `expand` with the given input.
/// Returns the key material in a vector of length `okm_len` or [`Error::OkmLengthTooLarge`]
/// if the requested output length is too large.
pub fn hkdf(
    mode: Algorithm,
    salt: &[u8],
    ikm: &[u8],
    info: &[u8],
    okm_len: usize,
) -> Result<Vec<u8>, Error> {
    let prk = extract(mode, salt, ikm);
    expand(mode, prk, info, okm_len)
}
