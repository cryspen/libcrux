//! HKDF
//!
//! This crate implements HKDF on SHA 1 and SHA 2 (except for SHA 224).

#[cfg(feature = "hacl")]
pub mod hacl;

#[cfg(feature = "hacl")]
mod impl_hacl;

pub use impl_hacl::{HkdfSha2_256, HkdfSha2_384, HkdfSha2_512};

pub trait HkdfMode<const HASH_LEN: usize> {
    /// The hash algorithm used in this HKDF mode.
    const MODE: Algorithm;

    /// HKDF extract using the `salt` and the input key material `ikm`.
    /// The result is written to `prk`.
    ///
    /// Returns nothing on success.
    /// Returns [`Error::ArgumentsTooLarge`] if one of `ikm` or `salt` is longer than [`u32::MAX`]
    /// bytes.
    fn extract(prk: &mut [u8; HASH_LEN], salt: &[u8], ikm: &[u8]) -> Result<(), Error>;

    /// HKDF expand using the pre-key material `prk` and `info`. The output length
    /// is defined through the type of the `okm` parameter, that the output is written to.
    ///
    /// Returns nothing on success.
    /// Returns [`Error::OkmTooLarge`] if the requested `OKM_LEN` is large.
    /// Returns [`Error::ArgumentsTooLarge`] if `prk` or `info` is longer than [`u32::MAX`] bytes.
    fn expand<const OKM_LEN: usize>(
        okm: &mut [u8; OKM_LEN],
        prk: &[u8],
        info: &[u8],
    ) -> Result<(), Error>;

    /// HKDF expand using the pre-key material `prk` and `info`. The output length
    /// is defined by the parameter `okm_len`.
    ///
    /// Returns the key material in a [`Vec<u8>`] of length `okm_len` on success.
    /// Returns [`Error::OkmTooLarge`] if the requested `okm_len` is too large.
    /// Returns [`Error::ArgumentsTooLarge`] if `prk` or `info` is longer than [`u32::MAX`] bytes.
    fn expand_vec(prk: &[u8], info: &[u8], okm_len: usize) -> Result<Vec<u8>, Error>;

    /// HKDF using the `salt`, input key material `ikm`, `info`.
    /// The result is written to `okm`.
    /// The output length is defined through the length of `okm`.
    /// Calls `extract` and `expand` with the given inputs.
    ///
    /// Returns nothing on success.
    /// Returns [`Error::OkmTooLarge`] if the requested `OKM_LEN` is too large.
    /// Returns [`Error::ArgumentsTooLarge`] if one of `ikm`, `salt` or `info` is longer than
    /// [`u32::MAX`] bytes.
    fn hkdf<const OKM_LEN: usize>(
        okm: &mut [u8; OKM_LEN],
        salt: &[u8],
        ikm: &[u8],
        info: &[u8],
    ) -> Result<(), Error> {
        let mut prk = [0u8; HASH_LEN];
        Self::extract(&mut prk, salt, ikm)?;
        Self::expand(okm, &prk, info)
    }

    /// HKDF using the `salt`, input key material `ikm`, `info`.
    /// The output length is defined by the parameter `okm_len`.
    /// Calls `extract` and `expand_vec` with the given input.
    ///
    /// Returns the key material in a [`Vec<u8>`] of length `okm_len` on success.
    /// Returns [`Error::OkmTooLarge`] if the requested `okm_len` is too large.
    /// Returns [`Error::ArgumentsTooLarge`] if `salt`, `ikm` or `info` is longer than [`u32::MAX`] bytes.
    fn hkdf_vec(salt: &[u8], ikm: &[u8], info: &[u8], okm_len: usize) -> Result<Vec<u8>, Error> {
        let mut prk = [0u8; HASH_LEN];
        Self::extract(&mut prk, salt, ikm)?;
        Self::expand_vec(&prk, info, okm_len)
    }
}

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
pub fn extract(
    alg: Algorithm,
    salt: impl AsRef<[u8]>,
    ikm: impl AsRef<[u8]>,
) -> Result<Vec<u8>, Error> {
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

fn allocbuf<const N: usize, T, E, F: Fn(&mut [u8; N]) -> Result<T, E>>(f: F) -> Result<Vec<u8>, E> {
    let mut buf = [0u8; N];

    f(&mut buf).map(|_| buf.into())
}
