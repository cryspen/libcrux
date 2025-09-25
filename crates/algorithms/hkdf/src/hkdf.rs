//! HKDF
//!
//! This crate implements HKDF on SHA2 256, 384 and 512.
#![no_std]

use core::marker::PhantomData;

use libcrux_secrets::{Classify, DeclassifyRef, DeclassifyRefMut, U8};

pub mod hacl;

/// The HKDF algorithm defining the used hash function. Only needed for the functions with dynamic
/// algorithm selection.
#[derive(Copy, Clone, Debug, PartialEq)]
pub enum Algorithm {
    Sha256,
    Sha384,
    Sha512,
}

/// HKDF extract using the `salt` and the input key material `ikm`.
/// The result is written to `prk`.
/// The `algo` argument is used for dynamic algorithm selection.
///
/// Returns nothing on success.
/// Returns [`ExtractError::ArgumentTooLong`] if one of `ikm` or `salt` is longer than [`u32::MAX`]
/// bytes.
/// Returns [`ExtractError::PrkTooShort`] if `prk` is shorter than the hash length.
pub fn extract(
    algo: Algorithm,
    prk: &mut [U8],
    salt: &[u8],
    ikm: &[U8],
) -> Result<(), ExtractError> {
    match algo {
        Algorithm::Sha256 => sha2_256::extract(prk, salt, ikm),
        Algorithm::Sha384 => sha2_384::extract(prk, salt, ikm),
        Algorithm::Sha512 => sha2_512::extract(prk, salt, ikm),
    }
}

/// HKDF extract using the `salt` and the input key material `ikm`.
/// The result is written to `prk`.
/// The `algo` argument is used for dynamic algorithm selection.
///
/// Returns nothing on success.
/// Returns [`ExtractError::ArgumentTooLong`] if one of `ikm` or `salt` is longer than
/// [`u32::MAX`] bytes.
/// Returns [`ExpandError::PrkTooShort`] if `prk` is shorter than hash length.
pub fn expand(algo: Algorithm, okm: &mut [U8], prk: &[U8], info: &[u8]) -> Result<(), ExpandError> {
    match algo {
        Algorithm::Sha256 => sha2_256::expand(okm, prk, info),
        Algorithm::Sha384 => sha2_384::expand(okm, prk, info),
        Algorithm::Sha512 => sha2_512::expand(okm, prk, info),
    }
}

pub fn hkdf(
    algo: Algorithm,
    okm: &mut [U8],
    salt: &[u8],
    ikm: &[U8],
    info: &[u8],
) -> Result<(), ExpandError> {
    match algo {
        Algorithm::Sha256 => sha2_256::hkdf(okm, salt, ikm, info),
        Algorithm::Sha384 => sha2_384::hkdf(okm, salt, ikm, info),
        Algorithm::Sha512 => sha2_512::hkdf(okm, salt, ikm, info),
    }
}

pub struct Sha2_256;
pub struct Sha2_384;
pub struct Sha2_512;

pub struct Hkdf<Algo>(PhantomData<Algo>);

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

macro_rules! impl_hkdf {
    ($struct_name:path, $name:ident, $string_name:literal, $mode:path, $extract:ident, $expand:ident,$hash_len:literal) => {
        pub mod $name {
            use libcrux_secrets::U8;

            use super::*;

            impl Hkdf<$struct_name> {
                /// HKDF extract using the `salt` and the input key material `ikm`.
                /// The result is written to `prk`.
                ///
                /// Returns nothing on success.
                /// Returns [`ExtractError::ArgumentTooLong`] if one of `ikm` or `salt` is longer than
                /// [`u32::MAX`] bytes.
                #[inline(always)]
                pub fn extract_fixed(
                    prk: &mut [U8; $hash_len],
                    salt: &[u8],
                    ikm: &[U8],
                ) -> Result<(), FixedExtractError> {
                    extract_fixed(prk, salt, ikm)
                }

                /// HKDF extract using the `salt` and the input key material `ikm`.
                /// The result is written to `prk`.
                ///
                /// Returns nothing on success.
                /// Returns [`ExtractError::ArgumentTooLong`] if one of `ikm` or `salt` is longer than
                /// [`u32::MAX`] bytes.
                /// Returns [`ExtractError::PrkTooShort`] if `prk` is shorter than hash length.
                #[inline(always)]
                pub fn extract(
                    prk: &mut [U8],
                    salt: &[u8],
                    ikm: &[U8],
                ) -> Result<(), ExtractError> {
                    extract(prk, salt, ikm)
                }

                /// HKDF expand using the pre-key material `prk` and `info`.
                /// The output is written to `okm`.
                ///
                /// Returns nothing on success.
                /// Returns [`ExpandError::OutputTooLong`] if `okm` is too long (longer than
                /// `255 * hash_length`)
                /// Returns [`ExpandError::ArgumentTooLong`] if one of `prk` or `info` is longer than
                /// [`u32::MAX`] bytes.
                #[inline(always)]
                pub fn expand_fixed(
                    okm: &mut [U8],
                    prk: &[U8; $hash_len],
                    info: &[u8],
                ) -> Result<(), FixedExpandError> {
                    if okm.len() > 255 * $hash_len {
                        // Output size is too large. HACL doesn't catch this.
                        return Err(FixedExpandError::OutputTooLong);
                    }

                    expand_fixed(okm, prk, info)
                }

                /// HKDF expand using the pre-key material `prk` and `info`.
                /// The output is written to `okm`.
                ///
                /// Returns nothing on success.
                /// Returns [`ExpandError::OutputTooLong`] if `okm` is too long (longer than
                /// `255 * hash_length`)
                /// Returns [`ExpandError::ArgumentTooLong`] if one of `prk` or `info` is longer than
                /// [`u32::MAX`] bytes.
                /// Returns [`ExpandError::PrkTooShort`] if `prk` is shorter than hash length.
                #[inline(always)]
                pub fn expand(okm: &mut [U8], prk: &[U8], info: &[u8]) -> Result<(), ExpandError> {
                    expand(okm, prk, info)
                }

                /// Full HKDF using the `salt`, input key material `ikm`, `info`.
                /// The result is written to `okm`.
                /// The output length is defined through the length of `okm`.
                /// Calls `extract` and `expand` with the given input.
                ///
                /// Returns nothing on success.
                /// Returns [`ExpandError::OutputTooLong`] if `okm` is too long (longer than
                /// `255 * hash_length`)
                /// Returns [`ExpandError::ArgumentTooLong`] if one of `prk` or `info` is longer than
                /// [`u32::MAX`] bytes.
                #[inline(always)]
                pub fn hkdf(
                    okm: &mut [U8],
                    salt: &[u8],
                    ikm: &[U8],
                    info: &[u8],
                ) -> Result<(), ExpandError> {
                    hkdf(okm, salt, ikm, info)
                }
            }

            /// HKDF extract using the `salt` and the input key material `ikm`.
            /// The result is written to `prk`.
            ///
            /// Returns nothing on success.
            /// Returns [`ExtractError::ArgumentTooLong`] if one of `ikm` or `salt` is longer than
            /// [`u32::MAX`] bytes.
            #[inline(always)]
            pub fn extract_fixed(
                prk: &mut [U8; $hash_len],
                salt: &[u8],
                ikm: &[U8],
            ) -> Result<(), FixedExtractError> {
                Ok(crate::hacl::$extract(
                    prk.declassify_ref_mut(),
                    salt,
                    checked_u32(salt.len())?,
                    ikm.declassify_ref(),
                    checked_u32(ikm.len())?,
                ))
            }

            /// HKDF extract using the `salt` and the input key material `ikm`.
            /// The result is written to `prk`.
            ///
            /// Returns nothing on success.
            /// Returns [`ExtractError::ArgumentTooLong`] if one of `ikm` or `salt` is longer than
            /// [`u32::MAX`] bytes.
            /// Returns [`ExtractError::PrkTooShort`] if `prk` is shorter than hash length.
            #[inline(always)]
            pub fn extract(prk: &mut [U8], salt: &[u8], ikm: &[U8]) -> Result<(), ExtractError> {
                let (prk, _) = prk
                    .split_at_mut_checked($hash_len)
                    .ok_or(ExtractError::PrkTooShort)?;
                let prk: &mut [U8; $hash_len] =
                    prk.try_into().map_err(|_| ExtractError::Unknown)?;

                extract_fixed(prk, salt, ikm).map_err(ExtractError::from)
            }

            /// HKDF expand using the pre-key material `prk` and `info`.
            /// The output is written to `okm`.
            ///
            /// Returns nothing on success.
            /// Returns [`ExpandError::OutputTooLong`] if `okm` is too long (longer than
            /// `255 * hash_length`)
            /// Returns [`ExpandError::ArgumentTooLong`] if one of `prk` or `info` is longer than
            /// [`u32::MAX`] bytes.
            #[inline(always)]
            pub fn expand_fixed(
                mut okm: &mut [U8],
                prk: &[U8; $hash_len],
                info: &[u8],
            ) -> Result<(), FixedExpandError> {
                let okm_len = okm.len();
                if okm_len > 255 * $hash_len {
                    // Output size is too large. HACL doesn't catch this.
                    return Err(FixedExpandError::OutputTooLong);
                }

                Ok(crate::hacl::$expand(
                    okm.declassify_ref_mut(),
                    prk.declassify_ref(),
                    checked_u32(prk.len())?,
                    info,
                    checked_u32(info.len())?,
                    checked_u32(okm_len)?,
                ))
            }

            /// HKDF expand using the pre-key material `prk` and `info`.
            /// The output is written to `okm`.
            ///
            /// Returns nothing on success.
            /// Returns [`ExpandError::OutputTooLong`] if `okm` is too long (longer than
            /// `255 * hash_length`)
            /// Returns [`ExpandError::ArgumentTooLong`] if one of `prk` or `info` is longer than
            /// [`u32::MAX`] bytes.
            /// Returns [`ExpandError::PrkTooShort`] if `prk` is shorter than hash length.
            #[inline(always)]
            pub fn expand(okm: &mut [U8], prk: &[U8], info: &[u8]) -> Result<(), ExpandError> {
                let (prk, _) = prk
                    .split_at_checked($hash_len)
                    .ok_or(ExpandError::PrkTooShort)?;
                let prk: &[U8; $hash_len] = prk.try_into().map_err(|_| ExpandError::Unknown)?;

                expand_fixed(okm, prk, info).map_err(ExpandError::from)
            }

            /// Full HKDF using the `salt`, input key material `ikm`, `info`.
            /// The result is written to `okm`.
            /// The output length is defined through the length of `okm`.
            /// Calls `extract` and `expand` with the given input.
            ///
            /// Returns nothing on success.
            /// Returns [`ExpandError::OutputTooLong`] if `okm` is too long (longer than
            /// `255 * hash_length`)
            /// Returns [`ExpandError::ArgumentTooLong`] if one of `prk` or `info` is longer than
            /// [`u32::MAX`] bytes.
            #[inline(always)]
            pub fn hkdf(
                okm: &mut [U8],
                salt: &[u8],
                ikm: &[U8],
                info: &[u8],
            ) -> Result<(), ExpandError> {
                let mut prk = [0u8.classify(); $hash_len];
                extract(&mut prk, salt, ikm)?;
                expand(okm, &prk, info)
            }
        }
    };
}

impl_hkdf!(
    crate::Sha2_256,
    sha2_256,
    "SHA2-256",
    Algorithm::Sha256,
    extract_sha2_256,
    expand_sha2_256,
    32
);

impl_hkdf!(
    crate::Sha2_384,
    sha2_384,
    "SHA2-384",
    Algorithm::Sha384,
    extract_sha2_384,
    expand_sha2_384,
    48
);

impl_hkdf!(
    crate::Sha2_512,
    sha2_512,
    "SHA2-512",
    Algorithm::Sha512,
    extract_sha2_512,
    expand_sha2_512,
    64
);

fn checked_u32(num: usize) -> Result<u32, ArgumentsTooLongError> {
    num.try_into().map_err(|_| ArgumentsTooLongError)
}

#[derive(Copy, Clone, Debug, PartialEq)]
pub enum FixedExtractError {
    ArgumentTooLong,
    Unknown,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum ExtractError {
    PrkTooShort,
    ArgumentTooLong,
    Unknown,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum FixedExpandError {
    OutputTooLong,
    ArgumentTooLong,
    Unknown,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum ExpandError {
    OutputTooLong,
    PrkTooShort,
    ArgumentTooLong,
    Unknown,
}

#[derive(Copy, Clone, Debug, PartialEq)]
struct ArgumentsTooLongError;

impl From<FixedExtractError> for ExtractError {
    fn from(err: FixedExtractError) -> Self {
        match err {
            FixedExtractError::ArgumentTooLong => ExtractError::ArgumentTooLong,
            FixedExtractError::Unknown => ExtractError::Unknown,
        }
    }
}

impl From<FixedExpandError> for ExpandError {
    fn from(err: FixedExpandError) -> Self {
        match err {
            FixedExpandError::OutputTooLong => ExpandError::OutputTooLong,
            FixedExpandError::ArgumentTooLong => ExpandError::ArgumentTooLong,
            FixedExpandError::Unknown => ExpandError::Unknown,
        }
    }
}

impl From<ExtractError> for ExpandError {
    fn from(err: ExtractError) -> Self {
        match err {
            ExtractError::PrkTooShort => ExpandError::PrkTooShort,
            ExtractError::ArgumentTooLong => ExpandError::ArgumentTooLong,
            ExtractError::Unknown => ExpandError::Unknown,
        }
    }
}

impl From<ArgumentsTooLongError> for FixedExtractError {
    fn from(_: ArgumentsTooLongError) -> Self {
        FixedExtractError::ArgumentTooLong
    }
}
impl From<ArgumentsTooLongError> for FixedExpandError {
    fn from(_: ArgumentsTooLongError) -> Self {
        FixedExpandError::ArgumentTooLong
    }
}
impl From<ArgumentsTooLongError> for ExtractError {
    fn from(_: ArgumentsTooLongError) -> Self {
        ExtractError::ArgumentTooLong
    }
}
impl From<ArgumentsTooLongError> for ExpandError {
    fn from(_: ArgumentsTooLongError) -> Self {
        ExpandError::ArgumentTooLong
    }
}
