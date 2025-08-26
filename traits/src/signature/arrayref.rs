//! This module contains the traits and related errors for signing and verification where arguments
//! are provided as array references, and outputs are written to mutable array references.

use libcrux_secrets::U8;

/// A signer. This trait is the most low-level and mostly used in the implementation of other, more
/// usable APIs on top. This trait takes array references as arguments.
///
/// The `SignAux` type is auxiliary information required for signing.
pub trait Sign<
    const SIGNING_KEY_LEN: usize,
    const VERIFICATION_KEY_LEN: usize,
    const SIGNATURE_LEN: usize,
    const RAND_KEYGEN_LEN: usize,
>
{
    /// Auxiliary information needed for signing.
    type SignAux<'a>;
    /// Sign a payload using a provided signature key. Required auxiliary information is provided using
    /// the `aux` argument.
    fn sign(
        payload: &[u8],
        signing_key: &[U8; SIGNING_KEY_LEN],
        signature: &mut [u8; SIGNATURE_LEN],
        aux: Self::SignAux<'_>,
    ) -> Result<(), SignError>;
    /// Auxiliary information needed for verification.
    type VerifyAux<'a>;
    /// Verify a signature using a provided verification key. Required auxiliary information is provided using
    /// the `aux` argument.
    fn verify(
        payload: &[u8],
        verification_key: &[u8; VERIFICATION_KEY_LEN],
        signature: &[u8; SIGNATURE_LEN],
        aux: Self::VerifyAux<'_>,
    ) -> Result<(), VerifyError>;
    fn keygen(
        signing_key: &mut [U8; SIGNING_KEY_LEN],
        verification_key: &mut [u8; VERIFICATION_KEY_LEN],
        randomness: [U8; RAND_KEYGEN_LEN],
    ) -> Result<(), KeyGenError>;
}

/// Error indicating that signing failed.
#[derive(Debug, PartialEq, Eq)]
pub enum SignError {
    /// The length of the provided payload is invalid.
    InvalidPayloadLength,
    /// Indicates a library error.
    LibraryError,
}

impl core::fmt::Display for SignError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let text = match self {
            SignError::InvalidPayloadLength => "the length of the provided payload is invalid",
            SignError::LibraryError => "indicates a library error",
        };

        f.write_str(text)
    }
}

/// Error indicating that verification failed.
#[derive(Debug, PartialEq, Eq)]
pub enum VerifyError {
    /// The provided signature is invalid.
    InvalidSignature,
    /// The length of the provided signature buffer is invalid.
    InvalidSignatureBufferLength,
    /// The length of the provided payload is invalid.
    InvalidPayloadLength,
    /// Indicates a library error.
    LibraryError,
}

impl core::fmt::Display for VerifyError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let text = match self {
            VerifyError::InvalidSignature => "the provided signature is invalid",
            VerifyError::InvalidSignatureBufferLength => {
                "the length of the provided signature buffer is invalid"
            }
            VerifyError::InvalidPayloadLength => "the length of the provided payload is invalid",
            VerifyError::LibraryError => "indicates a library error",
        };

        f.write_str(text)
    }
}

#[derive(Debug)]
pub enum KeyGenError {
    /// Error generating key with provided randomness
    InvalidRandomness,

    /// Indicates a library error
    LibraryError,
}

impl core::fmt::Display for KeyGenError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let text = match self {
            Self::InvalidRandomness => "error generating key with provided randomness",
            Self::LibraryError => "indicates a library error",
        };

        f.write_str(text)
    }
}

#[cfg(feature = "error_in_core")]
mod error_in_core {

    impl core::error::Error for super::SignError {}
    impl core::error::Error for super::VerifyError {}
    impl core::error::Error for super::KeyGenError {}
}
