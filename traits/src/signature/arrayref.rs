//! This module contains the traits and related errors for signing and verification where arguments
//! are provided as array references, and outputs are written to mutable array references.

/// A signer. This trait is the most low-level and mostly used in the implementation of other, more
/// usable APIs on top. This trait takes array references as arguments.
///
/// The `SignAux` type is auxiliary information required for signing.
pub trait Sign<SignAux, const SIGNING_KEY_LEN: usize, const SIGNATURE_LEN: usize> {
    /// Sign a payload using a provided signature key. Required auxiliary information is provided using
    /// the `aux` argument.
    fn sign(
        payload: &[u8],
        signing_key: &[u8; SIGNING_KEY_LEN],
        signature: &mut [u8; SIGNATURE_LEN],
        aux: SignAux,
    ) -> Result<(), SignError>;
}

/// A verifier. This trait takes array references as arguments.
///
/// The `VerifyAux` type is auxiliary information required for verification.
pub trait Verify<VerifyAux, const VERIFICATION_KEY_LEN: usize, const SIGNATURE_LEN: usize> {
    /// Verify a payload using a provided verification key. Required auxiliary information is provided using
    /// the `aux` argument.
    fn verify(
        payload: &[u8],
        verification_key: &[u8; VERIFICATION_KEY_LEN],
        signature: &[u8; SIGNATURE_LEN],
        aux: VerifyAux,
    ) -> Result<(), VerifyError>;
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

#[cfg(feature = "error_in_core")]
mod error_in_core {

    impl core::error::Error for super::SignError {}
    impl core::error::Error for super::VerifyError {}
}

/// A signer that does not require auxiliary information. This trait takes array references as arguments.
pub trait SignNoAux<const SIGNING_KEY_LEN: usize, const SIGNATURE_LEN: usize> {
    /// Sign a payload using a provided signature key.
    fn sign(
        payload: &[u8],
        signing_key: &[u8; SIGNING_KEY_LEN],
        signature: &mut [u8; SIGNATURE_LEN],
    ) -> Result<(), SignError>;
}

impl<
        const SIGNING_KEY_LEN: usize,
        const SIGNATURE_LEN: usize,
        T: Sign<(), SIGNING_KEY_LEN, SIGNATURE_LEN>,
    > SignNoAux<SIGNING_KEY_LEN, SIGNATURE_LEN> for T
{
    fn sign(
        payload: &[u8],
        signing_key: &[u8; SIGNING_KEY_LEN],
        signature: &mut [u8; SIGNATURE_LEN],
    ) -> Result<(), SignError> {
        <Self as Sign<(), SIGNING_KEY_LEN, SIGNATURE_LEN>>::sign(
            payload,
            signing_key,
            signature,
            (),
        )
    }
}

/// A verifier that does not require auxiliary information. This trait takes array references as arguments.
pub trait VerifyNoAux<const VERIFICATION_KEY_LEN: usize, const SIGNATURE_LEN: usize> {
    /// Verify a payload using a provided verification key.
    fn verify(
        payload: &[u8],
        verification_key: &[u8; VERIFICATION_KEY_LEN],
        signature: &[u8; SIGNATURE_LEN],
    ) -> Result<(), VerifyError>;
}

impl<
        const VERIFICATION_KEY_LEN: usize,
        const SIGNATURE_LEN: usize,
        T: Verify<(), VERIFICATION_KEY_LEN, SIGNATURE_LEN>,
    > VerifyNoAux<VERIFICATION_KEY_LEN, SIGNATURE_LEN> for T
{
    fn verify(
        payload: &[u8],
        verification_key: &[u8; VERIFICATION_KEY_LEN],
        signature: &[u8; SIGNATURE_LEN],
    ) -> Result<(), VerifyError> {
        <Self as Verify<(), VERIFICATION_KEY_LEN, SIGNATURE_LEN>>::verify(
            payload,
            verification_key,
            signature,
            (),
        )
    }
}
