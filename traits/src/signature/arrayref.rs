//! Low-level signature API using array references.
//!
//! This module contains the fundamental traits and error types for digital signature operations
//! where arguments are provided as array references and outputs are written to mutable array
//! references. This is the most basic API that other signature APIs build upon.
//!
//! # Key Features
//! - Fixed-size array arguments for compile-time length checking
//! - Mutable output parameters for zero-allocation operation
//! - Comprehensive error handling for all failure modes
//! - Support for auxiliary signing data through generic associated types

use super::key_centric_owned::SignTypes;
use libcrux_secrets::{Classify, DeclassifyRefMut, U8};

/// Core signing trait using fixed-size array references.
///
/// This trait provides the fundamental interface for digital signature operations using
/// compile-time known array sizes. It serves as the foundation for higher-level APIs.
///
/// # Type Parameters
/// - `SIGNING_KEY_LEN`: Length of signing (private) keys in bytes
/// - `VERIFICATION_KEY_LEN`: Length of verification (public) keys in bytes
/// - `SIGNATURE_LEN`: Length of signatures in bytes
/// - `RAND_KEYGEN_LEN`: Length of randomness required for key generation
///
/// # Associated Types
/// The `SignAux` type represents auxiliary information required for signing operations.
/// This is algorithm-specific and may include salts or nonces.
pub trait Sign<
    const SIGNING_KEY_LEN: usize,
    const VERIFICATION_KEY_LEN: usize,
    const SIGNATURE_LEN: usize,
    const RAND_KEYGEN_LEN: usize,
>:
    Sized
    + SignTypes<
        SigningKey = [U8; SIGNING_KEY_LEN],
        VerificationKey = [u8; VERIFICATION_KEY_LEN],
        Signature = [u8; SIGNATURE_LEN],
        KeyGenRandomness = [U8; RAND_KEYGEN_LEN],
    >
{
    /// Sign a payload using the provided signing key.
    ///
    /// # Parameters
    /// - `payload`: The data to be signed
    /// - `signing_key`: The private key for signing (secured with `U8`)
    /// - `signature`: Output buffer where the signature will be written
    /// - `aux`: Algorithm-specific auxiliary data required for signing
    ///
    /// # Returns
    /// `Ok(())` on successful signing, or [`SignError`] if the operation fails.
    fn sign(
        payload: &[u8],
        signing_key: &[U8; SIGNING_KEY_LEN],
        signature: &mut [u8; SIGNATURE_LEN],
        aux: Self::SignAux<'_>,
    ) -> Result<(), SignError>;

    /// Verify a signature using the provided verification key.
    ///
    /// # Parameters
    /// - `payload`: The original data that was signed
    /// - `verification_key`: The public key for verification
    /// - `signature`: The signature to verify
    ///
    /// # Returns
    /// `Ok(())` if the signature is valid, or [`VerifyError`] if verification fails.
    fn verify(
        payload: &[u8],
        verification_key: &[u8; VERIFICATION_KEY_LEN],
        signature: &[u8; SIGNATURE_LEN],
    ) -> Result<(), VerifyError>;

    /// Generate a pair of signing and verification keys.
    ///
    /// # Parameters
    /// - `signing_key`: Output buffer for the generated private key
    /// - `verification_key`: Output buffer for the generated public key
    /// - `rand`: Cryptographically secure randomness for key generation
    ///
    /// # Security
    /// It is the caller's responsibility to ensure that the `rand` argument contains
    /// cryptographically secure random data. Weak randomness will compromise key security.
    ///
    /// # Returns
    /// `Ok(())` on successful key generation, or [`KeyGenError`] if generation fails.
    fn keygen_derand(
        signing_key: &mut [U8; SIGNING_KEY_LEN],
        verification_key: &mut [u8; VERIFICATION_KEY_LEN],
        rand: &[U8; RAND_KEYGEN_LEN],
    ) -> Result<(), KeyGenError>;

    /// Generate a pair of signing and verification keys.
    ///
    /// # Parameters
    /// - `signing_key`: Output buffer for the generated private key
    /// - `verification_key`: Output buffer for the generated public key
    /// - `rng`: A cryptographic random number generator
    ///
    /// # Returns
    /// `Ok(())` on successful key generation, or [`KeyGenError`] if generation fails.
    fn keygen(
        signing_key: &mut [U8; SIGNING_KEY_LEN],
        verification_key: &mut [u8; VERIFICATION_KEY_LEN],
        rng: &mut impl rand::CryptoRng,
    ) -> Result<(), KeyGenError> {
        let mut rand = [0u8; RAND_KEYGEN_LEN].classify();
        rng.fill_bytes(rand.declassify_ref_mut());
        Self::keygen_derand(signing_key, verification_key, &rand)
    }
}

/// Error type for signing operation failures.
///
/// Represents various ways that a signing operation can fail, from invalid
/// input parameters to internal library errors.
#[derive(Debug, PartialEq, Eq)]
pub enum SignError {
    /// The the provided argument is invalid for this signature algorithm.
    /// It could be that the payload is too long.
    InvalidArgument,
    /// The random value provided is not suitable. For rejection sampling, try again with new
    /// randomness.
    InvalidRandomness,
    /// An internal library error occurred during the signing operation.
    LibraryError,
}

impl core::fmt::Display for SignError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let text = match self {
            SignError::InvalidArgument => "a provided argument is invalid",
            SignError::InvalidRandomness => "the provided randomness is unsuitable",
            SignError::LibraryError => "indicates a library error",
        };

        f.write_str(text)
    }
}

/// Error type for signature verification failures.
///
/// Represents various ways that signature verification can fail, including
/// invalid signatures, malformed inputs, and internal errors.
#[derive(Debug, PartialEq, Eq)]
pub enum VerifyError {
    /// The provided signature is cryptographically invalid or does not match the payload.
    InvalidSignature,
    /// The length of the provided payload is invalid for this signature algorithm.
    InvalidPayloadLength,
    /// An internal library error occurred during verification.
    LibraryError,
}

impl core::fmt::Display for VerifyError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let text = match self {
            VerifyError::InvalidSignature => "the provided signature is invalid",
            VerifyError::InvalidPayloadLength => "the length of the provided payload is invalid",
            VerifyError::LibraryError => "indicates a library error",
        };

        f.write_str(text)
    }
}

/// Error type for key generation failures.
///
/// Represents various ways that key generation can fail, typically due to
/// invalid randomness, or internal library errors.
#[derive(Debug)]
pub enum KeyGenError {
    /// The provided randomness is invalid for key generation.
    /// It makes sense to try again a few times when this error is returned.
    /// If this error is returned consistently, there might be something wrong with the randomness
    /// generator.
    InvalidRandomness,
    /// An internal library error occurred during key generation.
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

#[cfg(feature = "error-in-core")]
mod error_in_core {
    impl core::error::Error for super::SignError {}
    impl core::error::Error for super::VerifyError {}
    impl core::error::Error for super::KeyGenError {}
}
