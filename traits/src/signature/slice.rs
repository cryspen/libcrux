//! Dynamic length signature API using slices.
//!
//! This module provides a signature API that works with dynamic-length slices instead of
//! fixed-size arrays. This allows for more flexible buffer management but requires runtime
//! length validation and can accommodate varying signature algorithm requirements.
//!
//! # Key Features
//! - Dynamic buffer sizes using slices for maximum flexibility
//! - Runtime length validation with detailed error reporting
//! - Returns number of bytes written for variable-length operations
//! - Automatic implementation macro for arrayref-based algorithms

use super::key_centric_owned::SignTypes;
use libcrux_secrets::{Classify, DeclassifyRefMut, U8};

/// Signature trait using dynamic-length slices.
///
/// This trait provides a flexible interface for signature operations using slices
/// instead of fixed-size arrays, enabling support for varying buffer sizes and
/// algorithms with different length requirements.
///
/// # Type Parameters
/// - `RAND_KEYGEN_LEN`: Length of randomness required for key generation
///
/// # Associated Types
/// The `SignAux` type represents auxiliary information required for signing operations.
pub trait Sign<const RAND_KEYGEN_LEN: usize>: Sized + SignTypes {
    /// Sign a payload using the provided signing key.
    ///
    /// # Parameters
    /// - `payload`: The data to be signed
    /// - `signing_key`: A slice containing the signing key material
    /// - `signature`: Output buffer where the signature will be written
    /// - `aux`: Algorithm-specific auxiliary data required for signing
    ///
    /// # Returns
    /// The number of bytes written to the signature buffer on success,
    /// or [`SignError`] if signing fails.
    fn sign(
        payload: &[u8],
        signing_key: &[U8],
        signature: &mut [u8],
        aux: Self::SignAux<'_>,
    ) -> Result<usize, SignError>;

    /// Verify a signature using the provided verification key.
    ///
    /// # Parameters
    /// - `payload`: The original data that was signed
    /// - `verification_key`: A slice containing the verification key material
    /// - `signature`: The signature to verify
    ///
    /// # Returns
    /// `Ok(())` if the signature is valid, or [`VerifyError`] if verification fails.
    fn verify(payload: &[u8], verification_key: &[u8], signature: &[u8])
        -> Result<(), VerifyError>;
    /// Generate a pair of signing and verification keys.
    ///
    /// # Parameters
    /// - `signing_key`: Output buffer for the generated signing key
    /// - `verification_key`: Output buffer for the generated verification key
    /// - `rand`: Cryptographically secure randomness for key generation
    ///
    /// # Returns
    /// `Ok(())` on successful key generation, or [`KeyGenError`] if generation fails.
    ///
    /// # Security
    /// It is the caller's responsibility to ensure that the `rand` argument contains
    /// cryptographically secure random data.
    fn keygen_derand(
        signing_key: &mut [U8],
        verification_key: &mut [u8],
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
        signing_key: &mut [U8],
        verification_key: &mut [u8],
        rng: &mut impl rand::CryptoRng,
    ) -> Result<(), KeyGenError> {
        let mut rand = [0u8; RAND_KEYGEN_LEN].classify();
        rng.fill_bytes(rand.declassify_ref_mut());
        Self::keygen_derand(signing_key, verification_key, &rand)
    }
}

/// Error type for signing operation failures with slice-based inputs.
///
/// Extends the basic signing errors with additional failure modes specific
/// to dynamic-length slice operations.
#[derive(Debug, PartialEq, Eq)]
pub enum SignError {
    /// The length of the provided signing key slice is invalid for this algorithm.
    InvalidSigningKeyLength,
    /// The length of the provided signature output buffer is invalid.
    InvalidSignatureBufferLength,
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
            SignError::InvalidSigningKeyLength => {
                "the length of the provided signing key is invalid"
            }
            SignError::InvalidSignatureBufferLength => {
                "the length of the provided signature buffer is invalid"
            }
            SignError::InvalidArgument => "a provided argument is invalid",
            SignError::InvalidRandomness => "the provided randomness is unsuitable",
            SignError::LibraryError => "indicates a library error",
        };

        f.write_str(text)
    }
}

/// Error type for signature verification failures with slice-based inputs.
///
/// Provides detailed error information for verification failures when using
/// dynamic-length slice arguments.
#[derive(Debug, PartialEq, Eq)]
pub enum VerifyError {
    /// The length of the provided payload is invalid for this signature algorithm.
    InvalidPayloadLength,
    /// The length of the provided verification key slice is invalid for this algorithm.
    InvalidVerificationKeyLength,
    /// The length of the provided signature is invalid for this algorithm.
    InvalidSignatureBufferLength,
    /// The provided signature is cryptographically invalid or does not match the payload.
    InvalidSignature,
    /// An internal library error occurred during verification.
    LibraryError,
}

impl core::fmt::Display for VerifyError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let text = match self {
            VerifyError::InvalidSignature => "the provided signature is invalid",
            VerifyError::InvalidVerificationKeyLength => {
                "the length of the provided verification key is invalid"
            }
            VerifyError::InvalidSignatureBufferLength => {
                "the length of the provided signature buffer is invalid"
            }
            VerifyError::InvalidPayloadLength => "the length of the provided payload is invalid",
            VerifyError::LibraryError => "indicates a library error",
        };

        f.write_str(text)
    }
}

/// Error type for key generation failures with slice-based outputs.
///
/// Provides detailed error information for key generation failures when using
/// dynamic-length slice output buffers.
#[derive(Debug)]
pub enum KeyGenError {
    /// The provided randomness is insufficient or invalid for key generation.
    InvalidRandomness,
    /// The length of the provided signing key output buffer is invalid.
    InvalidSigningKeyBufferLength,
    /// The length of the provided verification key output buffer is invalid.
    InvalidVerificationKeyBufferLength,
    /// An internal library error occurred during key generation.
    LibraryError,
}

impl core::fmt::Display for KeyGenError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let text = match self {
            KeyGenError::InvalidRandomness => "error generating key with the provided randomness",
            KeyGenError::InvalidSigningKeyBufferLength => {
                "the length of the provided signing key buffer is invalid"
            }
            KeyGenError::InvalidVerificationKeyBufferLength => {
                "the length of the provided verification key buffer is invalid"
            }
            KeyGenError::LibraryError => "indicates a library error",
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

impl From<super::arrayref::SignError> for SignError {
    fn from(e: super::arrayref::SignError) -> Self {
        match e {
            super::arrayref::SignError::InvalidArgument => Self::InvalidArgument,
            super::arrayref::SignError::InvalidRandomness => Self::InvalidRandomness,
            super::arrayref::SignError::LibraryError => Self::LibraryError,
        }
    }
}
impl From<super::arrayref::VerifyError> for VerifyError {
    fn from(e: super::arrayref::VerifyError) -> Self {
        match e {
            super::arrayref::VerifyError::InvalidSignature => Self::InvalidSignature,
            super::arrayref::VerifyError::InvalidPayloadLength => Self::InvalidPayloadLength,
            super::arrayref::VerifyError::LibraryError => Self::LibraryError,
        }
    }
}

impl From<super::arrayref::KeyGenError> for KeyGenError {
    fn from(e: super::arrayref::KeyGenError) -> Self {
        match e {
            super::arrayref::KeyGenError::InvalidRandomness => Self::InvalidRandomness,
            super::arrayref::KeyGenError::LibraryError => Self::LibraryError,
        }
    }
}

/// Macro to implement the slice-based `Sign` trait from an arrayref implementation.
///
/// This macro automatically generates a slice-based implementation by wrapping
/// an existing arrayref-based `Sign` trait implementation, handling the necessary
/// length validation and array conversions.
///
/// # Parameters
/// - `$type`: The type implementing arrayref::Sign
/// - `$sk_len`: Signing key length in bytes
/// - `$vk_len`: Verification key length in bytes
/// - `$sig_len`: Signature length in bytes
/// - `$rand_keygen_len`: Key generation randomness length in bytes
/// - `$sign_aux`: Type for auxiliary signing data
/// - `$sign_aux_param`: Parameter name for auxiliary data
/// - `$byte`: Byte type (typically `U8` for secret keys)
#[macro_export]
macro_rules! impl_signature_slice_trait {
    ($type:ty => $sk_len:expr, $vk_len:expr, $sig_len:expr, $rand_keygen_len:expr, $sign_aux:ty, $sign_aux_param:tt) => {
        /// The [`slice`](libcrux_traits::signature::slice) version of the Sign trait.
        impl $crate::signature::slice::Sign<$rand_keygen_len> for $type {
            #[doc = "Sign a payload using a provided signing key and "]
            #[doc = concat!("`",stringify!($sign_aux_param),"`.")]
            fn sign(
                payload: &[u8],
                signing_key: &[U8],
                signature: &mut [u8],
                $sign_aux_param: $sign_aux,
            ) -> Result<usize, $crate::signature::slice::SignError> {
                let signing_key: &[U8; $sk_len] = signing_key
                    .try_into()
                    .map_err(|_| $crate::signature::slice::SignError::InvalidSigningKeyLength)?;

                // get the first $sig_len elements
                let signature: &mut [u8; $sig_len] = signature
                    .first_chunk_mut()
                    .ok_or($crate::signature::slice::SignError::InvalidSignatureBufferLength)?;

                <$type as $crate::signature::arrayref::Sign<
                    $sk_len,
                    $vk_len,
                    $sig_len,
                    $rand_keygen_len,
                >>::sign(payload, signing_key, signature, $sign_aux_param)
                .map(|_| $sk_len)
                .map_err($crate::signature::slice::SignError::from)
            }
            #[doc = "Verify a signature using a provided verification key."]
            fn verify(
                payload: &[u8],
                verification_key: &[u8],
                signature: &[u8],
            ) -> Result<(), $crate::signature::slice::VerifyError> {
                let verification_key: &[u8; $vk_len] =
                    verification_key.try_into().map_err(|_| {
                        $crate::signature::slice::VerifyError::InvalidVerificationKeyLength
                    })?;

                let signature: &[u8; $sig_len] = signature.try_into().map_err(|_| {
                    $crate::signature::slice::VerifyError::InvalidSignatureBufferLength
                })?;

                <$type as $crate::signature::arrayref::Sign<
                    $sk_len,
                    $vk_len,
                    $sig_len,
                    $rand_keygen_len,
                >>::verify(payload, verification_key, signature)
                .map_err($crate::signature::slice::VerifyError::from)
            }

            fn keygen_derand(
                signing_key: &mut [U8],
                verification_key: &mut [u8],
                randomness: &[U8; $rand_keygen_len],
            ) -> Result<(), $crate::signature::slice::KeyGenError> {
                let signing_key: &mut [U8; $sk_len] = signing_key.try_into().map_err(|_| {
                    $crate::signature::slice::KeyGenError::InvalidSigningKeyBufferLength
                })?;
                let verification_key: &mut [u8; $vk_len] =
                    verification_key.try_into().map_err(|_| {
                        $crate::signature::slice::KeyGenError::InvalidVerificationKeyBufferLength
                    })?;
                <$type as $crate::signature::arrayref::Sign<
                    $sk_len,
                    $vk_len,
                    $sig_len,
                    $rand_keygen_len,
                >>::keygen_derand(signing_key, verification_key, randomness)
                .map_err($crate::signature::slice::KeyGenError::from)
            }

            fn keygen(
                signing_key: &mut [U8],
                verification_key: &mut [u8],
                rng: &mut impl $crate::rand::CryptoRng,
            ) -> Result<(), $crate::signature::slice::KeyGenError> {
                let signing_key: &mut [U8; $sk_len] = signing_key.try_into().map_err(|_| {
                    $crate::signature::slice::KeyGenError::InvalidSigningKeyBufferLength
                })?;
                let verification_key: &mut [u8; $vk_len] =
                    verification_key.try_into().map_err(|_| {
                        $crate::signature::slice::KeyGenError::InvalidVerificationKeyBufferLength
                    })?;
                <$type as $crate::signature::arrayref::Sign<
                    $sk_len,
                    $vk_len,
                    $sig_len,
                    $rand_keygen_len,
                >>::keygen(signing_key, verification_key, rng)
                .map_err($crate::signature::slice::KeyGenError::from)
            }
        }
    };
}
pub use impl_signature_slice_trait;
