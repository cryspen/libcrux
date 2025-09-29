//! This module contains the traits and related errors for signing and verification where arguments
//! are provided as slices, and the results are written to mutable slices.

use libcrux_secrets::U8;

/// A signer. This trait takes slices as arguments.
///
/// The `SignAux` type is auxiliary information required for signing.
///
/// Returns the number of bytes written.
pub trait Sign<const RAND_KEYGEN_LEN: usize> {
    /// Auxiliary information needed for signing.
    type SignAux<'a>;
    /// Sign a payload using a provided signature key. Required auxiliary information is provided using
    /// the `aux` argument.
    fn sign(
        payload: &[u8],
        signing_key: &[U8],
        signature: &mut [u8],
        aux: Self::SignAux<'_>,
    ) -> Result<usize, SignError>;
    /// Auxiliary information needed for verification.
    type VerifyAux<'a>;
    /// Verify a signature using a provided verification key. Required auxiliary information is provided using
    /// the `aux` argument.
    fn verify(
        payload: &[u8],
        verification_key: &[u8],
        signature: &[u8],
        aux: Self::VerifyAux<'_>,
    ) -> Result<(), VerifyError>;
    /// Generate a pair of signing and verification keys.
    ///
    /// It is the responsibility of the caller to ensure  that the `rand` argument is actually
    /// random.
    fn keygen(
        signing_key: &mut [U8],
        verification_key: &mut [u8],
        rand: [U8; RAND_KEYGEN_LEN],
    ) -> Result<(), KeyGenError>;
}

/// Error indicating that signing failed.
#[derive(Debug, PartialEq, Eq)]
pub enum SignError {
    /// The length of the provided signing key is invalid.
    InvalidSigningKeyLength,
    /// The length of the provided signature buffer is invalid.
    InvalidSignatureBufferLength,
    /// The length of the provided payload is invalid.
    InvalidPayloadLength,
    /// Indicates a library error.
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
            SignError::InvalidPayloadLength => "the length of the provided payload is invalid",
            SignError::LibraryError => "indicates a library error",
        };

        f.write_str(text)
    }
}

/// Error indicating that verification failed.
#[derive(Debug, PartialEq, Eq)]
pub enum VerifyError {
    /// The length of the provided payload is invalid.
    InvalidPayloadLength,
    /// The length of the provided verification key is invalid.
    InvalidVerificationKeyLength,
    /// The length of the provided signature buffer is invalid.
    InvalidSignatureBufferLength,
    /// The provided signature is invalid.
    InvalidSignature,
    /// Indicates a library error.
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

/// Error generating key with provided randomness.
#[derive(Debug)]
pub enum KeyGenError {
    /// Error generating key with provided randomness.
    InvalidRandomness,
    /// The length of the provided signing key buffer is invalid.
    InvalidSigningKeyBufferLength,
    /// The length of the provided verification key buffer is invalid.
    InvalidVerificationKeyBufferLength,
    /// Indicates a library error.
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
            super::arrayref::SignError::InvalidPayloadLength => Self::InvalidPayloadLength,
            super::arrayref::SignError::LibraryError => Self::LibraryError,
        }
    }
}
impl From<super::arrayref::VerifyError> for VerifyError {
    fn from(e: super::arrayref::VerifyError) -> Self {
        match e {
            super::arrayref::VerifyError::InvalidSignature => Self::InvalidSignature,
            super::arrayref::VerifyError::InvalidSignatureBufferLength => {
                Self::InvalidSignatureBufferLength
            }
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

/// Implements [`Sign`] for any [`arrayref::Sign`](crate::signature::arrayref::Sign)
#[macro_export]
macro_rules! impl_signature_slice_trait {
    ($type:ty => $sk_len:expr, $vk_len:expr, $sig_len:expr, $rand_keygen_len:expr, $sign_aux:ty, $sign_aux_param:tt, $verify_aux:ty, $verify_aux_param:tt, $byte:ty) => {
        /// The [`slice`](libcrux_traits::signature::slice) version of the Sign trait.
        impl $crate::signature::slice::Sign<$rand_keygen_len> for $type {
            #[doc = "Auxiliary information needed for signing: "]
            #[doc = concat!("`",stringify!($sign_aux_param),"`")]
            #[doc = ". If the type is `()`, then no auxiliary information is required.\n\n"]
            type SignAux<'a> = <$type as $crate::signature::arrayref::Sign<
                $sk_len,
                $vk_len,
                $sig_len,
                $rand_keygen_len,
            >>::SignAux<'a>;

            #[doc = "Sign a payload using a provided signing key and "]
            #[doc = concat!("`",stringify!($sign_aux_param),"`.")]
            fn sign(
                payload: &[u8],
                signing_key: &[$byte],
                signature: &mut [u8],
                $sign_aux_param: $sign_aux,
            ) -> Result<usize, $crate::signature::slice::SignError> {
                let signing_key: &[$byte; $sk_len] = signing_key
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
            #[doc = "Auxiliary information needed for verification: "]
            #[doc = concat!("`",stringify!($verify_aux_param),"`")]
            #[doc = ". If the type is `()`, then no auxiliary information is required.\n\n"]
            type VerifyAux<'a> = <$type as $crate::signature::arrayref::Sign<
                $sk_len,
                $vk_len,
                $sig_len,
                $rand_keygen_len,
            >>::VerifyAux<'a>;
            #[doc = "Verify a signature using a provided verification key and "]
            #[doc = concat!("`",stringify!($verify_aux_param),"`.")]
            fn verify(
                payload: &[u8],
                verification_key: &[u8],
                signature: &[u8],
                $verify_aux_param: $verify_aux,
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
                >>::verify(payload, verification_key, signature, $verify_aux_param)
                .map_err($crate::signature::slice::VerifyError::from)
            }

            fn keygen(
                signing_key: &mut [$byte],
                verification_key: &mut [$byte],
                randomness: [$byte; $rand_keygen_len],
            ) -> Result<(), $crate::signature::slice::KeyGenError> {
                let signing_key: &mut [u8; $sk_len] = signing_key.try_into().map_err(|_| {
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
                >>::keygen(signing_key, verification_key, randomness)
                .map_err($crate::signature::slice::KeyGenError::from)
            }
        }
    };
}
pub use impl_signature_slice_trait;
