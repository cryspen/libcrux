//! This module contains the trait and related errors for an Authenticated
//! Encryption with Associated Data (AEAD) scheme that takes slices
//! as arguments and writes outputs to mutable slices.

/// An Authenticated Encryption with Associated Data (AEAD) scheme.
///
/// Some implementors of this trait may impose stronger restrictions on the inputs than described
/// here. Check the documentation of the types implementing this trait to make sure which inputs
/// are valid.
pub trait Aead {
    /// Encrypt a plaintext message, producing a ciphertext and an authentication tag.
    /// The arguments `plaintext` and `ciphertext` must have the same length.
    fn encrypt(
        ciphertext: &mut [u8],
        tag: &mut [u8],
        key: &[u8],
        nonce: &[u8],
        aad: &[u8],
        plaintext: &[u8],
    ) -> Result<(), EncryptError>;

    /// Decrypt a ciphertext, verifying its authenticity.
    /// The arguments `plaintext` and `ciphertext` must have the same length.
    fn decrypt(
        plaintext: &mut [u8],
        key: &[u8],
        nonce: &[u8],
        aad: &[u8],
        ciphertext: &[u8],
        tag: &[u8],
    ) -> Result<(), DecryptError>;
}

/// Error that can occur during encryption.
#[derive(Debug, PartialEq, Eq)]
pub enum EncryptError {
    /// The ciphertext buffer has the wrong length.
    WrongCiphertextLength,
    /// The plaintext is too long for this algorithm or implementation.
    PlaintextTooLong,
    /// The AAD is too long for this algorithm or implementation.
    AadTooLong,
    WrongKeyLength,
    WrongTagLength,
    WrongNonceLength,
    /// An unknown error occurred during encryption.
    Unknown,
}

/// Error that can occur during decryption.
#[derive(Debug, PartialEq, Eq)]
pub enum DecryptError {
    /// The authentication tag is invalid; the ciphertext has been tampered with
    /// or the key/nonce/aad is incorrect.
    InvalidTag,
    /// The plaintext buffer has the wrong length.
    WrongPlaintextLength,
    /// The plaintext is too long for this algorithm or implementation.
    PlaintextTooLong,
    /// The AAD is too long for this algorithm or implementation.
    AadTooLong,
    WrongKeyLength,
    WrongTagLength,
    WrongNonceLength,
    /// An unknown error occurred during decryption.
    Unknown,
}

impl From<super::arrayref::EncryptError> for EncryptError {
    fn from(value: super::arrayref::EncryptError) -> Self {
        match value {
            super::arrayref::EncryptError::WrongCiphertextLength => {
                EncryptError::WrongCiphertextLength
            }
            super::arrayref::EncryptError::PlaintextTooLong => EncryptError::PlaintextTooLong,
            super::arrayref::EncryptError::AadTooLong => EncryptError::AadTooLong,
            super::arrayref::EncryptError::Unknown => EncryptError::Unknown,
        }
    }
}

impl From<super::arrayref::DecryptError> for DecryptError {
    fn from(value: super::arrayref::DecryptError) -> Self {
        match value {
            super::arrayref::DecryptError::InvalidTag => DecryptError::InvalidTag,
            super::arrayref::DecryptError::WrongPlaintextLength => {
                DecryptError::WrongPlaintextLength
            }
            super::arrayref::DecryptError::PlaintextTooLong => DecryptError::PlaintextTooLong,
            super::arrayref::DecryptError::AadTooLong => DecryptError::AadTooLong,
            super::arrayref::DecryptError::Unknown => DecryptError::Unknown,
        }
    }
}

/// Implements [`slice::Aead`] based on [`arrayref::Aead`].
///
/// [`slice::Aead`]: Aead
/// [`arrayref::Aead`]: super::arrayref::Aead
#[macro_export]
macro_rules! impl_aead_slice_trait {
    ($type:ty => $key:expr, $tag:expr, $nonce:expr) => {
        impl $crate::aead::slice::Aead for $type {
            fn encrypt(
                ciphertext: &mut [u8],
                tag: &mut [u8],
                key: &[u8],
                nonce: &[u8],
                aad: &[u8],
                plaintext: &[u8],
            ) -> Result<(), $crate::aead::slice::EncryptError> {
                let key: &[u8; $key] = key
                    .try_into()
                    .map_err(|_| $crate::aead::slice::EncryptError::WrongKeyLength)?;
                let tag: &mut [u8; $tag] = tag
                    .try_into()
                    .map_err(|_| $crate::aead::slice::EncryptError::WrongTagLength)?;
                let nonce: &[u8; $nonce] = nonce
                    .try_into()
                    .map_err(|_| $crate::aead::slice::EncryptError::WrongNonceLength)?;

                <Self as $crate::aead::arrayref::Aead<$key, $tag, $nonce>>::encrypt(
                    ciphertext, tag, key, nonce, aad, plaintext,
                )
                .map_err($crate::aead::slice::EncryptError::from)
            }

            fn decrypt(
                plaintext: &mut [u8],
                key: &[u8],
                nonce: &[u8],
                aad: &[u8],
                ciphertext: &[u8],
                tag: &[u8],
            ) -> Result<(), $crate::aead::slice::DecryptError> {
                let key: &[u8; $key] = key
                    .try_into()
                    .map_err(|_| $crate::aead::slice::DecryptError::WrongKeyLength)?;
                let tag: &[u8; $tag] = tag
                    .try_into()
                    .map_err(|_| $crate::aead::slice::DecryptError::WrongTagLength)?;
                let nonce: &[u8; $nonce] = nonce
                    .try_into()
                    .map_err(|_| $crate::aead::slice::DecryptError::WrongNonceLength)?;

                <Self as $crate::aead::arrayref::Aead<$key, $tag, $nonce>>::decrypt(
                    plaintext, key, nonce, aad, ciphertext, tag,
                )
                .map_err($crate::aead::slice::DecryptError::from)
            }
        }
    };
}

pub use impl_aead_slice_trait;
