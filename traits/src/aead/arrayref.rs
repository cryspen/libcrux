//! This module contains the trait and related errors for an Authenticated
//! Encryption with Associated Data (AEAD) scheme that takes array references
//! as arguments and writes outputs to mutable array references.

/// An Authenticated Encryption with Associated Data (AEAD) scheme. This trait
/// is low-level and is mostly used for implementing other, more usable APIs.
pub trait Aead<const KEY_LEN: usize, const TAG_LEN: usize, const NONCE_LEN: usize> {
    /// Encrypt a plaintext message, producing a ciphertext and an authentication tag.
    /// The `ciphertext` argument must have length `plaintext.len() + TAG_LEN`.
    fn encrypt(
        ciphertext: &mut [u8],
        tag: &mut [u8; TAG_LEN],
        key: &[u8; KEY_LEN],
        nonce: &[u8; NONCE_LEN],
        aad: &[u8],
        plaintext: &[u8],
    ) -> Result<(), EncryptError>;

    /// Decrypt a ciphertext, verifying its authenticity.
    /// The `plaintext` argument must have length `ciphertext.len() - TAG_LEN`.
    fn decrypt(
        plaintext: &mut [u8],
        key: &[u8; KEY_LEN],
        nonce: &[u8; NONCE_LEN],
        aad: &[u8],
        ciphertext: &[u8],
        tag: &[u8; TAG_LEN],
    ) -> Result<(), DecryptError>;
}

/// Error that can occur during encryption.
#[derive(Debug, PartialEq, Eq)]
pub enum EncryptError {
    /// The ciphertext buffer has the wrong length.
    WrongCiphertextText,
    /// The plaintext is too long for this algorithm or implementation.
    PlaintextTooLong,
    /// The AAD is too long for this algorithm or implementation.
    AadTooLong,
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
    WrongPlaintextText,
    /// The plaintext is too long for this algorithm or implementation.
    PlaintextTooLong,
    /// The AAD is too long for this algorithm or implementation.
    AadTooLong,
    /// An unknown error occurred during decryption.
    Unknown,
}
