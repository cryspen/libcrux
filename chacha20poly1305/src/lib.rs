#![no_std]

/// The length of ChaCha20-Poly1305 keys.
pub const KEY_LEN: usize = 32;

/// The length of Poly1305 MAC tags.
pub const TAG_LEN: usize = 16;

/// The length of ChaCha20-Poly1305 nonces.
pub const NONCE_LEN: usize = 12;

/// Describes the error conditions of the  ChaCha20-Poly1305 AEAD.
#[derive(Debug)]
pub enum AeadError {
    /// Indicates that the plaintext argument is too large for the library to handle.
    PlaintextTooLarge,
    /// Indicates that the ciphertext argument is too large for the library to handle.
    CiphertextTooLarge,
    /// Indicates that the associated data argument is too large for the library to handle.
    AadTooLarge,
    /// This indicates that the provided destination ciphertext does not fit the ciphertext and tag.
    CiphertextTooShort,
    /// This indicates that the provided destination plaintext is shorter than `ctxt.len() - TAG_LEN`
    /// and thus will not fit the decrypted plaintext
    PlaintextTooShort,
    /// Indicates that the ciphertext is not a valid encryption under the given key and nonce.
    InvalidCiphertext,
}

impl core::fmt::Display for AeadError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let msg = match self {
            AeadError::PlaintextTooLarge => {
                "The plaintext argument is too large for the library to handle"
            }
            AeadError::CiphertextTooLarge => {
                "The ciphertext argument is too large for the library to handle"
            }
            AeadError::AadTooLarge => {
                "The associated data argument is too large for the library to handle"
            }
            AeadError::CiphertextTooShort => {
                "The provided destination ciphertext does not fit the ciphertext and tag"
            }
            AeadError::PlaintextTooShort => {
                "The provided destination plaintext is too short to fit the decrypted plaintext"
            }
            AeadError::InvalidCiphertext => {
                "The ciphertext is not a valid encryption under the given key and nonce."
            }
        };

        f.write_str(msg)
    }
}

/// Describes the error conditions of the Poly1305 MAC.
#[derive(Debug)]
pub enum MacError {
    /// Indicates that the message argument is too large for the library to handle.
    MessageTooLarge,

    /// Indicates that the MAC tag is invalid for that key and message.
    InvalidMacTag,
}

impl core::fmt::Display for MacError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let msg = match self {
            MacError::MessageTooLarge => {
                "The message argument is too large for the library to handle"
            }
            MacError::InvalidMacTag => "The MAC tag is invalid for that key and message",
        };

        f.write_str(msg)
    }
}

mod hacl {
    pub(crate) use libcrux_poly1305::hacl::mac_poly1305;

    pub(crate) mod aead_chacha20poly1305;
    pub(crate) mod chacha20;
}

mod impl_hacl;

pub use impl_hacl::*;
