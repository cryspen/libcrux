#![no_std]

/// The length of ChaCha20-Poly1305 keys.
pub const KEY_LEN: usize = 32;

/// The length of Poly1305 MAC tags.
pub const TAG_LEN: usize = 16;

/// The length of ChaCha20-Poly1305 nonces.
pub const NONCE_LEN: usize = 12;

/// Describes the error conditions of the  ChaCha20-Poly1305 AEAD.
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

/// Describes the error conditions of the Poly1305 MAC.
pub enum MacError {
    /// Indicates that the message argument is too large for the library to handle.
    MessageTooLarge,

    /// Indicates that the MAC tag is invalid for that key and message.
    InvalidMacTag,
}

#[cfg(feature = "hacl")]
mod hacl {
    pub(crate) use libcrux_poly1305::hacl::mac_poly1305;

    pub(crate) mod aead_chacha20poly1305;
    pub(crate) mod chacha20;
    pub(crate) mod chacha20_vec32;
}

#[cfg(feature = "hacl")]
mod impl_hacl;

#[cfg(feature = "hacl")]
pub use impl_hacl::*;
