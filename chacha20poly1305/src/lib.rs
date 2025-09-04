#![no_std]

use libcrux_traits::aead::{typed_owned, typed_refs};

pub mod xchacha20_poly1305;

mod hacl {
    pub(crate) use libcrux_poly1305::hacl::mac_poly1305;

    pub(crate) mod aead_chacha20poly1305;
    pub(crate) mod chacha20;
}

mod impl_aead_trait;
mod impl_hacl;

pub use impl_aead_trait::ChaCha20Poly1305;
pub use impl_hacl::*;

/// The length of ChaCha20-Poly1305 keys.
pub const KEY_LEN: usize = 32;

/// The length of Poly1305 MAC tags.
pub const TAG_LEN: usize = 16;

/// The length of ChaCha20-Poly1305 nonces.
pub const NONCE_LEN: usize = 12;

/// An owned ChaCha20Poly1305 key.
pub type Key = typed_owned::Key<ChaCha20Poly1305>;
/// An owned ChaCha20Poly1305 tag.
pub type Tag = typed_owned::Tag<ChaCha20Poly1305>;
/// An owned ChaCha20Poly1305 nonce.
pub type Nonce = typed_owned::Nonce<ChaCha20Poly1305>;

/// A referece to a ChaCha20Poly1305 key.
pub type KeyRef<'a> = typed_refs::KeyRef<'a, ChaCha20Poly1305>;
/// A referece to a ChaCha20Poly1305 tag.
pub type TagRef<'a> = typed_refs::TagRef<'a, ChaCha20Poly1305>;
/// A mutable referece to a ChaCha20Poly1305 tag.
pub type TagMut<'a> = typed_refs::TagMut<'a, ChaCha20Poly1305>;
/// A referece to a ChaCha20Poly1305 nonce.
pub type NonceRef<'a> = typed_refs::NonceRef<'a, ChaCha20Poly1305>;

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
