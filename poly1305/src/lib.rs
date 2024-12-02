#![no_std]

/// The length of ChaCha20-Poly1305 keys.
pub const KEY_LEN: usize = 16;

/// The length of Poly1305 MAC tags.
pub const TAG_LEN: usize = 16;

/// Describes the error conditions of the Poly1305 MAC.
pub enum Error {
    /// Indicates that the message argument is too large for the library to handle.
    MessageTooLarge,

    /// Indicates that the MAC tag is invalid for that key and message.
    InvalidMacTag,
}

#[cfg(all(feature = "hacl", not(feature = "expose-hacl")))]
mod hacl {
    pub(crate) mod mac_poly1305;
}

#[cfg(feature = "expose-hacl")]
pub mod hacl {
    pub mod mac_poly1305;
}

#[cfg(feature = "hacl")]
mod impl_hacl;

#[cfg(feature = "hacl")]
pub use impl_hacl::*;
