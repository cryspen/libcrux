//! This module contains the traits and related errors for hashers that take array references as
//! arguments and write the outputs to mutable array references.
//!

#[derive(Debug, PartialEq)]
/// Error indicating that hashing failed.
pub enum HashError {
    /// The length of the provided payload is invalid.
    InvalidPayloadLength,
}

impl core::fmt::Display for HashError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let text = match self {
            HashError::InvalidPayloadLength => "the length of the provided payload is invalid",
        };

        f.write_str(text)
    }
}

#[cfg(feature = "error-in-core")]
mod error_in_core {

    impl core::error::Error for super::HashError {}
}

/// A trait for incremental hashing, where the output is written into a provided buffer.
pub trait DigestIncremental<const OUTPUT_LEN: usize>: super::DigestIncrementalBase {
    /// Writes the digest into `digest`.
    ///
    /// Note that the digest state can be continued to be used, to extend the digest.
    fn finish(state: &mut Self::IncrementalState, digest: &mut [u8; OUTPUT_LEN]);
}

/// A trait for oneshot hashing, where the output is written into a provided buffer.
pub trait Hash<const OUTPUT_LEN: usize> {
    /// Writes the digest for the given input byte slice, into `digest` in immediate mode.
    fn hash(digest: &mut [u8; OUTPUT_LEN], payload: &[u8]) -> Result<(), HashError>;
}
