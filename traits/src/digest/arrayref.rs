//! This module contains the traits and related errors for hashers that take array references as
//! arguments and write the outputs to mutable array references.
//!

#[derive(Debug, PartialEq)]
/// Error indicating that hashing failed.
pub enum HashError {
    /// The length of the provided payload is invalid.
    InvalidPayloadLength,
}

pub trait DigestIncremental<const OUTPUT_LEN: usize>: super::DigestIncrementalBase {
    /// Writes the digest into `digest`.
    ///
    /// Note that the digest state can be continued to be used, to extend the digest.
    fn finish(state: &mut Self::IncrementalState, digest: &mut [u8; OUTPUT_LEN]);
}

pub trait Hash<const OUTPUT_LEN: usize> {
    /// Writes the digest for the given input byte slice, into `digest` in immediate mode.
    fn hash(digest: &mut [u8; OUTPUT_LEN], payload: &[u8]) -> Result<(), HashError>;
}
