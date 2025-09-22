//! This module provides common interface traits for digest/hashing functionality.

pub mod arrayref;
pub mod owned;
pub mod slice;

pub mod consts;
pub mod typed_owned;
pub mod typed_refs;

#[cfg(feature = "generic-tests")]
pub mod tests;

/// Error indicating that updating the digest state failed.
#[derive(Debug, PartialEq)]
pub enum UpdateError {
    /// The length of the provided payload is invalid.
    InvalidPayloadLength,
    ///The maximum input length is exceeded.
    MaximumLengthExceeded,
    /// Unknown error.
    Unknown,
}

/// Error indicating that initializing the digest state failed.
#[derive(Debug, PartialEq)]
pub enum InitializeError {
    /// The provided digest length is invalid.
    InvalidDigestLength,
    /// Unknown error.
    Unknown,
}

impl core::fmt::Display for UpdateError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let text = match self {
            UpdateError::InvalidPayloadLength => "the length of the provided payload is invalid",
            UpdateError::MaximumLengthExceeded => "the maximum input length is exceeded",
            UpdateError::Unknown => "indicates an unknown error",
        };

        f.write_str(text)
    }
}

impl core::fmt::Display for InitializeError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let text = match self {
            InitializeError::InvalidDigestLength => "the provided digest length is invalid",
            InitializeError::Unknown => "indicates an unknown error",
        };

        f.write_str(text)
    }
}

#[cfg(feature = "error-in-core")]
mod error_in_core {

    impl core::error::Error for super::InitializeError {}
    impl core::error::Error for super::UpdateError {}
}

/// Base trait for incremental functionality.
///
/// Traits that are built on top of this trait:
/// - [`slice::DigestIncremental`]
/// - [`arrayref::DigestIncremental`]
/// - [`owned::DigestIncremental`]
pub trait DigestIncrementalBase {
    /// The digest state.
    type IncrementalState;
    /// Initialize a new digest state.
    fn new() -> Result<Self::IncrementalState, InitializeError>;
    /// Reset the digest state.
    fn reset(state: &mut Self::IncrementalState);
    /// Update the digest state with the `payload`.
    fn update(state: &mut Self::IncrementalState, payload: &[u8]) -> Result<(), UpdateError>;
}

#[derive(Clone)]
/// A hasher that maintains the incremental digest state.
pub struct Hasher<const N: usize, D: DigestIncrementalBase> {
    /// The digest state.
    pub state: D::IncrementalState,
}

impl<const N: usize, D: DigestIncrementalBase<IncrementalState: Default>> Default for Hasher<N, D> {
    fn default() -> Self {
        Self {
            state: Default::default(),
        }
    }
}

impl<const N: usize, D: slice::DigestIncremental> Hasher<N, D> {
    /// Finalize and write into a digest buffer, provided as a `&mut [u8]` slice.
    pub fn finish_slice(&mut self, digest: &mut [u8]) -> Result<usize, slice::FinishError> {
        D::finish(&mut self.state, digest)
    }
}

impl<const N: usize, D: DigestIncrementalBase> Hasher<N, D> {
    /// Initialize a new hasher.
    pub fn new() -> Result<Self, InitializeError> {
        D::new().map(|state| Self { state })
    }

    /// Update the digest state with the `payload`.
    pub fn update(&mut self, payload: &[u8]) -> Result<(), UpdateError> {
        D::update(&mut self.state, payload)
    }
    /// Reset the digest state.
    pub fn reset(&mut self) {
        D::reset(&mut self.state)
    }
}

impl<const N: usize, D: arrayref::DigestIncremental<N>> Hasher<N, D> {
    /// Finalize and write into a digest buffer, provided as a `&mut [u8; N]` array reference.
    pub fn finish(&mut self, digest: &mut [u8; N]) {
        D::finish(&mut self.state, digest)
    }
    /// owned version of `finish()`
    pub fn finish_to_owned(&mut self) -> [u8; N] {
        <D as owned::DigestIncremental<N>>::finish(&mut self.state)
    }
}

impl<const N: usize, D: DigestIncrementalBase + slice::Hash> Hasher<N, D> {
    /// Oneshot API. Hash into a digest buffer, provided as a `&mut [u8]` slice.
    pub fn hash_slice(digest: &mut [u8], payload: &[u8]) -> Result<usize, slice::HashError> {
        D::hash(digest, payload)
    }
}

impl<const N: usize, D: DigestIncrementalBase + arrayref::Hash<N>> Hasher<N, D> {
    /// Oneshot API. Hash into a digest buffer, provided as a `&mut [u8; N]` array reference.
    pub fn hash(digest: &mut [u8; N], payload: &[u8]) -> Result<(), arrayref::HashError> {
        D::hash(digest, payload)
    }
    /// owned version of `hash()`
    pub fn hash_to_owned(payload: &[u8]) -> Result<[u8; N], arrayref::HashError> {
        <D as owned::Hash<N>>::hash(payload)
    }
}
