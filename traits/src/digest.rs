//! This module provides common interface traits for digest/hashing functionality.

pub mod arrayref;
pub mod owned;
pub mod slice;

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

// TODO: rename to `DigestIncrementalBase`
/// Base trait for incremental functionality.
///
/// Traits that are built on top of this trait:
/// - [`slice::DigestIncremental`]
/// - [`arrayref::DigestIncremental`]
/// - [`owned::DigestIncremental`]
pub trait DigestBase {
    /// The digest state.
    type IncrementalState;
    /// Reset the digest state.
    fn reset(state: &mut Self::IncrementalState);
    /// Update the digest state with the `payload`.
    fn update(state: &mut Self::IncrementalState, payload: &[u8]) -> Result<(), UpdateError>;
}

#[derive(Clone)]
/// A hasher that maintains the incremental state.
pub struct Hasher<const N: usize, D: DigestBase> {
    pub state: D::IncrementalState,
}

impl<const N: usize, D: arrayref::DigestIncremental<N>> Default for Hasher<N, D>
where
    D::IncrementalState: Default,
{
    fn default() -> Self {
        Self {
            state: Default::default(),
        }
    }
}

impl<const N: usize, D: DigestBase + slice::Hash> Hasher<N, D> {
    /// Oneshot API. Hash into a digest buffer, provided as a `&mut [u8]` slice.
    pub fn hash_slice(digest: &mut [u8], payload: &[u8]) -> Result<usize, slice::HashError> {
        D::hash(digest, payload)
    }
}

impl<const N: usize, D: slice::DigestIncremental> Hasher<N, D> {
    /// Finalize and write into a digest buffer, provided as a `&mut [u8]` slice.
    pub fn finish_slice(&mut self, digest: &mut [u8]) -> Result<usize, slice::FinishError> {
        D::finish(&mut self.state, digest)
    }
}

impl<const N: usize, D: DigestBase> Hasher<N, D> {
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

impl<const N: usize, D: DigestBase + arrayref::Hash<N>> Hasher<N, D> {
    /// Oneshot API. Hash into a digest buffer, provided as a `&mut [u8; N]` array reference.
    pub fn hash(digest: &mut [u8; N], payload: &[u8]) -> Result<(), arrayref::HashError> {
        D::hash(digest, payload)
    }
    /// owned version of `hash()`
    pub fn hash_to_owned(payload: &[u8]) -> Result<[u8; N], arrayref::HashError> {
        <D as owned::Hash<N>>::hash(payload)
    }
}
