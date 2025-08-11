pub mod arrayref;
pub mod owned;
pub mod slice;

#[derive(Debug, PartialEq)]
pub enum UpdateError {
    InvalidPayloadLength,
    MaximumLengthExceeded,
    Unknown,
}

// TODO: rename
pub trait DigestBase {
    type IncrementalState;
    fn reset(state: &mut Self::IncrementalState);
    fn update(state: &mut Self::IncrementalState, payload: &[u8]) -> Result<(), UpdateError>;
}

#[derive(Clone)]
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
    // TODO: rename
    pub fn hash_slice(digest: &mut [u8], payload: &[u8]) -> Result<usize, slice::HashError> {
        D::hash(digest, payload)
    }
}

impl<const N: usize, D: slice::DigestIncremental> Hasher<N, D> {
    pub fn finish_slice(&mut self, payload: &mut [u8]) -> Result<usize, slice::FinishError> {
        D::finish(&mut self.state, payload)
    }
}

impl<const N: usize, D: DigestBase> Hasher<N, D> {
    pub fn update(&mut self, payload: &[u8]) -> Result<(), UpdateError> {
        D::update(&mut self.state, payload)
    }
    pub fn reset(&mut self) {
        D::reset(&mut self.state)
    }
}

impl<const N: usize, D: arrayref::DigestIncremental<N>> Hasher<N, D> {
    pub fn finish(&mut self, digest: &mut [u8; N]) {
        D::finish(&mut self.state, digest)
    }
    /// owned version of `finish()`
    pub fn finish_to_owned(&mut self) -> [u8; N] {
        <D as owned::DigestIncremental<N>>::finish(&mut self.state)
    }
}

impl<const N: usize, D: DigestBase + arrayref::Hash<N>> Hasher<N, D> {
    pub fn hash(digest: &mut [u8; N], payload: &[u8]) -> Result<(), arrayref::HashError> {
        D::hash(digest, payload)
    }
    /// owned version of `hash()`
    pub fn hash_to_owned(payload: &[u8]) -> Result<[u8; N], arrayref::HashError> {
        <D as owned::Hash<N>>::hash(payload)
    }
}
