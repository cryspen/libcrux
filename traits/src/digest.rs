pub mod arrayref;
pub mod owned;
pub mod slice;

#[derive(Clone)]
pub struct SliceHasher<D: slice::DigestIncremental> {
    pub state: D::IncrementalState,
}
impl<D: slice::DigestIncremental> Default for SliceHasher<D>
where
    D::IncrementalState: Default,
{
    fn default() -> Self {
        Self {
            state: Default::default(),
        }
    }
}

impl<D: slice::DigestIncremental> SliceHasher<D> {
    pub fn update(&mut self, payload: &[u8]) -> Result<(), slice::UpdateError> {
        D::update(&mut self.state, payload)
    }
    pub fn reset(&mut self) {
        D::reset(&mut self.state)
    }
    pub fn finish(&mut self, digest: &mut [u8]) -> Result<usize, slice::FinishError> {
        D::finish(&mut self.state, digest)
    }
}

impl<D: slice::DigestIncremental + slice::Hash> SliceHasher<D> {
    pub fn hash(digest: &mut [u8], payload: &[u8]) -> Result<usize, slice::HashError> {
        D::hash(digest, payload)
    }
}

#[derive(Clone)]
pub struct Hasher<const N: usize, D: arrayref::DigestIncremental<N>> {
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

impl<const N: usize, D: arrayref::DigestIncremental<N>> Hasher<N, D> {
    pub fn update(&mut self, payload: &[u8]) -> Result<(), arrayref::UpdateError> {
        D::update(&mut self.state, payload)
    }
    pub fn reset(&mut self) {
        D::reset(&mut self.state)
    }
    pub fn finish(&mut self, digest: &mut [u8; N]) {
        D::finish(&mut self.state, digest)
    }
    /// owned version of `finish()`
    pub fn finish_to_owned(&mut self) -> [u8; N] {
        <D as owned::DigestIncremental<N>>::finish(&mut self.state)
    }
}

// XXX: can't implement this for something that doesn't implement DigestIncremental
impl<const N: usize, D: arrayref::DigestIncremental<N> + arrayref::Hash<N>> Hasher<N, D> {
    pub fn hash(digest: &mut [u8; N], payload: &[u8]) -> Result<(), arrayref::HashError> {
        D::hash(digest, payload)
    }
    /// owned version of `hash()`
    pub fn hash_to_owned(payload: &[u8]) -> Result<[u8; N], arrayref::HashError> {
        <D as owned::Hash<N>>::hash(payload)
    }
}
