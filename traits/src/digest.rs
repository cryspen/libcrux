pub mod arrayref;
pub mod owned;
pub mod slice;

#[derive(Clone, Default)]
pub struct Hasher<const N: usize, D: arrayref::Digest<N>> {
    pub state: D::IncrementalState,
}

impl<const N: usize, D: arrayref::Digest<N>> Hasher<N, D> {
    pub fn update(&mut self, payload: &[u8]) -> Result<(), arrayref::UpdateError> {
        D::update(&mut self.state, payload)
    }
    pub fn reset(&mut self) {
        D::reset(&mut self.state)
    }
    pub fn finish(&mut self, digest: &mut [u8; N]) {
        D::finish(&mut self.state, digest)
    }
}
