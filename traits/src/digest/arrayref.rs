#[derive(Debug)]
pub enum HashError {
    PayloadTooLong,
}

#[derive(Debug)]
pub enum UpdateError {
    PayloadTooLong,
}

pub trait Digest<const OUTPUT_LEN: usize> {
    type IncrementalState: Default;

    /// Oneshot API
    fn hash(digest: &mut [u8; OUTPUT_LEN], payload: &[u8]) -> Result<(), HashError>;

    fn update(state: &mut Self::IncrementalState, payload: &[u8]) -> Result<(), UpdateError>;

    fn finish(state: &mut Self::IncrementalState, digest: &mut [u8; OUTPUT_LEN]);

    fn reset(state: &mut Self::IncrementalState);
}
