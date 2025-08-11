#[derive(Debug)]
pub enum HashError {
    InvalidPayloadLength,
}

#[derive(Debug)]
pub enum UpdateError {
    InvalidPayloadLength,
    MaximumLengthExceeded,
    Unknown,
}

pub trait DigestIncremental<const OUTPUT_LEN: usize>: super::DigestBase {
    fn update(state: &mut Self::IncrementalState, payload: &[u8]) -> Result<(), UpdateError>;

    fn finish(state: &mut Self::IncrementalState, digest: &mut [u8; OUTPUT_LEN]);

    fn reset(state: &mut Self::IncrementalState);
}

pub trait Hash<const OUTPUT_LEN: usize> {
    /// Oneshot API
    fn hash(digest: &mut [u8; OUTPUT_LEN], payload: &[u8]) -> Result<(), HashError>;
}
