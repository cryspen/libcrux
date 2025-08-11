#[derive(Debug, PartialEq)]
pub enum HashError {
    InvalidPayloadLength,
}

#[derive(Debug, PartialEq)]
pub enum UpdateError {
    InvalidPayloadLength,
    MaximumLengthExceeded,
    Unknown,
}

pub trait DigestIncremental<const OUTPUT_LEN: usize>: super::DigestBase {
    fn finish(state: &mut Self::IncrementalState, digest: &mut [u8; OUTPUT_LEN]);
}

pub trait Hash<const OUTPUT_LEN: usize> {
    /// Oneshot API
    fn hash(digest: &mut [u8; OUTPUT_LEN], payload: &[u8]) -> Result<(), HashError>;
}
