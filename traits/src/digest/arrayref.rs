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
    /// Writes the digest into `digest`.
    ///
    /// Note that the digest state can be continued to be used, to extend the digest.
    fn finish(state: &mut Self::IncrementalState, digest: &mut [u8; OUTPUT_LEN]);
}

pub trait Hash<const OUTPUT_LEN: usize> {
    /// Writes the digest for the given input byte slice, into `digest` in immediate mode.
    fn hash(digest: &mut [u8; OUTPUT_LEN], payload: &[u8]) -> Result<(), HashError>;
}
