use super::arrayref;

pub use arrayref::{HashError, UpdateError};

pub trait Hash<const OUTPUT_LEN: usize> {
    /// Oneshot API
    fn hash(payload: &[u8]) -> Result<[u8; OUTPUT_LEN], HashError>;
}

pub trait DigestIncremental<const OUTPUT_LEN: usize>: super::DigestBase {
    fn update(state: &mut Self::IncrementalState, payload: &[u8]) -> Result<(), UpdateError>;

    fn finish(state: &mut Self::IncrementalState) -> [u8; OUTPUT_LEN];

    fn reset(state: &mut Self::IncrementalState);
}

impl<const OUTPUT_LEN: usize, D: arrayref::Hash<OUTPUT_LEN>> Hash<OUTPUT_LEN> for D {
    fn hash(payload: &[u8]) -> Result<[u8; OUTPUT_LEN], HashError> {
        let mut digest = [0; OUTPUT_LEN];
        Self::hash(&mut digest, payload).map(|_| digest)
    }
}
impl<const OUTPUT_LEN: usize, D: arrayref::DigestIncremental<OUTPUT_LEN>>
    DigestIncremental<OUTPUT_LEN> for D
{
    fn update(state: &mut Self::IncrementalState, payload: &[u8]) -> Result<(), UpdateError> {
        Self::update(state, payload)
    }

    fn finish(state: &mut Self::IncrementalState) -> [u8; OUTPUT_LEN] {
        let mut digest = [0; OUTPUT_LEN];
        Self::finish(state, &mut digest);
        digest
    }

    fn reset(state: &mut Self::IncrementalState) {
        Self::reset(state)
    }
}
