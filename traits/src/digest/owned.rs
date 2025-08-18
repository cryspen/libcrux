//! This module contains the traits and related errors for hashers that take array references as
//! arguments and return values as arrays.
//!

use super::arrayref;

pub use arrayref::HashError;

pub trait Hash<const OUTPUT_LEN: usize> {
    /// Returns the digest for the given input byte slice, as an array, in immediate mode.
    fn hash(payload: &[u8]) -> Result<[u8; OUTPUT_LEN], HashError>;
}

pub trait DigestIncremental<const OUTPUT_LEN: usize>: super::DigestBase {
    /// Returns the digest as an array.
    ///
    /// Note that the digest state can be continued to be used, to extend the digest.
    fn finish(state: &mut Self::IncrementalState) -> [u8; OUTPUT_LEN];
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
    fn finish(state: &mut Self::IncrementalState) -> [u8; OUTPUT_LEN] {
        let mut digest = [0; OUTPUT_LEN];
        Self::finish(state, &mut digest);
        digest
    }
}
