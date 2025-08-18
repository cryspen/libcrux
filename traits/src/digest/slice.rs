use super::arrayref;

pub trait Hash {
    /// Writes the digest for the given input byte slice, into `digest` in immediate mode.
    fn hash(digest: &mut [u8], payload: &[u8]) -> Result<usize, HashError>;
}
pub trait DigestIncremental: super::DigestBase {
    /// Writes the digest into `digest`.
    ///
    /// Note that the digest state can be continued to be used, to extend the digest.
    fn finish(state: &mut Self::IncrementalState, digest: &mut [u8]) -> Result<usize, FinishError>;
}

#[derive(Debug, PartialEq)]
pub enum FinishError {
    InvalidDigestLength,
    Unknown,
}

#[derive(Debug, PartialEq)]
pub enum HashError {
    InvalidDigestLength,
    InvalidPayloadLength,
}

impl From<arrayref::HashError> for HashError {
    fn from(e: arrayref::HashError) -> Self {
        match e {
            arrayref::HashError::InvalidPayloadLength => Self::InvalidPayloadLength,
        }
    }
}

#[macro_export]
macro_rules! impl_hash_trait {
    ($type:ty => $len:expr) => {
        impl $crate::digest::slice::Hash for $type {
            fn hash(
                digest: &mut [u8],
                payload: &[u8],
            ) -> Result<usize, $crate::digest::slice::HashError> {
                let digest: &mut [u8; $len] = digest
                    .try_into()
                    .map_err(|_| $crate::digest::slice::HashError::InvalidDigestLength)?;
                <Self as $crate::digest::arrayref::Hash<$len>>::hash(digest, payload)
                    .map(|_| $len)
                    .map_err($crate::digest::slice::HashError::from)
            }
        }
    };
}

#[macro_export]
macro_rules! impl_digest_incremental_trait {
    ($type:ty => $incremental_state:ty, $len:expr) => {
        impl $crate::digest::slice::DigestIncremental for $type {
            fn finish(
                state: &mut Self::IncrementalState,
                digest: &mut [u8],
            ) -> Result<usize, $crate::digest::slice::FinishError> {
                let digest: &mut [u8; $len] = digest
                    .try_into()
                    .map_err(|_| $crate::digest::slice::FinishError::InvalidDigestLength)?;
                <Self as $crate::digest::arrayref::DigestIncremental<$len>>::finish(state, digest);

                Ok($len)
            }
        }
    };
}

pub use impl_digest_incremental_trait;
pub use impl_hash_trait;
