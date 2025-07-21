use super::arrayref;

pub trait Hash {
    /// Oneshot API
    fn hash(digest: &mut [u8], payload: &[u8]) -> Result<usize, HashError>;
}
pub trait DigestIncremental {
    type IncrementalState;

    fn update(state: &mut Self::IncrementalState, payload: &[u8]) -> Result<(), UpdateError>;

    fn finish(state: &mut Self::IncrementalState, digest: &mut [u8]) -> Result<usize, FinishError>;

    fn reset(state: &mut Self::IncrementalState);
}

#[derive(Debug)]
pub enum FinishError {
    InvalidDigestLength,
    Unknown,
}

#[derive(Debug)]
pub enum HashError {
    InvalidDigestLength,
    InvalidPayloadLength,
}

#[derive(Debug)]
pub enum UpdateError {
    InvalidPayloadLength,
    MaximumLengthExceeded,
    Unknown,
}

impl From<arrayref::HashError> for HashError {
    fn from(e: arrayref::HashError) -> Self {
        match e {
            arrayref::HashError::InvalidPayloadLength => Self::InvalidPayloadLength,
        }
    }
}

impl From<arrayref::UpdateError> for UpdateError {
    fn from(e: arrayref::UpdateError) -> Self {
        match e {
            arrayref::UpdateError::InvalidPayloadLength => Self::InvalidPayloadLength,
            arrayref::UpdateError::MaximumLengthExceeded => Self::MaximumLengthExceeded,
            arrayref::UpdateError::Unknown => Self::Unknown,
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
            type IncrementalState = $incremental_state;

            fn update(
                state: &mut Self::IncrementalState,
                payload: &[u8],
            ) -> Result<(), $crate::digest::slice::UpdateError> {
                <Self as $crate::digest::arrayref::DigestIncremental<$len>>::update(state, payload)
                    .map_err($crate::digest::slice::UpdateError::from)
            }

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

            fn reset(state: &mut Self::IncrementalState) {
                <Self as $crate::digest::arrayref::DigestIncremental<$len>>::reset(state);
            }
        }
    };
}

pub use impl_digest_incremental_trait;
pub use impl_hash_trait;
