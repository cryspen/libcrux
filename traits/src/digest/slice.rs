pub trait Digest {
    type IncrementalState: Default;

    /// Oneshot API
    fn hash(digest: &mut [u8], payload: &[u8]) -> Result<(), HashError>;

    // TODO: don't panic?
    fn update(state: &mut Self::IncrementalState, payload: &[u8]);

    fn finish(state: &mut Self::IncrementalState, digest: &mut [u8]) -> Result<(), FinishError>;

    fn reset(state: &mut Self::IncrementalState);
}

pub enum FinishError {
    IncorrectDigestLength,
}

pub enum HashError {
    IncorrectDigestLength,
}

#[macro_export]
macro_rules! impl_digest_trait {
    ($type:ty => $incremental_state:ty, $len:expr) => {
        impl $crate::digest::slice::Digest for $type {
            type IncrementalState = $incremental_state;

            fn hash(
                digest: &mut [u8],
                payload: &[u8],
            ) -> Result<(), $crate::digest::slice::HashError> {
                let digest: &mut [u8; $len] = digest
                    .try_into()
                    .map_err(|_| $crate::digest::slice::HashError::IncorrectDigestLength)?;
                <Self as $crate::digest::arrayref::Digest<$len>>::hash(digest, payload);
                Ok(())
            }
            fn update(state: &mut Self::IncrementalState, payload: &[u8]) {
                <Self as $crate::digest::arrayref::Digest<$len>>::update(state, payload);
            }

            fn finish(
                state: &mut Self::IncrementalState,
                digest: &mut [u8],
            ) -> Result<(), $crate::digest::slice::FinishError> {
                let digest: &mut [u8; $len] = digest
                    .try_into()
                    .map_err(|_| $crate::digest::slice::FinishError::IncorrectDigestLength)?;
                <Self as $crate::digest::arrayref::Digest<$len>>::finish(state, digest);

                Ok(())
            }

            fn reset(state: &mut Self::IncrementalState) {
                <Self as $crate::digest::arrayref::Digest<$len>>::reset(state);
            }
        }
    };
}
pub use impl_digest_trait;
