use crate::impl_hacl::*;
use libcrux_traits::digest::{arrayref, slice, DigestBase, Hasher};

macro_rules! impl_digest_traits {
    ($out_size:ident, $type:ty, $blake2:ty) => {
        impl<const $out_size: usize> DigestBase for $type {
            type IncrementalState = $blake2;
        }

        impl<const $out_size: usize> slice::DigestIncremental for $type {
            fn update(
                state: &mut Self::IncrementalState,
                payload: &[u8],
            ) -> Result<(), slice::UpdateError> {
                <Self as arrayref::DigestIncremental<$out_size>>::update(state, payload)
                    .map_err(slice::UpdateError::from)
            }

            fn finish(
                state: &mut Self::IncrementalState,
                digest: &mut [u8],
            ) -> Result<usize, slice::FinishError> {
                let digest: &mut [u8; $out_size] = digest
                    .try_into()
                    .map_err(|_| slice::FinishError::InvalidDigestLength)?;
                <Self as arrayref::DigestIncremental<$out_size>>::finish(state, digest);

                Ok($out_size)
            }

            fn reset(state: &mut Self::IncrementalState) {
                <Self as arrayref::DigestIncremental<$out_size>>::reset(state);
            }
        }

        impl<const $out_size: usize> arrayref::DigestIncremental<$out_size> for $type {
            fn update(
                state: &mut Self::IncrementalState,
                chunk: &[u8],
            ) -> Result<(), arrayref::UpdateError> {
                // XXX: maps all known errors returned by this function
                state.update(chunk).map_err(|e| match e {
                    Error::InvalidChunkLength => arrayref::UpdateError::InvalidPayloadLength,
                    Error::MaximumLengthExceeded => arrayref::UpdateError::MaximumLengthExceeded,
                    _ => arrayref::UpdateError::Unknown,
                })
            }

            fn finish(state: &mut Self::IncrementalState, dst: &mut [u8; $out_size]) {
                state.finalize(dst)
            }

            fn reset(state: &mut Self::IncrementalState) {
                state.reset()
            }
        }
    };
}

/// A struct that implements [`libcrux_traits::digest`] traits.
///
/// [`Blake2bHasher`] is a convenient hasher for this struct.
pub struct Blake2bHash<const OUT_SIZE: usize>;

impl_digest_traits!(
    OUT_SIZE,
    Blake2bHash<OUT_SIZE>,
    Blake2b<ConstKeyLenConstDigestLen<0, OUT_SIZE>>
);

/// A hasher for [`Blake2bHash`].
pub type Blake2bHasher<const OUT_SIZE: usize> = Hasher<OUT_SIZE, Blake2bHash<OUT_SIZE>>;

/// A struct that implements [`libcrux_traits::digest`] traits.
///
/// [`Blake2sHasher`] is a convenient hasher for this struct.
pub struct Blake2sHash<const OUT_SIZE: usize>;
impl_digest_traits!(
    OUT_SIZE,
    Blake2sHash<OUT_SIZE>,
    Blake2s<ConstKeyLenConstDigestLen<0, OUT_SIZE>>
);

/// A hasher for [`Blake2sHash`].
pub type Blake2sHasher<const OUT_SIZE: usize> = Hasher<OUT_SIZE, Blake2sHash<OUT_SIZE>>;
