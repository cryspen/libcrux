use crate::impl_hacl::*;
use libcrux_traits::digest::{arrayref, slice};

macro_rules! impl_digest_trait_const_len {
    ($type:ident, $blake2:ty) => {
        pub struct $type;

        impl<const OUT_SIZE: usize> arrayref::DigestIncremental<OUT_SIZE> for $type {
            type IncrementalState = $blake2;

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

            fn finish(state: &mut Self::IncrementalState, dst: &mut [u8; OUT_SIZE]) {
                state.finalize(dst)
            }

            fn reset(state: &mut Self::IncrementalState) {
                state.reset()
            }
        }
    };
}
macro_rules! impl_digest_trait_dynamic_len {
    ($type:ident, $blake2:ty) => {
        pub struct $type;

        impl slice::DigestIncremental for $type {
            type IncrementalState = $blake2;

            fn update(
                state: &mut Self::IncrementalState,
                chunk: &[u8],
            ) -> Result<(), slice::UpdateError> {
                // XXX: maps all known errors returned by this function
                state.update(chunk).map_err(|e| match e {
                    Error::InvalidChunkLength => slice::UpdateError::InvalidPayloadLength,
                    Error::MaximumLengthExceeded => slice::UpdateError::MaximumLengthExceeded,
                    _ => slice::UpdateError::Unknown,
                })
            }
            fn finish(
                state: &mut Self::IncrementalState,
                dst: &mut [u8],
            ) -> Result<usize, slice::FinishError> {
                // XXX: maps all known errors returned by this function
                state.finalize(dst).map_err(|e| match e {
                    Error::InvalidDigestLength => slice::FinishError::InvalidDigestLength,
                    _ => slice::FinishError::Unknown,
                })
            }
            fn reset(state: &mut Self::IncrementalState) {
                state.reset()
            }
        }
    };
}

impl_digest_trait_const_len!(Blake2sHash, Blake2s<ConstKeyLenConstDigestLen<0, OUT_SIZE>>);
impl_digest_trait_dynamic_len!(Blake2sHashDynamic, Blake2s<ConstKeyLen<0>>);
impl_digest_trait_const_len!(Blake2bHash, Blake2b<ConstKeyLenConstDigestLen<0, OUT_SIZE>>);
impl_digest_trait_dynamic_len!(Blake2bHashDynamic, Blake2b<ConstKeyLen<0>>);
