use crate::impl_hacl::*;
use libcrux_traits::digest::{
    arrayref, slice, DigestIncrementalBase, Hasher, InitializeDigestState, UpdateError,
};

use crate::impl_hacl::SupportsOutLen;

macro_rules! impl_digest_traits {
    ($out_size:ident, $type:ty, $blake2:ty, $hasher:ty, $set:ty, $builder:ty) => {
        // Digest state initialization
        impl<const $out_size: usize> InitializeDigestState for $blake2
        where
            // implement for supported digest lengths only
            $set: SupportsOutLen<$out_size>,
        {
            fn new() -> Self {
                <$builder>::new_unkeyed().build_const_digest_len().into()
            }
        }

        // Oneshot hash trait implementation
        impl<const $out_size: usize> arrayref::Hash<$out_size> for $type
        where
            // implement for supported digest lengths only
            $set: SupportsOutLen<$out_size>,
        {
            fn hash(
                digest: &mut [u8; $out_size],
                payload: &[u8],
            ) -> Result<(), arrayref::HashError> {
                let mut digest_state = <$blake2>::new();
                <Self as DigestIncrementalBase>::update(&mut digest_state, payload).map_err(
                    |e| match e {
                        UpdateError::InvalidPayloadLength | UpdateError::MaximumLengthExceeded => {
                            arrayref::HashError::InvalidPayloadLength
                        }
                        UpdateError::Unknown => arrayref::HashError::Unknown,
                    },
                )?;
                <Self as arrayref::DigestIncremental<$out_size>>::finish(&mut digest_state, digest);

                Ok(())
            }
        }
        // Oneshot hash slice trait implementation
        impl<const $out_size: usize> slice::Hash for $type
        where
            // implement for supported digest lengths only
            $set: SupportsOutLen<$out_size>,
        {
            fn hash(digest: &mut [u8], payload: &[u8]) -> Result<usize, slice::HashError> {
                let digest: &mut [u8; $out_size] = digest
                    .try_into()
                    .map_err(|_| slice::HashError::InvalidDigestLength)?;

                <Self as arrayref::Hash<$out_size>>::hash(digest, payload)?;

                Ok($out_size)
            }
        }

        // Digest incremental base trait implementation
        impl<const $out_size: usize> DigestIncrementalBase for $type
        where
            // implement for supported digest lengths only
            $set: SupportsOutLen<$out_size>,
        {
            type IncrementalState = $blake2;

            fn update(state: &mut Self::IncrementalState, chunk: &[u8]) -> Result<(), UpdateError> {
                // maps all known errors returned by this function
                state.update(chunk).map_err(|e| match e {
                    Error::InvalidChunkLength => UpdateError::InvalidPayloadLength,
                    Error::MaximumLengthExceeded => UpdateError::MaximumLengthExceeded,
                    _ => UpdateError::Unknown,
                })
            }
            fn reset(state: &mut Self::IncrementalState) {
                state.reset()
            }
        }

        // Digest incremental slice trait implementation
        impl<const $out_size: usize> slice::DigestIncremental for $type
        where
            // implement for supported digest lengths only
            $set: SupportsOutLen<$out_size>,
        {
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
        }

        // Digest incremental arrayref trait implementation
        impl<const $out_size: usize> arrayref::DigestIncremental<$out_size> for $type
        where
            // implement for supported digest lengths only
            $set: SupportsOutLen<$out_size>,
        {
            fn finish(state: &mut Self::IncrementalState, dst: &mut [u8; $out_size]) {
                state.finalize(dst)
            }
        }

        // Convert to `libcrux_traits::digest::Hasher`
        impl<const $out_size: usize> From<$blake2> for $hasher
        where
            // implement for supported digest lengths only
            $set: SupportsOutLen<$out_size>,
        {
            fn from(state: $blake2) -> Self {
                Self { state }
            }
        }
    };
}

/// A struct that implements [`libcrux_traits::digest`] traits.
///
/// [`Blake2bHasher`] is a convenience hasher for this struct.
pub struct Blake2bHash<const OUT_SIZE: usize>;

impl_digest_traits!(
    OUT_SIZE,
    Blake2bHash<OUT_SIZE>,
    Blake2b<ConstKeyLenConstDigestLen<0, OUT_SIZE>>,
    Blake2bHasher<OUT_SIZE>,
    Blake2b<LengthBounds>,
    Blake2bBuilder<'_, &()>
);

/// A hasher for [`Blake2bHash`].
pub type Blake2bHasher<const OUT_SIZE: usize> = Hasher<OUT_SIZE, Blake2bHash<OUT_SIZE>>;

/// A struct that implements [`libcrux_traits::digest`] traits.
///
/// [`Blake2sHasher`] is a convenience hasher for this struct.
pub struct Blake2sHash<const OUT_SIZE: usize>;
impl_digest_traits!(
    OUT_SIZE,
    Blake2sHash<OUT_SIZE>,
    Blake2s<ConstKeyLenConstDigestLen<0, OUT_SIZE>>,
    Blake2sHasher<OUT_SIZE>,
    Blake2s<LengthBounds>,
    Blake2sBuilder<'_, &()>
);

/// A hasher for [`Blake2sHash`].
pub type Blake2sHasher<const OUT_SIZE: usize> = Hasher<OUT_SIZE, Blake2sHash<OUT_SIZE>>;
