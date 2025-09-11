use crate::impl_hacl::*;
use libcrux_traits::digest::{
    arrayref,
    consts::HashConsts,
    slice,
    typed_owned::{impl_digest_incremental_typed_owned, impl_hash_typed_owned},
    typed_refs, DigestIncrementalBase, Hasher, InitializeError, UpdateError,
};

macro_rules! impl_runtime_digest_traits {
    ($type:ty, $builder:ty, $max:expr) => {
        impl slice::Hash for $type {
            fn hash(digest: &mut [u8], payload: &[u8]) -> Result<usize, slice::HashError> {
                let digest_len: u8 = digest
                    .len()
                    .try_into()
                    .map_err(|_| slice::HashError::InvalidDigestLength)?;

                let mut hasher = <$builder>::new_unkeyed()
                    .build_var_digest_len(digest_len)
                    .map_err(|_| slice::HashError::InvalidDigestLength)?;

                hasher.update(payload).map_err(|e| match e {
                    Error::InvalidChunkLength | Error::MaximumLengthExceeded => {
                        slice::HashError::InvalidPayloadLength
                    }
                    _ => slice::HashError::Unknown,
                })?;

                hasher
                    .finalize(digest.as_mut())
                    .map_err(|_| slice::HashError::InvalidDigestLength)
            }
        }
        impl typed_refs::Hash for $type {
            fn digest_len_is_valid(&self, len: usize) -> bool {
                (1..=$max).contains(&len)
            }
            fn hash<'a>(
                &self,
                mut digest: typed_refs::DigestMut<'a, Self>,
                payload: &[u8],
            ) -> Result<(), typed_refs::HashError> {
                <$type as slice::Hash>::hash(digest.as_mut(), payload)?;
                Ok(())
            }
        }
    };
}

macro_rules! impl_const_digest_traits {
    ($out_size:ident, $type:ty, $blake2:ty, $hasher:ty, $builder:ty) => {
        impl<const $out_size: usize> DigestIncrementalBase for $type {
            type IncrementalState = $blake2;

            fn new() -> Result<Self::IncrementalState, InitializeError> {
                <$builder>::new_unkeyed()
                    .build_const_digest_len()
                    .map_err(|e| match e {
                        Error::InvalidDigestLength => InitializeError::InvalidDigestLength,
                        _ => InitializeError::Unknown,
                    })
            }
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

        impl<const $out_size: usize> slice::DigestIncremental for $type {
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

        impl<const $out_size: usize> arrayref::DigestIncremental<$out_size> for $type {
            fn finish(state: &mut Self::IncrementalState, dst: &mut [u8; $out_size]) {
                state.finalize(dst)
            }
        }

        impl<const $out_size: usize> arrayref::Hash<$out_size> for $type {
            fn hash(
                digest: &mut [u8; $out_size],
                payload: &[u8],
            ) -> Result<(), arrayref::HashError> {
                // Initialize a new incremental hasher
                let mut hasher = <$hasher>::new().map_err(|e| match e {
                    InitializeError::InvalidDigestLength => {
                        arrayref::HashError::InvalidDigestLength
                    }
                    InitializeError::Unknown => arrayref::HashError::Unknown,
                })?;
                // Update the hasher with the payload
                hasher.update(payload).map_err(|e| match e {
                    UpdateError::InvalidPayloadLength => arrayref::HashError::InvalidPayloadLength,
                    UpdateError::MaximumLengthExceeded => arrayref::HashError::InvalidPayloadLength,
                    UpdateError::Unknown => arrayref::HashError::Unknown,
                })?;
                // Finalize and write to digest
                hasher.finish(digest);

                Ok(())
            }
        }

        impl<const $out_size: usize> From<$blake2> for $hasher {
            fn from(state: $blake2) -> Self {
                Self { state }
            }
        }

        impl<const $out_size: usize> HashConsts for $type {
            const DIGEST_SIZE: usize = $out_size;
        }
        impl_hash_typed_owned!($type, $out_size, generic);
        impl_digest_incremental_typed_owned!($type, $out_size, generic);
    };
}

#[derive(Clone, Copy, Debug, Default, PartialEq)]
pub struct ConstDigestLen<const OUT_SIZE: usize>;
#[derive(Clone, Copy, Debug, Default, PartialEq)]
pub struct RuntimeDigestLen;

/// A struct that implements [`libcrux_traits::digest`] traits.
///
/// [`Blake2bHasher`] is a convenience hasher for this struct.
#[derive(Clone, Copy, Debug, Default, PartialEq)]
pub struct Blake2bHash<T> {
    _marker: core::marker::PhantomData<T>,
}

impl_const_digest_traits!(
    OUT_SIZE,
    Blake2bHash<ConstDigestLen<OUT_SIZE>>,
    Blake2b<ConstKeyLenConstDigestLen<0, OUT_SIZE>>,
    Blake2bHasher<OUT_SIZE>,
    Blake2bBuilder<'_, &_>
);

impl_runtime_digest_traits!(Blake2bHash<RuntimeDigestLen>, Blake2bBuilder<'_, &_>, 64);

/// A hasher for [`Blake2bHash`].
pub type Blake2bHasher<const OUT_SIZE: usize> =
    Hasher<OUT_SIZE, Blake2bHash<ConstDigestLen<OUT_SIZE>>>;

/// A struct that implements [`libcrux_traits::digest`] traits.
///
/// [`Blake2sHasher`] is a convenience hasher for this struct.
#[derive(Clone, Copy, Debug, Default, PartialEq)]
pub struct Blake2sHash<T> {
    _marker: core::marker::PhantomData<T>,
}
impl_const_digest_traits!(
    OUT_SIZE,
    Blake2sHash<ConstDigestLen<OUT_SIZE>>,
    Blake2s<ConstKeyLenConstDigestLen<0, OUT_SIZE>>,
    Blake2sHasher<OUT_SIZE>,
    Blake2sBuilder<'_, &_>
);

impl_runtime_digest_traits!(Blake2sHash<RuntimeDigestLen>, Blake2sBuilder<'_, &_>, 32);

/// A hasher for [`Blake2sHash`].
pub type Blake2sHasher<const OUT_SIZE: usize> =
    Hasher<OUT_SIZE, Blake2sHash<ConstDigestLen<OUT_SIZE>>>;
