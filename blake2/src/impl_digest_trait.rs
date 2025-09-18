use crate::impl_hacl::*;
use libcrux_traits::digest::{arrayref, slice, DigestIncrementalBase, Hasher, UpdateError};

// Implements sets of allowed digest sizes
mod digest_size_support {
    pub(super) struct Blake2bOutSupport;
    pub(super) struct Blake2sOutSupport;

    // a marker trait indicating whether something is supported
    pub(super) trait SupportsLen<const LEN: usize> {}

    // this helps us implement SupportsLen for more than one number
    macro_rules! support_out_lens {
    ($ty:ty, $($supported:expr),*) => {
        $( impl SupportsLen<$supported> for $ty {})*
    };
}
    support_out_lens!(
        Blake2bOutSupport,
        1,
        2,
        3,
        4,
        5,
        6,
        7,
        8,
        9,
        10,
        11,
        12,
        13,
        14,
        15,
        16,
        17,
        18,
        19,
        20,
        21,
        22,
        23,
        24,
        25,
        26,
        27,
        28,
        29,
        30,
        31,
        32,
        33,
        34,
        35,
        36,
        37,
        38,
        39,
        40,
        41,
        42,
        43,
        44,
        45,
        46,
        47,
        48,
        49,
        50,
        51,
        52,
        53,
        54,
        55,
        56,
        57,
        58,
        59,
        60,
        61,
        62,
        63,
        64
    );
    support_out_lens!(
        Blake2sOutSupport,
        1,
        2,
        3,
        4,
        5,
        6,
        7,
        8,
        9,
        10,
        11,
        12,
        13,
        14,
        15,
        16,
        17,
        18,
        19,
        20,
        21,
        22,
        23,
        24,
        25,
        26,
        27,
        28,
        29,
        30,
        31,
        32
    );
}

use digest_size_support::{Blake2bOutSupport, Blake2sOutSupport, SupportsLen};

macro_rules! impl_digest_traits {
    ($out_size:ident, $type:ty, $blake2:ty, $hasher:ty, $set:ident) => {
        impl<const $out_size: usize> DigestIncrementalBase for $type
        where
            // implement for supported digest lengths only
            $set: SupportsLen<$out_size>,
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

        impl<const $out_size: usize> slice::DigestIncremental for $type
        where
            // implement for supported digest lengths only
            $set: SupportsLen<$out_size>,
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

        impl<const $out_size: usize> arrayref::DigestIncremental<$out_size> for $type
        where
            // implement for supported digest lengths only
            $set: SupportsLen<$out_size>,
        {
            fn finish(state: &mut Self::IncrementalState, dst: &mut [u8; $out_size]) {
                state.finalize(dst)
            }
        }

        impl<const $out_size: usize> From<$blake2> for $hasher
        where
            // implement for supported digest lengths only
            $set: SupportsLen<$out_size>,
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
    Blake2bOutSupport
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
    Blake2sOutSupport
);

/// A hasher for [`Blake2sHash`].
pub type Blake2sHasher<const OUT_SIZE: usize> = Hasher<OUT_SIZE, Blake2sHash<OUT_SIZE>>;
