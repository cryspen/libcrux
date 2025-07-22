use super::*;
use libcrux_hacl_rs::prelude::*;
use libcrux_traits::digest::arrayref::Hash;

/// The different Sha2 algorithms.
#[derive(Clone, Copy, Debug)]
pub enum Algorithm {
    Sha224,
    Sha256,
    Sha384,
    Sha512,
}

impl Algorithm {
    // The length of the digest by algorithm.
    pub const fn hash_len(&self) -> usize {
        match self {
            Algorithm::Sha224 => SHA224_LENGTH,
            Algorithm::Sha256 => SHA256_LENGTH,
            Algorithm::Sha384 => SHA384_LENGTH,
            Algorithm::Sha512 => SHA512_LENGTH,
        }
    }
}

impl Algorithm {
    /// Sha2
    ///
    /// Write the Sha2 hash of `payload` into `digest`.
    pub fn hash(
        &self,
        payload: &[u8],
        digest: &mut [u8],
    ) -> Result<usize, libcrux_traits::digest::slice::HashError> {
        use libcrux_traits::digest::slice::Hash;
        match self {
            Algorithm::Sha224 => <Sha224 as Hash>::hash(digest, payload),
            Algorithm::Sha256 => <Sha256 as Hash>::hash(digest, payload),
            Algorithm::Sha384 => <Sha384 as Hash>::hash(digest, payload),
            Algorithm::Sha512 => <Sha512 as Hash>::hash(digest, payload),
        }
    }
}

/// SHA2 224
/// Will panic if `payload` is longer than `u32::MAX` to ensure that hacl-rs can
/// process it.
#[inline(always)]
pub fn sha224(payload: &[u8]) -> Result<[u8; SHA224_LENGTH], HashError> {
    let mut digest = [0u8; SHA224_LENGTH];
    Sha224::hash(&mut digest, payload).map(|_| digest)
}

/// SHA2 256
/// Will panic if `payload` is longer than `u32::MAX` to ensure that hacl-rs can
/// process it.
#[inline(always)]
pub fn sha256(payload: &[u8]) -> Result<[u8; SHA256_LENGTH], HashError> {
    let mut digest = [0u8; SHA256_LENGTH];
    Sha256::hash(&mut digest, payload).map(|_| digest)
}

/// SHA2 384
/// Will panic if `payload` is longer than `u32::MAX` to ensure that hacl-rs can
/// process it.
#[inline(always)]
pub fn sha384(payload: &[u8]) -> Result<[u8; SHA384_LENGTH], HashError> {
    let mut digest = [0u8; SHA384_LENGTH];
    Sha384::hash(&mut digest, payload).map(|_| digest)
}

pub use libcrux_traits::digest::arrayref::HashError;

/// SHA2 512
/// Will panic if `payload` is longer than `u32::MAX` to ensure that hacl-rs can
/// process it.
#[inline(always)]
pub fn sha512(payload: &[u8]) -> Result<[u8; SHA512_LENGTH], HashError> {
    let mut digest = [0u8; SHA512_LENGTH];
    Sha512::hash(&mut digest, payload).map(|_| digest)
}

// Streaming API - This is the recommended one.
// For implementations based on hacl_rs (over hacl-c)
macro_rules! impl_hash {
    ($hasher_name:ident, $state_name:ident, $name:ident, $digest_size:literal, $state:ty, $malloc:expr, $reset:expr, $update:expr, $finish:expr, $copy:expr, $hash:expr) => {
        #[derive(Clone, Default)]
        #[allow(non_camel_case_types)]
        pub struct $name;

        pub type $hasher_name = libcrux_traits::digest::Hasher<$digest_size, $name>;

        pub struct $state_name($state);

        impl Clone for $state_name {
            fn clone(&self) -> Self {
                Self($copy(self.0.as_ref()))
            }
        }

        impl Default for $state_name {
            fn default() -> Self {
                Self($malloc())
            }
        }
        impl libcrux_traits::digest::arrayref::Hash<$digest_size> for $name {
            /// Return the digest for the given input byte slice, in immediate mode.
            /// Will return an error if `payload` is longer than `u32::MAX` to ensure that hacl-rs can
            /// process it.
            #[inline(always)]
            fn hash(digest: &mut [u8; $digest_size], payload: &[u8]) -> Result<(), libcrux_traits::digest::arrayref::HashError> {
                debug_assert!(digest.len() == $digest_size);
                let payload_len: u32 = payload.len().try_into()
                    .map_err(|_| libcrux_traits::digest::arrayref::HashError::PayloadTooLong)?;

                $hash(digest, payload, payload_len);

                Ok(())
            }


        }
        impl libcrux_traits::digest::arrayref::DigestIncremental<$digest_size> for $name {
            type IncrementalState = $state_name;

            /// Add the `payload` to the digest.
            /// Will panic if `payload` is longer than `u32::MAX` to ensure that hacl-rs can
            /// process it.
            #[inline(always)]
            fn update(state: &mut Self::IncrementalState, payload: &[u8])
            -> Result<(), libcrux_traits::digest::arrayref::UpdateError> {
                let payload_len: u32 = payload.len().try_into()
                    .map_err(|_| libcrux_traits::digest::arrayref::UpdateError::PayloadTooLong)?;
                $update(state.0.as_mut(), payload, payload_len);
                Ok(())
            }

            /// Get the digest.
            ///
            /// Note that the digest state can be continued to be used, to extend the
            /// digest.
            #[inline(always)]
            fn finish(state: &mut Self::IncrementalState, digest: &mut [u8; $digest_size]) {
                $finish(state.0.as_ref(), digest);
            }

            /// Reset the digest state.
            #[inline(always)]
            fn reset(state: &mut Self::IncrementalState) {
                $reset(state.0.as_mut());
            }
        }
        libcrux_traits::digest::slice::impl_digest_trait!($name => $state_name, $digest_size);

    };
}

impl_hash!(
    Sha256Hasher,
    Sha256State,
    Sha256,
    32,
    Box<[libcrux_hacl_rs::streaming_types::state_32]>,
    crate::hacl::malloc_256,
    crate::hacl::reset_256,
    crate::hacl::update_256,
    crate::hacl::digest_256,
    crate::hacl::copy_256,
    crate::hacl::hash_256
);
impl_hash!(
    Sha224Hasher,
    Sha224State,
    Sha224,
    28,
    Box<[libcrux_hacl_rs::streaming_types::state_32]>,
    crate::hacl::malloc_224,
    crate::hacl::reset_224,
    crate::hacl::update_224,
    crate::hacl::digest_224,
    crate::hacl::copy_256,
    crate::hacl::hash_224
);

impl_hash!(
    Sha512Hasher,
    Sha512State,
    Sha512,
    64,
    Box<[libcrux_hacl_rs::streaming_types::state_64]>,
    crate::hacl::malloc_512,
    crate::hacl::reset_512,
    crate::hacl::update_512,
    crate::hacl::digest_512,
    crate::hacl::copy_512,
    crate::hacl::hash_512
);

impl_hash!(
    Sha384Hasher,
    Sha384State,
    Sha384,
    48,
    Box<[libcrux_hacl_rs::streaming_types::state_64]>,
    crate::hacl::malloc_384,
    crate::hacl::reset_384,
    crate::hacl::update_384,
    crate::hacl::digest_384,
    crate::hacl::copy_512,
    crate::hacl::hash_384
);
