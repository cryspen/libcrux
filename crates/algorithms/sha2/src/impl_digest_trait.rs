use libcrux_traits::{
    digest::{arrayref, slice, DigestIncrementalBase, InitializeDigestState, UpdateError},
    Digest,
};

use crate::impl_hacl::*;

// Streaming API - This is the recommended one.
// For implementations based on hacl_rs (over hacl-c)
macro_rules! impl_hash {
    ($hasher_name:ident, $name:ident, $state_name:ty, $digest_size:literal, $test_name:ident) => {
        #[derive(Clone, Default)]

        #[doc = concat!("A struct that implements [`libcrux_traits::digest`] traits.")]
        #[doc = concat!("\n\n")]
        #[doc = concat!("[`",stringify!($hasher_name), "`] is a convenience hasher for this struct.")]
        #[allow(non_camel_case_types)]
        pub struct $name;

        #[doc = concat!("A hasher for [`",stringify!($name), "`].")]
        pub type $hasher_name = libcrux_traits::digest::Hasher<$digest_size, $name>;


        impl arrayref::Hash<$digest_size> for $name {
            /// Return the digest for the given input byte slice, in immediate mode.
            /// Will return an error if `payload` is longer than `u32::MAX` to ensure that hacl-rs can
            /// process it.
            #[inline(always)]
            fn hash(digest: &mut [u8; $digest_size], payload: &[u8]) -> Result<(), arrayref::HashError> {

                if payload.len() > u32::MAX as usize {
                    return Err(arrayref::HashError::InvalidPayloadLength);
                }
                <$state_name>::hash(digest, payload);

                Ok(())
            }


        }

        impl InitializeDigestState for $state_name {
            fn new() -> Self {
                Self::default()
            }
        }

        impl DigestIncrementalBase for $name {
            type IncrementalState = $state_name;
            /// Add the `payload` to the digest.
            /// Will return an error if `payload` is longer than `u32::MAX` to ensure that hacl-rs can
            /// process it.
            #[inline(always)]
            fn update(state: &mut Self::IncrementalState, payload: &[u8])
            -> Result<(), UpdateError> {
                if payload.len() > u32::MAX as usize {
                    return Err(UpdateError::InvalidPayloadLength);
                }
                state.update(payload);
                Ok(())
            }
            /// Reset the digest state.
            #[inline(always)]
            fn reset(state: &mut Self::IncrementalState) {
                state.reset()
            }
        }
        impl arrayref::DigestIncremental<$digest_size> for $name {

            #[inline(always)]
            fn finish(state: Self::IncrementalState, digest: &mut [u8; $digest_size]) {
                state.finish (digest);
            }

        }
        slice::impl_hash_trait!($name => $digest_size);
        slice::impl_digest_incremental_trait!($name => $state_name, $digest_size);


        #[test]
        fn $test_name() {
            libcrux_traits::digest::tests::simple::<$digest_size, $name>();
        }
    };
}

impl_hash!(Sha224Hasher, Sha224Hash, Sha224, 28, sha224_traits_test);
impl_hash!(Sha256Hasher, Sha256Hash, Sha256, 32, sha256_traits_test);

impl_hash!(Sha384Hasher, Sha384Hash, Sha384, 48, sha384_traits_test);
impl_hash!(Sha512Hasher, Sha512Hash, Sha512, 64, sha512_traits_test);
