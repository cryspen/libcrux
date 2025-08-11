use crate::impl_hacl::*;

use libcrux_traits::Digest;

use libcrux_traits::digest::{arrayref, slice, DigestBase};

// Streaming API - This is the recommended one.
// For implementations based on hacl_rs (over hacl-c)
macro_rules! impl_hash {
    ($hasher_name:ident, $name:ident, $state_name:ty, $digest_size:literal) => {
        #[derive(Clone, Default)]

        #[doc = concat!("A struct that implements [`libcrux_traits::digest`] traits.")]
        #[doc = concat!("\n\n")]
        #[doc = concat!("[`",stringify!($hasher_name), "`] is a convenient hasher for this struct.")]
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
                debug_assert!(digest.len() == $digest_size);
                <$state_name>::hash(digest, payload);

                Ok(())
            }


        }
        impl DigestBase for $name {
            type IncrementalState = $state_name;
        }
        impl arrayref::DigestIncremental<$digest_size> for $name {

            /// Add the `payload` to the digest.
            /// Will panic if `payload` is longer than `u32::MAX` to ensure that hacl-rs can
            /// process it.
            #[inline(always)]
            fn update(state: &mut Self::IncrementalState, payload: &[u8])
            -> Result<(), arrayref::UpdateError> {
                state.update(payload);
                Ok(())
            }

            /// Get the digest.
            ///
            /// Note that the digest state can be continued to be used, to extend the
            /// digest.
            #[inline(always)]
            fn finish(state: &mut Self::IncrementalState, digest: &mut [u8; $digest_size]) {
                state.finish (digest);
            }

            /// Reset the digest state.
            #[inline(always)]
            fn reset(state: &mut Self::IncrementalState) {
                state.reset()
            }
        }
        slice::impl_hash_trait!($name => $digest_size);
        slice::impl_digest_incremental_trait!($name => $state_name, $digest_size);

    };
}

impl_hash!(Sha224Hasher, Sha224Hash, Sha224, 28);
impl_hash!(Sha256Hasher, Sha256Hash, Sha256, 32);

impl_hash!(Sha384Hasher, Sha384Hash, Sha384, 48);
impl_hash!(Sha512Hasher, Sha512Hash, Sha512, 64);
