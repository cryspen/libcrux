use libcrux_traits::ecdh::key_centric_owned::Pair;
pub use libcrux_traits::ecdh::{arrayref::EcdhArrayref, owned::EcdhOwned, slice::EcdhSlice};

use crate::clamp;

use super::{DK_LEN, EK_LEN, X25519};

/// Number of bytes of randomness required to generate an ECDH secret.
pub const RAND_LEN: usize = DK_LEN;
/// Length in bytes of an ECDH secret value.
pub const SECRET_LEN: usize = DK_LEN;
/// Length in bytes of an ECDH public value.
pub const PUBLIC_LEN: usize = EK_LEN;

use libcrux_secrets::{Classify, Declassify, DeclassifyRef, DeclassifyRefMut, U8};

/// A corresponding pair of ECDH public and secret values over Curve25519.
pub type X25519Pair = Pair<X25519>;

impl libcrux_traits::ecdh::arrayref::EcdhArrayref<RAND_LEN, SECRET_LEN, PUBLIC_LEN> for X25519 {
    fn generate_secret(
        secret: &mut [U8; SECRET_LEN],
        rand: &[U8; RAND_LEN],
    ) -> Result<(), libcrux_traits::ecdh::arrayref::GenerateSecretError> {
        secret.copy_from_slice(rand);
        clamp(secret.declassify_ref_mut());

        Ok(())
    }

    fn secret_to_public(
        public: &mut [u8; PUBLIC_LEN],
        secret: &[U8; SECRET_LEN],
    ) -> Result<(), libcrux_traits::ecdh::arrayref::SecretToPublicError> {
        crate::hacl::secret_to_public(public, secret.declassify_ref());
        Ok(())
    }

    fn derive_ecdh(
        derived: &mut [U8; PUBLIC_LEN],
        public: &[u8; PUBLIC_LEN],
        secret: &[U8; SECRET_LEN],
    ) -> Result<(), libcrux_traits::ecdh::arrayref::DeriveError> {
        crate::hacl::ecdh(
            derived.declassify_ref_mut().as_mut_slice(),
            secret.declassify_ref().as_slice(),
            public.as_ref(),
        )
        .then_some(())
        .ok_or(libcrux_traits::ecdh::arrayref::DeriveError::Unknown)
    }

    fn validate_secret(
        secret: &[U8; SECRET_LEN],
    ) -> Result<(), libcrux_traits::ecdh::arrayref::ValidateSecretError> {
        let mut all_zero = 0u8.classify();
        for i in 0..SECRET_LEN {
            all_zero |= secret[i];
        }

        (all_zero.declassify() != 0)
            .then_some(())
            .ok_or(libcrux_traits::ecdh::arrayref::ValidateSecretError::InvalidSecret)
    }
}

libcrux_traits::ecdh::slice::impl_ecdh_slice_trait!(X25519 => RAND_LEN, SECRET_LEN, PUBLIC_LEN);
libcrux_traits::ecdh::key_centric_owned::impl_ecdh_key_centric_owned!(X25519 => RAND_LEN, SECRET_LEN, PUBLIC_LEN, PUBLIC_LEN);
