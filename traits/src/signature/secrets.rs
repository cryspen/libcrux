//! This module contains the trait and related errors for signers that take array references as
//! arguments and return results instead of writing to a mutable reference. Secret values use the
//! types from [libcrux-secrets](libcrux_secrets).
//!
pub use super::owned::SignError;
use libcrux_secrets::{DeclassifyRef, U8};

// TODO: declassify signing key
/// A signer. This trait makes use of types suitable for checking secret independence.
///
/// The `SignAux` type is auxiliary information required for signing.
pub trait Sign<const SIGNING_KEY_LEN: usize, const SIGNATURE_LEN: usize> {
    /// Auxiliary information needed for signing.
    type SignAux<'a>;
    /// The signing key.
    type SigningKey<'a, const LEN: usize>;
    /// Sign a payload using a provided signature key. Required auxiliary information is provided using
    /// the `aux` argument.
    fn sign(
        payload: &[u8],
        signing_key: Self::SigningKey<'_, SIGNING_KEY_LEN>,
        aux: Self::SignAux<'_>,
    ) -> Result<[u8; SIGNATURE_LEN], SignError>;
}

impl<
        const SIGNING_KEY_LEN: usize,
        const SIGNATURE_LEN: usize,
        T: for<'a> super::owned::Sign<
            SIGNING_KEY_LEN,
            SIGNATURE_LEN,
            SigningKey<'a, SIGNING_KEY_LEN> = &'a [u8; SIGNING_KEY_LEN],
        >,
    > Sign<SIGNING_KEY_LEN, SIGNATURE_LEN> for T
{
    type SignAux<'a> = <Self as super::owned::Sign<SIGNING_KEY_LEN, SIGNATURE_LEN>>::SignAux<'a>;
    type SigningKey<'a, const LEN: usize> = &'a [U8; SIGNING_KEY_LEN];

    fn sign(
        payload: &[u8],
        signing_key: &[U8; SIGNING_KEY_LEN],
        aux: Self::SignAux<'_>,
    ) -> Result<[u8; SIGNATURE_LEN], SignError> {
        Self::sign(payload, signing_key.declassify_ref(), aux)
    }
}
