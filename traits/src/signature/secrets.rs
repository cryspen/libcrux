//! This module contains the trait and related errors for signers that take array references as
//! arguments and return results instead of writing to a mutable reference. Secret values use the
//! types from [libcrux-secrets](libcrux_secrets).
//!
pub use super::owned::SignError;
use libcrux_secrets::{DeclassifyRef, U8};

/// A signer. This trait makes use of types suitable for checking secret independence.
///
/// The `SignAux` type is auxiliary information required for signing.
pub trait Sign<const SIGNING_KEY_LEN: usize, const SIGNATURE_LEN: usize> {
    /// Sign a payload using a provided signature key. Required auxiliary information is provided using
    /// the `aux` argument.
    type SignAux<'a>;
    fn sign(
        payload: &[u8],
        signing_key: &[U8; SIGNING_KEY_LEN],
        aux: Self::SignAux<'_>,
    ) -> Result<[u8; SIGNATURE_LEN], SignError>;
}

impl<
        const SIGNING_KEY_LEN: usize,
        const SIGNATURE_LEN: usize,
        T: super::owned::Sign<SIGNING_KEY_LEN, SIGNATURE_LEN>,
    > Sign<SIGNING_KEY_LEN, SIGNATURE_LEN> for T
{
    type SignAux<'a> = <Self as super::owned::Sign<SIGNING_KEY_LEN, SIGNATURE_LEN>>::SignAux<'a>;

    fn sign(
        payload: &[u8],
        signing_key: &[U8; SIGNING_KEY_LEN],
        aux: Self::SignAux<'_>,
    ) -> Result<[u8; SIGNATURE_LEN], SignError> {
        Self::sign(payload, signing_key.declassify_ref(), aux)
    }
}

/*
/// A signer that does not require auxiliary information. This trait makes use of types suitable for checking secret independence.
pub trait SignNoAux<const SIGNING_KEY_LEN: usize, const SIGNATURE_LEN: usize> {
    /// Sign a payload using a provided signature key.
    fn sign(
        payload: &[u8],
        signing_key: &[U8; SIGNING_KEY_LEN],
    ) -> Result<[u8; SIGNATURE_LEN], SignError>;
}

impl<
        const SIGNING_KEY_LEN: usize,
        const SIGNATURE_LEN: usize,
        T: Sign<(), SIGNING_KEY_LEN, SIGNATURE_LEN>,
    > SignNoAux<SIGNING_KEY_LEN, SIGNATURE_LEN> for T
{
    fn sign(
        payload: &[u8],
        signing_key: &[U8; SIGNING_KEY_LEN],
    ) -> Result<[u8; SIGNATURE_LEN], SignError> {
        <Self as Sign<(), SIGNING_KEY_LEN, SIGNATURE_LEN>>::sign(payload, signing_key, ())
    }
}
*/
