//! This module contains the trait and related errors for signers that take array references as
//! arguments and return results instead of writing to a mutable reference. Secret values use the
//! types from [libcrux-secrets](libcrux_secrets).
//!
pub use super::owned::SignError;
use libcrux_secrets::{DeclassifyRef, U8};

/// A signer. This trait makes use of types suitable for checking secret independence.
pub trait Sign<SignAux, const PRIVATE_KEY_LEN: usize, const SIGNATURE_LEN: usize> {
    /// Sign a payload using a provided signature key. Required auxiliary information is provided using
    /// the `aux` argument.
    fn sign(
        payload: &[u8],
        private_key: &[U8; PRIVATE_KEY_LEN],
        sign_aux: SignAux,
    ) -> Result<[u8; SIGNATURE_LEN], SignError>;
}

impl<
        SignAux,
        const PRIVATE_KEY_LEN: usize,
        const SIGNATURE_LEN: usize,
        T: super::owned::Sign<SignAux, PRIVATE_KEY_LEN, SIGNATURE_LEN>,
    > Sign<SignAux, PRIVATE_KEY_LEN, SIGNATURE_LEN> for T
{
    fn sign(
        payload: &[u8],
        private_key: &[U8; PRIVATE_KEY_LEN],
        sign_aux: SignAux,
    ) -> Result<[u8; SIGNATURE_LEN], SignError> {
        Self::sign(payload, private_key.declassify_ref(), sign_aux)
    }
}

/// A signer that does not require auxiliary information. This trait makes use of types suitable for checking secret independence.
pub trait SignNoAux<const PRIVATE_KEY_LEN: usize, const SIGNATURE_LEN: usize> {
    /// Sign a payload using a provided signature key.
    fn sign(
        payload: &[u8],
        private_key: &[U8; PRIVATE_KEY_LEN],
    ) -> Result<[u8; SIGNATURE_LEN], SignError>;
}

impl<
        const PRIVATE_KEY_LEN: usize,
        const SIGNATURE_LEN: usize,
        T: Sign<(), PRIVATE_KEY_LEN, SIGNATURE_LEN>,
    > SignNoAux<PRIVATE_KEY_LEN, SIGNATURE_LEN> for T
{
    fn sign(
        payload: &[u8],
        private_key: &[U8; PRIVATE_KEY_LEN],
    ) -> Result<[u8; SIGNATURE_LEN], SignError> {
        <Self as Sign<(), PRIVATE_KEY_LEN, SIGNATURE_LEN>>::sign(payload, private_key, ())
    }
}
