//! This module contains the trait and related errors for signers that take array references as arguments and return values as arrays.

pub use super::arrayref::Verify;
pub use super::arrayref::{SignError, VerifyError};
use libcrux_secrets::U8;

/// A signer that returns values instead of writing results to `&mut` arguments.
///
/// The `SignAux` type is auxiliary information required for signing.
pub trait Sign<const SIGNING_KEY_LEN: usize, const SIGNATURE_LEN: usize> {
    /// Auxiliary information needed for signing.
    type SignAux<'a>;
    /// The signing key.
    /// Sign a payload using a provided signature key. Required auxiliary information is provided using
    /// the `aux` argument.
    fn sign(
        payload: &[u8],
        signing_key: &[U8; SIGNING_KEY_LEN],
        aux: Self::SignAux<'_>,
    ) -> Result<[u8; SIGNATURE_LEN], SignError>;
}

impl<
        const SIGNING_KEY_LEN: usize,
        const SIGNATURE_LEN: usize,
        T: super::arrayref::Sign<SIGNING_KEY_LEN, SIGNATURE_LEN>,
    > Sign<SIGNING_KEY_LEN, SIGNATURE_LEN> for T
{
    type SignAux<'a> = <Self as super::arrayref::Sign<SIGNING_KEY_LEN, SIGNATURE_LEN>>::SignAux<'a>;
    fn sign(
        payload: &[u8],
        signing_key: &[U8; SIGNING_KEY_LEN],
        aux: Self::SignAux<'_>,
    ) -> Result<[u8; SIGNATURE_LEN], SignError> {
        let mut signature = [0; SIGNATURE_LEN];
        <Self as super::arrayref::Sign<SIGNING_KEY_LEN, SIGNATURE_LEN>>::sign(
            payload,
            signing_key,
            &mut signature,
            aux,
        )
        .map(|_| signature)
    }
}
