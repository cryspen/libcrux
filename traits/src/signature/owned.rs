//! This module contains the trait and related errors for signers that take array references as arguments and return values as arrays.

pub use super::arrayref::SignError;

/// A signer that returns values instead of writing results to `&mut` arguments.
pub trait Sign<SignAux, const SIGNING_KEY_LEN: usize, const SIGNATURE_LEN: usize> {
    /// Sign a payload using a provided signature key. Required auxiliary information is provided using
    /// the `aux` argument.
    fn sign(
        payload: &[u8],
        signing_key: &[u8; SIGNING_KEY_LEN],
        aux: SignAux,
    ) -> Result<[u8; SIGNATURE_LEN], SignError>;
}

impl<
        SignAux,
        const SIGNING_KEY_LEN: usize,
        const SIGNATURE_LEN: usize,
        T: super::arrayref::Sign<SignAux, SIGNING_KEY_LEN, SIGNATURE_LEN>,
    > Sign<SignAux, SIGNING_KEY_LEN, SIGNATURE_LEN> for T
{
    fn sign(
        payload: &[u8],
        signing_key: &[u8; SIGNING_KEY_LEN],
        aux: SignAux,
    ) -> Result<[u8; SIGNATURE_LEN], SignError> {
        let mut signature = [0; SIGNATURE_LEN];
        <Self as super::arrayref::Sign<SignAux, SIGNING_KEY_LEN, SIGNATURE_LEN>>::sign(
            payload,
            signing_key,
            &mut signature,
            aux,
        )
        .map(|_| signature)
    }
}

// No auxiliary information
/// A signer that does not require auxiliary information. This trait returns values instead of writing results to `&mut` arguments.
pub trait SignNoAux<const SIGNING_KEY_LEN: usize, const SIGNATURE_LEN: usize> {
    /// Sign a payload using a provided signature key.
    fn sign(
        payload: &[u8],
        signing_key: &[u8; SIGNING_KEY_LEN],
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
        signing_key: &[u8; SIGNING_KEY_LEN],
    ) -> Result<[u8; SIGNATURE_LEN], SignError> {
        <Self as Sign<(), SIGNING_KEY_LEN, SIGNATURE_LEN>>::sign(payload, signing_key, ())
    }
}
