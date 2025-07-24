use super::arrayref::SignError;
use libcrux_secrets::{DeclassifyRef, U8};

pub trait Sign<SignAux, const PRIVATE_KEY_LEN: usize, const SIGNATURE_LEN: usize> {
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
