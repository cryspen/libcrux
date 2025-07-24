use super::arrayref::{SignError, VerifyError};
use libcrux_secrets::{DeclassifyRef, U8};

pub trait Signature<
    SignAux,
    VerifyAux,
    const PUBLIC_KEY_LEN: usize,
    const PRIVATE_KEY_LEN: usize,
    const SIGNATURE_LEN: usize,
>
{
    fn sign(
        payload: &[u8],
        private_key: &[U8; PRIVATE_KEY_LEN],
        sign_aux: SignAux,
    ) -> Result<[u8; SIGNATURE_LEN], SignError>;
    fn verify(
        payload: &[u8],
        public_key: &[u8; PUBLIC_KEY_LEN],
        signature: &[u8; SIGNATURE_LEN],
        verify_aux: VerifyAux,
    ) -> Result<(), VerifyError>;
}

impl<
        SignAux,
        VerifyAux,
        const PUBLIC_KEY_LEN: usize,
        const PRIVATE_KEY_LEN: usize,
        const SIGNATURE_LEN: usize,
        T: super::owned::Signature<SignAux, VerifyAux, PUBLIC_KEY_LEN, PRIVATE_KEY_LEN, SIGNATURE_LEN>,
    > Signature<SignAux, VerifyAux, PUBLIC_KEY_LEN, PRIVATE_KEY_LEN, SIGNATURE_LEN> for T
{
    fn sign(
        payload: &[u8],
        private_key: &[U8; PRIVATE_KEY_LEN],
        sign_aux: SignAux,
    ) -> Result<[u8; SIGNATURE_LEN], SignError> {
        Self::sign(payload, private_key.declassify_ref(), sign_aux)
    }
    fn verify(
        payload: &[u8],
        public_key: &[u8; PUBLIC_KEY_LEN],
        signature: &[u8; SIGNATURE_LEN],
        verify_aux: VerifyAux,
    ) -> Result<(), VerifyError> {
        Self::verify(payload, public_key, signature, verify_aux)
    }
}
