use super::arrayref::{SignError, VerifyError};
use libcrux_secrets::{DeclassifyRef, U8};

pub trait Signature<
    const PUBLIC_KEY_LEN: usize,
    const PRIVATE_KEY_LEN: usize,
    const SIGNATURE_LEN: usize,
>
{
    type Config;
    fn sign(
        payload: &[u8],
        private_key: &[U8; PRIVATE_KEY_LEN],
        config: Self::Config,
    ) -> Result<[u8; SIGNATURE_LEN], SignError>;
    fn verify(
        payload: &[u8],
        public_key: &[u8; PUBLIC_KEY_LEN],
        signature: &[u8; SIGNATURE_LEN],
    ) -> Result<(), VerifyError>;
}

impl<
        const PUBLIC_KEY_LEN: usize,
        const PRIVATE_KEY_LEN: usize,
        const SIGNATURE_LEN: usize,
        T: super::owned::Signature<PUBLIC_KEY_LEN, PRIVATE_KEY_LEN, SIGNATURE_LEN>,
    > Signature<PUBLIC_KEY_LEN, PRIVATE_KEY_LEN, SIGNATURE_LEN> for T
{
    type Config =
        <T as super::owned::Signature<PUBLIC_KEY_LEN, PRIVATE_KEY_LEN, SIGNATURE_LEN>>::Config;
    fn sign(
        payload: &[u8],
        private_key: &[U8; PRIVATE_KEY_LEN],
        config: Self::Config,
    ) -> Result<[u8; SIGNATURE_LEN], SignError> {
        Self::sign(payload, private_key.declassify_ref(), config)
    }
    fn verify(
        payload: &[u8],
        public_key: &[u8; PUBLIC_KEY_LEN],
        signature: &[u8; SIGNATURE_LEN],
    ) -> Result<(), VerifyError> {
        Self::verify(payload, public_key, signature)
    }
}
