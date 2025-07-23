pub use super::arrayref::{SignError, VerifyError};

pub trait Signature<
    const PUBLIC_KEY_LEN: usize,
    const PRIVATE_KEY_LEN: usize,
    const SIGNATURE_LEN: usize,
>
{
    type Config;
    fn sign(
        payload: &[u8],
        private_key: &[u8; PRIVATE_KEY_LEN],
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
        T: super::arrayref::Signature<PUBLIC_KEY_LEN, PRIVATE_KEY_LEN, SIGNATURE_LEN>,
    > Signature<PUBLIC_KEY_LEN, PRIVATE_KEY_LEN, SIGNATURE_LEN> for T
{
    type Config =
        <T as super::arrayref::Signature<PUBLIC_KEY_LEN, PRIVATE_KEY_LEN, SIGNATURE_LEN>>::Config;
    fn sign(
        payload: &[u8],
        private_key: &[u8; PRIVATE_KEY_LEN],
        config: Self::Config,
    ) -> Result<[u8; SIGNATURE_LEN], SignError> {
        let mut signature = [0; SIGNATURE_LEN];
        Self::sign(payload, private_key, &mut signature, config).map(|_| signature)
    }
    fn verify(
        payload: &[u8],
        public_key: &[u8; PUBLIC_KEY_LEN],
        signature: &[u8; SIGNATURE_LEN],
    ) -> Result<(), VerifyError> {
        Self::verify(payload, public_key, signature)
    }
}
