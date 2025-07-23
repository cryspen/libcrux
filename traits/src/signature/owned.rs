pub use super::arrayref::{SignError, VerifyError};

pub trait Signature<
    const PUBLIC_KEY_LEN: usize,
    const PRIVATE_KEY_LEN: usize,
    const SIGNATURE_LEN: usize,
>
{
    fn sign(
        payload: &[u8],
        private_key: &[u8; PRIVATE_KEY_LEN],
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
    fn sign(
        payload: &[u8],
        private_key: &[u8; PRIVATE_KEY_LEN],
    ) -> Result<[u8; SIGNATURE_LEN], SignError> {
        let mut signature = [0; SIGNATURE_LEN];
        Self::sign(payload, private_key, &mut signature).map(|_| signature)
    }
    fn verify(
        payload: &[u8],
        public_key: &[u8; PUBLIC_KEY_LEN],
        signature: &[u8; SIGNATURE_LEN],
    ) -> Result<(), VerifyError> {
        Self::verify(payload, public_key, signature)
    }
}
