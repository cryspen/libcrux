pub trait Signature<
    SignAux,
    VerifyAux,
    const PUBLIC_KEY_LEN: usize,
    const PRIVATE_KEY_LEN: usize,
    const SIGNATURE_LEN: usize,
>
{
    // TODO: should this be called `private_key` or `sk`?
    fn sign(
        payload: &[u8],
        private_key: &[u8; PRIVATE_KEY_LEN],
        signature: &mut [u8; SIGNATURE_LEN],
        sign_aux: SignAux,
    ) -> Result<(), SignError>;
    fn verify(
        payload: &[u8],
        public_key: &[u8; PUBLIC_KEY_LEN],
        signature: &[u8; SIGNATURE_LEN],
        verify_aux: VerifyAux,
    ) -> Result<(), VerifyError>;
}

#[derive(Debug, PartialEq, Eq)]
pub enum SignError {
    InvalidPayloadLength,
}

#[derive(Debug, PartialEq, Eq)]
pub enum VerifyError {
    InvalidSignature,
    InvalidPayloadLength,
}
