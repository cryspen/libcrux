pub trait SignWithAux<SignAux, const PRIVATE_KEY_LEN: usize, const SIGNATURE_LEN: usize> {
    // TODO: should this be called `private_key` or `sk`?
    fn sign(
        payload: &[u8],
        private_key: &[u8; PRIVATE_KEY_LEN],
        signature: &mut [u8; SIGNATURE_LEN],
        sign_aux: SignAux,
    ) -> Result<(), SignError>;
}

pub trait VerifyWithAux<VerifyAux, const PUBLIC_KEY_LEN: usize, const SIGNATURE_LEN: usize> {
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

// No auxiliary information
pub trait Sign<const PRIVATE_KEY_LEN: usize, const SIGNATURE_LEN: usize> {
    fn sign(
        payload: &[u8],
        private_key: &[u8; PRIVATE_KEY_LEN],
        signature: &mut [u8; SIGNATURE_LEN],
    ) -> Result<(), SignError>;
}

impl<
        'a,
        const PRIVATE_KEY_LEN: usize,
        const SIGNATURE_LEN: usize,
        T: SignWithAux<&'a (), PRIVATE_KEY_LEN, SIGNATURE_LEN>,
    > Sign<PRIVATE_KEY_LEN, SIGNATURE_LEN> for T
{
    fn sign(
        payload: &[u8],
        private_key: &[u8; PRIVATE_KEY_LEN],
        signature: &mut [u8; SIGNATURE_LEN],
    ) -> Result<(), SignError> {
        <Self as SignWithAux<&'a (), PRIVATE_KEY_LEN, SIGNATURE_LEN>>::sign(
            payload,
            private_key,
            signature,
            &(),
        )
    }
}

// No auxiliary information
pub trait Verify<const PUBLIC_KEY_LEN: usize, const SIGNATURE_LEN: usize> {
    fn verify(
        payload: &[u8],
        public_key: &[u8; PUBLIC_KEY_LEN],
        signature: &[u8; SIGNATURE_LEN],
    ) -> Result<(), VerifyError>;
}

impl<
        'a,
        const PUBLIC_KEY_LEN: usize,
        const SIGNATURE_LEN: usize,
        T: VerifyWithAux<&'a (), PUBLIC_KEY_LEN, SIGNATURE_LEN>,
    > Verify<PUBLIC_KEY_LEN, SIGNATURE_LEN> for T
{
    fn verify(
        payload: &[u8],
        public_key: &[u8; PUBLIC_KEY_LEN],
        signature: &[u8; SIGNATURE_LEN],
    ) -> Result<(), VerifyError> {
        <Self as VerifyWithAux<&'a (), PUBLIC_KEY_LEN, SIGNATURE_LEN>>::verify(
            payload,
            public_key,
            signature,
            &(),
        )
    }
}
