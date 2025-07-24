pub use super::arrayref::{SignError, VerifyError};

pub trait SignatureAux<
    SignAux,
    VerifyAux,
    const PUBLIC_KEY_LEN: usize,
    const PRIVATE_KEY_LEN: usize,
    const SIGNATURE_LEN: usize,
>
{
    fn sign(
        payload: &[u8],
        private_key: &[u8; PRIVATE_KEY_LEN],
        aux: SignAux,
    ) -> Result<[u8; SIGNATURE_LEN], SignError>;
    fn verify(
        payload: &[u8],
        public_key: &[u8; PUBLIC_KEY_LEN],
        signature: &[u8; SIGNATURE_LEN],
        aux: VerifyAux,
    ) -> Result<(), VerifyError>;
}

impl<
        SignAux,
        VerifyAux,
        const PUBLIC_KEY_LEN: usize,
        const PRIVATE_KEY_LEN: usize,
        const SIGNATURE_LEN: usize,
        T: super::arrayref::SignatureAux<
            SignAux,
            VerifyAux,
            PUBLIC_KEY_LEN,
            PRIVATE_KEY_LEN,
            SIGNATURE_LEN,
        >,
    > SignatureAux<SignAux, VerifyAux, PUBLIC_KEY_LEN, PRIVATE_KEY_LEN, SIGNATURE_LEN> for T
{
    fn sign(
        payload: &[u8],
        private_key: &[u8; PRIVATE_KEY_LEN],
        aux: SignAux,
    ) -> Result<[u8; SIGNATURE_LEN], SignError> {
        let mut signature = [0; SIGNATURE_LEN];
        <Self as super::arrayref::SignatureAux<
            SignAux,
            VerifyAux,
            PUBLIC_KEY_LEN,
            PRIVATE_KEY_LEN,
            SIGNATURE_LEN,
        >>::sign(payload, private_key, &mut signature, aux)
        .map(|_| signature)
    }
    fn verify(
        payload: &[u8],
        public_key: &[u8; PUBLIC_KEY_LEN],
        signature: &[u8; SIGNATURE_LEN],
        aux: VerifyAux,
    ) -> Result<(), VerifyError> {
        Self::verify(payload, public_key, signature, aux)
    }
}

// No auxiliary information
pub trait Sign<
    const PUBLIC_KEY_LEN: usize,
    const PRIVATE_KEY_LEN: usize,
    const SIGNATURE_LEN: usize,
>
{
    fn sign(
        payload: &[u8],
        private_key: &[u8; PRIVATE_KEY_LEN],
    ) -> Result<[u8; SIGNATURE_LEN], SignError>;
}

impl<
        'a,
        const PUBLIC_KEY_LEN: usize,
        const PRIVATE_KEY_LEN: usize,
        const SIGNATURE_LEN: usize,
        T: SignatureAux<&'a (), &'a (), PUBLIC_KEY_LEN, PRIVATE_KEY_LEN, SIGNATURE_LEN>,
    > Sign<PUBLIC_KEY_LEN, PRIVATE_KEY_LEN, SIGNATURE_LEN> for T
{
    fn sign(
        payload: &[u8],
        private_key: &[u8; PRIVATE_KEY_LEN],
    ) -> Result<[u8; SIGNATURE_LEN], SignError> {
        <Self as SignatureAux<&'a (), &'a (), PUBLIC_KEY_LEN, PRIVATE_KEY_LEN, SIGNATURE_LEN>>::sign(
            payload,
            private_key,
            &(),
        )
    }
}

// No auxiliary information
pub trait Verify<
    const PUBLIC_KEY_LEN: usize,
    const PRIVATE_KEY_LEN: usize,
    const SIGNATURE_LEN: usize,
>
{
    fn verify(
        payload: &[u8],
        public_key: &[u8; PUBLIC_KEY_LEN],
        signature: &[u8; SIGNATURE_LEN],
    ) -> Result<(), VerifyError>;
}

impl<
        'a,
        const PUBLIC_KEY_LEN: usize,
        const PRIVATE_KEY_LEN: usize,
        const SIGNATURE_LEN: usize,
        T: SignatureAux<&'a (), &'a (), PUBLIC_KEY_LEN, PRIVATE_KEY_LEN, SIGNATURE_LEN>,
    > Verify<PUBLIC_KEY_LEN, PRIVATE_KEY_LEN, SIGNATURE_LEN> for T
{
    fn verify(
        payload: &[u8],
        public_key: &[u8; PUBLIC_KEY_LEN],
        signature: &[u8; SIGNATURE_LEN],
    ) -> Result<(), VerifyError> {
        <Self as SignatureAux<&'a (), &'a (), PUBLIC_KEY_LEN, PRIVATE_KEY_LEN, SIGNATURE_LEN>>::verify(
    payload, public_key, signature, &())
    }
}
