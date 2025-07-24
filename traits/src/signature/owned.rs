pub use super::arrayref::{SignError, VerifyError};

pub trait Sign<SignAux, const PRIVATE_KEY_LEN: usize, const SIGNATURE_LEN: usize> {
    fn sign(
        payload: &[u8],
        private_key: &[u8; PRIVATE_KEY_LEN],
        aux: SignAux,
    ) -> Result<[u8; SIGNATURE_LEN], SignError>;
}

impl<
        SignAux,
        const PRIVATE_KEY_LEN: usize,
        const SIGNATURE_LEN: usize,
        T: super::arrayref::Sign<SignAux, PRIVATE_KEY_LEN, SIGNATURE_LEN>,
    > Sign<SignAux, PRIVATE_KEY_LEN, SIGNATURE_LEN> for T
{
    fn sign(
        payload: &[u8],
        private_key: &[u8; PRIVATE_KEY_LEN],
        aux: SignAux,
    ) -> Result<[u8; SIGNATURE_LEN], SignError> {
        let mut signature = [0; SIGNATURE_LEN];
        <Self as super::arrayref::Sign<SignAux, PRIVATE_KEY_LEN, SIGNATURE_LEN>>::sign(
            payload,
            private_key,
            &mut signature,
            aux,
        )
        .map(|_| signature)
    }
}

// No auxiliary information
pub trait SignNoAux<const PRIVATE_KEY_LEN: usize, const SIGNATURE_LEN: usize> {
    fn sign(
        payload: &[u8],
        private_key: &[u8; PRIVATE_KEY_LEN],
    ) -> Result<[u8; SIGNATURE_LEN], SignError>;
}

impl<
        'a,
        const PRIVATE_KEY_LEN: usize,
        const SIGNATURE_LEN: usize,
        T: Sign<&'a (), PRIVATE_KEY_LEN, SIGNATURE_LEN>,
    > SignNoAux<PRIVATE_KEY_LEN, SIGNATURE_LEN> for T
{
    fn sign(
        payload: &[u8],
        private_key: &[u8; PRIVATE_KEY_LEN],
    ) -> Result<[u8; SIGNATURE_LEN], SignError> {
        <Self as Sign<&'a (), PRIVATE_KEY_LEN, SIGNATURE_LEN>>::sign(payload, private_key, &())
    }
}
