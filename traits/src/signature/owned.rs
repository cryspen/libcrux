pub use super::arrayref::{SignError, VerifyError};

pub trait SignWithAux<SignAux, const PRIVATE_KEY_LEN: usize, const SIGNATURE_LEN: usize> {
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
        T: super::arrayref::SignWithAux<SignAux, PRIVATE_KEY_LEN, SIGNATURE_LEN>,
    > SignWithAux<SignAux, PRIVATE_KEY_LEN, SIGNATURE_LEN> for T
{
    fn sign(
        payload: &[u8],
        private_key: &[u8; PRIVATE_KEY_LEN],
        aux: SignAux,
    ) -> Result<[u8; SIGNATURE_LEN], SignError> {
        let mut signature = [0; SIGNATURE_LEN];
        <Self as super::arrayref::SignWithAux<SignAux, PRIVATE_KEY_LEN, SIGNATURE_LEN>>::sign(
            payload,
            private_key,
            &mut signature,
            aux,
        )
        .map(|_| signature)
    }
}

// No auxiliary information
pub trait Sign<const PRIVATE_KEY_LEN: usize, const SIGNATURE_LEN: usize> {
    fn sign(
        payload: &[u8],
        private_key: &[u8; PRIVATE_KEY_LEN],
    ) -> Result<[u8; SIGNATURE_LEN], SignError>;
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
    ) -> Result<[u8; SIGNATURE_LEN], SignError> {
        <Self as SignWithAux<&'a (), PRIVATE_KEY_LEN, SIGNATURE_LEN>>::sign(
            payload,
            private_key,
            &(),
        )
    }
}
