use libcrux_traits::signature::arrayref::{SignError, Signature, VerifyError};

pub struct Signer;

const PUBLIC_KEY_LEN: usize = 32;
const PRIVATE_KEY_LEN: usize = 32;
const SIGNATURE_LEN: usize = 64;

impl Signature<&(), &(), PUBLIC_KEY_LEN, PRIVATE_KEY_LEN, SIGNATURE_LEN> for Signer {
    fn sign(
        payload: &[u8],
        private_key: &[u8; PRIVATE_KEY_LEN],
        signature: &mut [u8; SIGNATURE_LEN],
        _aux: &(),
    ) -> Result<(), SignError> {
        crate::hacl::ed25519::sign(
            signature,
            private_key,
            payload
                .len()
                .try_into()
                .map_err(|_| SignError::InvalidPayloadLength)?,
            payload,
        );

        Ok(())
    }
    fn verify(
        payload: &[u8],
        public_key: &[u8; PUBLIC_KEY_LEN],
        signature: &[u8; SIGNATURE_LEN],
        _aux: &(),
    ) -> Result<(), VerifyError> {
        if crate::hacl::ed25519::verify(
            public_key,
            payload
                .len()
                .try_into()
                .map_err(|_| VerifyError::InvalidPayloadLength)?,
            payload,
            signature,
        ) {
            Ok(())
        } else {
            Err(VerifyError::InvalidSignature)
        }
    }
}

libcrux_traits::signature::slice::impl_signature_slice_trait!(Signer => PUBLIC_KEY_LEN, PRIVATE_KEY_LEN, SIGNATURE_LEN, &(), _aux, &(), _aux);
