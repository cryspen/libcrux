pub mod signers {
    //! [`libcrux_traits::signature`] APIs.

    use libcrux_traits::signature::arrayref::{Sign, SignError, Verify, VerifyError};

    /// A convenience struct for signature scheme functionality.
    pub struct Signer;

    const VERIFICATION_KEY_LEN: usize = 32;
    const SIGNING_KEY_LEN: usize = 32;
    const SIGNATURE_LEN: usize = 64;

    impl Sign<SIGNING_KEY_LEN, SIGNATURE_LEN> for Signer {
        type SignAux<'a> = ();
        type SigningKey<'a, const LEN: usize> = &'a [u8; SIGNING_KEY_LEN];
        fn sign(
            payload: &[u8],
            signing_key: &[u8; SIGNING_KEY_LEN],
            signature: &mut [u8; SIGNATURE_LEN],
            _aux: (),
        ) -> Result<(), SignError> {
            crate::hacl::ed25519::sign(
                signature,
                signing_key,
                payload
                    .len()
                    .try_into()
                    .map_err(|_| SignError::InvalidPayloadLength)?,
                payload,
            );

            Ok(())
        }
    }
    impl Verify<VERIFICATION_KEY_LEN, SIGNATURE_LEN> for Signer {
        type VerifyAux<'a> = ();

        fn verify(
            payload: &[u8],
            verification_key: &[u8; VERIFICATION_KEY_LEN],
            signature: &[u8; SIGNATURE_LEN],
            _aux: (),
        ) -> Result<(), VerifyError> {
            if crate::hacl::ed25519::verify(
                verification_key,
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

    libcrux_traits::signature::slice::impl_signature_slice_trait!(Signer => SIGNING_KEY_LEN, SIGNATURE_LEN, (), _aux, &'a [u8; SIGNING_KEY_LEN]);
    libcrux_traits::signature::slice::impl_verify_slice_trait!(Signer => VERIFICATION_KEY_LEN, SIGNATURE_LEN, (), _aux);
}
