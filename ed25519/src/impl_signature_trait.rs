pub mod signers {
    //! [`libcrux_traits::signature`] APIs.

    use libcrux_secrets::{DeclassifyRef, U8};
    use libcrux_traits::signature::arrayref::{KeyGenError, Sign, SignError, VerifyError};

    /// A convenience struct for signature scheme functionality.
    pub struct Signer;

    const VERIFICATION_KEY_LEN: usize = 32;
    const SIGNING_KEY_LEN: usize = 32;
    const SIGNATURE_LEN: usize = 64;
    const RAND_KEYGEN_LEN: usize = SIGNING_KEY_LEN;

    impl Sign<SIGNING_KEY_LEN, VERIFICATION_KEY_LEN, SIGNATURE_LEN, RAND_KEYGEN_LEN> for Signer {
        /// Sign a payload with a provided signing key.
        fn sign(
            payload: &[u8],
            signing_key: &[U8; SIGNING_KEY_LEN],
            signature: &mut [u8; SIGNATURE_LEN],
            _aux: (),
        ) -> Result<(), SignError> {
            crate::hacl::ed25519::sign(
                signature,
                signing_key.declassify_ref(),
                payload
                    .len()
                    .try_into()
                    .map_err(|_| SignError::InvalidArgument)?,
                payload,
            );

            Ok(())
        }

        /// Verify a signature using a provided verification key.
        fn verify(
            payload: &[u8],
            verification_key: &[u8; VERIFICATION_KEY_LEN],
            signature: &[u8; SIGNATURE_LEN],
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

        fn keygen_derand(
            signing_key: &mut [U8; SIGNING_KEY_LEN],
            verification_key: &mut [u8; VERIFICATION_KEY_LEN],
            randomness: &[U8; SIGNING_KEY_LEN],
        ) -> Result<(), KeyGenError> {
            *signing_key = *randomness;
            crate::secret_to_public(verification_key, signing_key.declassify_ref());

            Ok(())
        }
    }

    libcrux_traits::signature::slice::impl_signature_slice_trait!(
        Signer => SIGNING_KEY_LEN,
        VERIFICATION_KEY_LEN, SIGNATURE_LEN, RAND_KEYGEN_LEN, (), _aux);

    // key centric APIs
    libcrux_traits::signature::key_centric_owned::impl_sign_types!(
        Signer,
        SIGNING_KEY_LEN,
        VERIFICATION_KEY_LEN,
        SIGNATURE_LEN,
        RAND_KEYGEN_LEN,
        ()
    );
}
