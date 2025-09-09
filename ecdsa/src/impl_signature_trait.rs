pub mod signers {
    //! [`libcrux_traits::signature`] APIs.

    use libcrux_traits::signature::arrayref;

    const SIGNING_KEY_LEN: usize = 32;
    const VERIFICATION_KEY_LEN: usize = 64;
    const SIG_LEN: usize = 64;
    const RAND_KEYGEN_LEN: usize = 32;

    macro_rules! impl_signature_trait {
        (
            $digest_alg_name:ident,
            $name:ident,
            $sign_fn:ident,
            $verify_fn:ident
        ) => {
            #[allow(non_camel_case_types)]
            #[doc = concat!("A signer using [`libcrux_sha2::", stringify!($digest_alg_name),"`].")]
            pub struct $name;

            /// The [`arrayref`](libcrux_traits::signature::arrayref) version of the Sign trait.
            impl arrayref::Sign<SIGNING_KEY_LEN, VERIFICATION_KEY_LEN, SIG_LEN, RAND_KEYGEN_LEN> for $name {
                /// The nonce needed for signing.
                type SignAux<'a> = &'a Nonce;
                /// Sign a payload using a provided signing key and `nonce`.
                #[inline(always)]
                fn sign(
                    payload: &[u8],
                    signing_key: &[u8; SIGNING_KEY_LEN],
                    signature: &mut [u8; SIG_LEN],
                    nonce: &Nonce,
                ) -> Result<(), arrayref::SignError> {
                    let result = libcrux_p256::$sign_fn(
                        signature,
                        payload.len().try_into().map_err(|_| arrayref::SignError::InvalidPayloadLength)?,
                        payload,
                        signing_key,
                        &nonce.0,
                    );
                    if !result {
                        return Err(arrayref::SignError::LibraryError);
                    }
                    Ok(())
                }
                /// No auxiliary information is required for verification.
                type VerifyAux<'a> = ();
                #[inline(always)]
                /// Verify a signature using a provided verification key.
                fn verify(
                    payload: &[u8],
                    verification_key: &[u8; VERIFICATION_KEY_LEN],
                    signature: &[u8; SIG_LEN],
                    _aux: (),
                ) -> Result<(), arrayref::VerifyError> {
                    let result = libcrux_p256::$verify_fn(
                        payload.len().try_into().map_err(|_| arrayref::VerifyError::InvalidPayloadLength)?,
                        payload,
                        verification_key,
                        <&[u8; 32]>::try_from(&signature[0..32]).unwrap(),
                        <&[u8; 32]>::try_from(&signature[32..]).unwrap(),
                    );
                    if !result {
                        return Err(arrayref::VerifyError::LibraryError);
                    }
                    Ok(())
                }
                fn keygen(signing_key: &mut [u8; SIGNING_KEY_LEN], verification_key: &mut [u8; VERIFICATION_KEY_LEN], randomness: [u8; RAND_KEYGEN_LEN]) -> Result<(), arrayref::KeyGenError> {
                    use libcrux_traits::kem::arrayref::*;

                    libcrux_p256::P256::keygen(verification_key, signing_key, &randomness)
                        .map_err(|e| match e {
                            libcrux_traits::kem::arrayref::KeyGenError::InvalidRandomness => arrayref::KeyGenError::InvalidRandomness,

                            libcrux_traits::kem::arrayref::KeyGenError::Unknown => arrayref::KeyGenError::LibraryError,
                        })
                }
            }
            libcrux_traits::impl_signature_slice_trait!(
                $name => SIGNING_KEY_LEN, VERIFICATION_KEY_LEN, SIG_LEN, RAND_KEYGEN_LEN, &Nonce, nonce, (), _aux, u8);
        };
    }

    pub mod p256 {
        //! [`libcrux_traits::signature`] APIs for p256.

        use super::*;

        use crate::p256::Nonce;

        impl_signature_trait!(
            Sha256,
            Signer_Sha2_256,
            ecdsa_sign_p256_sha2,
            ecdsa_verif_p256_sha2
        );
        impl_signature_trait!(
            Sha384,
            Signer_Sha2_384,
            ecdsa_sign_p256_sha384,
            ecdsa_verif_p256_sha384
        );
        impl_signature_trait!(
            Sha512,
            Signer_Sha2_512,
            ecdsa_sign_p256_sha512,
            ecdsa_verif_p256_sha512
        );
    }
}
