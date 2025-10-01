pub mod signers {
    //! [`libcrux_traits::signature`] APIs.

    use libcrux_traits::signature::arrayref;

    const SIGNING_KEY_LEN: usize = 32;
    const VERIFICATION_KEY_LEN: usize = 64;
    const SIG_LEN: usize = 64;
    const RAND_KEYGEN_LEN: usize = 32;

    macro_rules! impl_signature_traits {
        (
            $alias:ident,
            $name:ty,
            $sign_fn:ident,
            $verify_fn:ident
        ) => {
            pub type $alias = Signer<$name>;

            /// The [`arrayref`](libcrux_traits::signature::arrayref) version of the Sign trait.
            impl arrayref::Sign<SIGNING_KEY_LEN, VERIFICATION_KEY_LEN, SIG_LEN, RAND_KEYGEN_LEN> for Signer<$name> {
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
                Signer<$name> => SIGNING_KEY_LEN, VERIFICATION_KEY_LEN, SIG_LEN, RAND_KEYGEN_LEN, &Nonce, nonce, (), _aux, u8);

            // key centric APIs
            libcrux_traits::signature::key_centric_owned::impl_key_centric_owned!(
                Signer<$name>,
                SIGNING_KEY_LEN,
                VERIFICATION_KEY_LEN,
                SIG_LEN,
                RAND_KEYGEN_LEN
            );

        };
    }

    pub mod p256 {
        //! [`libcrux_traits::signature`] APIs for p256.

        use super::*;

        pub use crate::p256::Nonce;

        /// A P256 signer.
        pub struct Signer<T> {
            _marker: core::marker::PhantomData<T>,
        }
        pub use libcrux_sha2::{Sha256 as Sha2_256, Sha384 as Sha2_384, Sha512 as Sha2_512};

        impl_signature_traits!(
            Sha2_256Signer,
            Sha2_256,
            ecdsa_sign_p256_sha2,
            ecdsa_verif_p256_sha2
        );

        impl_signature_traits!(
            Sha2_384Signer,
            Sha2_384,
            ecdsa_sign_p256_sha384,
            ecdsa_verif_p256_sha384
        );

        impl_signature_traits!(
            Sha2_512Signer,
            Sha2_512,
            ecdsa_sign_p256_sha512,
            ecdsa_verif_p256_sha512
        );
    }
}
