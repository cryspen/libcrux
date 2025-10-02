pub mod signers {
    //! [`libcrux_traits::signature`] APIs.

    use libcrux_secrets::{DeclassifyRef, U8};
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
            #[doc = concat!(
                "ECDSA P256 signer specialized for ",
                stringify!($name),
                " hash algorithm.\n\n",
                "This type alias provides a convenient way to access ECDSA signing and verification\n",
                "operations using the ",
                stringify!($name),
                " hash function. It implements all signature traits from\n",
                "`libcrux_traits::signature` including arrayref, owned, slice, and key-centric APIs.\n\n",
                "# Hash Algorithm\n",
                "Uses ",
                stringify!($name),
                " for message hashing before signing.\n\n",
                "# Key Sizes\n",
                "- Signing keys: 32 bytes\n",
                "- Verification keys: 64 bytes\n",
                "- Signatures: 64 bytes"
            )]
            pub type $alias = Signer<$name>;

            /// The [`arrayref`](libcrux_traits::signature::arrayref) version of the Sign trait.
            impl arrayref::Sign<SIGNING_KEY_LEN, VERIFICATION_KEY_LEN, SIG_LEN, RAND_KEYGEN_LEN> for Signer<$name> {
                /// Sign a payload using a provided signing key and `nonce`.
                #[inline(always)]
                fn sign(
                    payload: &[u8],
                    signing_key: &[U8; SIGNING_KEY_LEN],
                    signature: &mut [u8; SIG_LEN],
                    nonce: &Nonce,
                ) -> Result<(), arrayref::SignError> {
                    let result = libcrux_p256::$sign_fn(
                        signature,
                        payload.len().try_into().map_err(|_| arrayref::SignError::InvalidPayloadLength)?,
                        payload,
                        signing_key.declassify_ref(),
                        &nonce.0,
                    );
                    if !result {
                        return Err(arrayref::SignError::LibraryError);
                    }
                    Ok(())
                }
                #[inline(always)]
                /// Verify a signature using a provided verification key.
                fn verify(
                    payload: &[u8],
                    verification_key: &[u8; VERIFICATION_KEY_LEN],
                    signature: &[u8; SIG_LEN],
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
                fn keygen_derand(
                    signing_key: &mut [U8; SIGNING_KEY_LEN],
                    verification_key: &mut [u8; VERIFICATION_KEY_LEN],
                    randomness: &[U8; RAND_KEYGEN_LEN],
                ) -> Result<(), arrayref::KeyGenError> {
                    use libcrux_traits::ecdh::arrayref::*;

                    libcrux_p256::P256::secret_to_public(verification_key, &randomness).map_err(|err| match err {
                            libcrux_traits::ecdh::arrayref::SecretToPublicError::InvalidSecret => arrayref::KeyGenError::InvalidRandomness,
                            libcrux_traits::ecdh::arrayref::SecretToPublicError::Unknown => arrayref::KeyGenError::LibraryError,

            })?;
                    *signing_key = *randomness;
            Ok(())

                }
            }
            libcrux_traits::impl_signature_slice_trait!(
                Signer<$name> => SIGNING_KEY_LEN, VERIFICATION_KEY_LEN, SIG_LEN, RAND_KEYGEN_LEN, &Nonce, nonce);

            // key centric APIs
            libcrux_traits::signature::key_centric_owned::impl_sign_types!(
                Signer<$name>,
                SIGNING_KEY_LEN,
                VERIFICATION_KEY_LEN,
                SIG_LEN,
                RAND_KEYGEN_LEN,
                &'a Nonce
            );

        };
    }

    pub mod p256 {
        //! [`libcrux_traits::signature`] APIs for p256.

        use super::*;

        pub use crate::p256::Nonce;

        /// Generic ECDSA P256 signer parameterized by hash algorithm.
        ///
        /// This struct provides the foundation for ECDSA signing and verification operations
        /// using the P256 elliptic curve. It is parameterized by a hash algorithm type `Hash`
        /// to support different hash functions while maintaining type safety.
        ///
        /// # Type Parameter
        /// - `Hash`: The hash algorithm type (e.g., `Sha2_256`, `Sha2_384`, `Sha2_512`)
        ///
        /// # Usage
        /// This struct is typically not used directly. Instead, use the specialized type aliases:
        /// - [`Sha2_256Signer`] for SHA-256 hashing
        /// - [`Sha2_384Signer`] for SHA-384 hashing
        /// - [`Sha2_512Signer`] for SHA-512 hashing
        ///
        /// # Security
        /// - Requires a cryptographically secure nonce for each signing operation
        /// - The same nonce must never be reused with the same key and different messages
        /// - Verification is deterministic and does not require additional randomness
        pub struct Signer<Hash> {
            _marker: core::marker::PhantomData<Hash>,
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
