//! This module includes key-centric and slice-based APIs for ECDSA-P256.
//!
//! ### Key-centric APIs
//! This module provides key-centric APIs for ECDSA-P256.
//!
//! #### Key-centric (owned)
//! ```rust
//! # use libcrux_ecdsa::key_centric_apis::sha2_256::{SigningKey, KeyPair, VerificationKey};
//! # use rand::TryRngCore;
//! # use libcrux_ecdsa::p256::Nonce;
//! # let mut rng = rand_core::OsRng;
//! # let mut rng = rng.unwrap_mut();
//!
//! // generate key pair
//! let KeyPair { signing_key, verification_key } = KeyPair::generate(&mut rng).unwrap();
//!
//! // sign and verify
//! let nonce = Nonce::random(&mut rng).unwrap();
//! let signature = signing_key.sign(b"payload", &nonce).unwrap();
//! verification_key.verify(b"payload", &signature).unwrap();
//! ```
//!
//! #### Key-centric (reference)
//! ```rust
//! # use libcrux_ecdsa::key_centric_apis::sha2_256::{
//! #     EcdsaP256, SigningKeyRef, VerificationKeyRef,
//! # };
//! # use libcrux_traits::signature::SignConsts;
//! #
//! # // key generation
//! # let mut signing_key = [0u8; EcdsaP256::SIGNING_KEY_LEN];
//! # let mut verification_key = [0u8; EcdsaP256::VERIFICATION_KEY_LEN];
//! # EcdsaP256::keygen(&mut signing_key, &mut verification_key, [0; 32]).unwrap();
//! #
//! # use rand::TryRngCore;
//! # use libcrux_ecdsa::p256::Nonce;
//! # let mut rng = rand_core::OsRng;
//! # let mut rng = rng.unwrap_mut();
//!
//! // create key structs from references
//! let signing_key = SigningKeyRef::from_slice(&signing_key).unwrap();
//! let verification_key = VerificationKeyRef::from_slice(&verification_key).unwrap();
//!
//! // signature buffer
//! let mut signature = [0u8; EcdsaP256::SIGNATURE_LEN];
//!
//! // sign and verify
//! let nonce = Nonce::random(&mut rng).unwrap();
//! signing_key
//!     .sign(b"payload", &mut signature, &nonce)
//!     .unwrap();
//! verification_key
//!     .verify(b"payload", &signature)
//!     .unwrap();
//! ```
//!
//! ### Slice-based APIs
//! This module also provides slice-based APIs via the structs [`sha2_256::EcdsaP256`], [`sha2_384::EcdsaP256`] and
//! [`sha2_512::EcdsaP256`].
//!
//! ```rust
//! # use libcrux_ecdsa::key_centric_apis::sha2_256::EcdsaP256;
//! # use libcrux_traits::signature::SignConsts;
//! #
//! # use rand::TryRngCore;
//! # use libcrux_ecdsa::p256::Nonce;
//! # let mut rng = rand_core::OsRng;
//! # let mut rng = rng.unwrap_mut();
//!
//! // keygen
//! let mut signing_key = [0u8; EcdsaP256::SIGNING_KEY_LEN];
//! let mut verification_key = [0u8; EcdsaP256::VERIFICATION_KEY_LEN];
//! EcdsaP256::keygen(&mut signing_key, &mut verification_key, [0; 32]);
//!
//! // signature buffer
//! let mut signature = [0u8; EcdsaP256::SIGNATURE_LEN];
//!
//! // sign and verify
//! let nonce = Nonce::random(&mut rng).unwrap();
//! EcdsaP256::sign(&signing_key, b"payload", &mut signature, &nonce).unwrap();
//! EcdsaP256::verify(&verification_key, b"payload", &signature).unwrap();
//! ```

use crate::p256::Nonce;
use libcrux_traits::signature::{
    impl_key_centric_types, impl_sign_consts, SignConsts, WrongLengthError,
};

macro_rules! impl_mod {
    ($ty:ident, $module:ident,
            $sign_fn:ident,
            $verify_fn:ident) => {
        use libcrux_secrets::{Classify, DeclassifyRef, U8};

        const SIGNING_KEY_LEN: usize = 32;
        const VERIFICATION_KEY_LEN: usize = 64;
        const SIGNATURE_LEN: usize = 64;
        const RAND_KEYGEN_LEN: usize = 32;

        use super::*;

        #[doc(inline)]
        pub use self::{
            arrayref::{
                KeyPair, Signature, SigningKey, SigningKeyRef, VerificationKey, VerificationKeyRef,
            },
            slice::*,
        };

        pub(crate) mod arrayref {
            #[derive(Debug, PartialEq)]
            pub(crate) struct $ty;
            use super::*;
            impl_key_centric_types!(
                $ty,
                SIGNING_KEY_LEN,
                VERIFICATION_KEY_LEN,
                SIGNATURE_LEN,
                RAND_KEYGEN_LEN,
                WrongLengthError,
                WrongLengthError
            );
        }
        pub mod slice {
            //! Slice-based APIs for ECDSA-P256.
            //!
            //! ```rust
            //! use libcrux_traits::signature::SignConsts;
            //! use libcrux_ecdsa::key_centric_apis::sha2_256::slice::EcdsaP256;
            //! use libcrux_ecdsa::p256::Nonce;
            //!
            //! use rand::{RngCore, TryRngCore};
            //! let mut rng = rand_core::OsRng;
            //! let mut rng = rng.unwrap_mut();
            //!
            //! let mut signing_key = [0u8; EcdsaP256::SIGNING_KEY_LEN];
            //! let mut verification_key = [0u8; EcdsaP256::VERIFICATION_KEY_LEN];
            //!
            //! // keygen
            //! let mut bytes = [0u8; EcdsaP256::RAND_KEYGEN_LEN];
            //! rng.fill_bytes(&mut bytes);
            //! EcdsaP256::keygen(&mut signing_key, &mut verification_key, bytes).unwrap();
            //!
            //! // sign
            //! let mut signature = [0u8; EcdsaP256::SIGNATURE_LEN];
            //! EcdsaP256::sign(
            //!     &signing_key,
            //!     b"payload",
            //!     &mut signature,
            //!     &Nonce::random(&mut rng).unwrap(),
            //! )
            //! .unwrap();
            //!
            //! // verify
            //! EcdsaP256::verify(&verification_key, b"payload", &signature).unwrap();
            //! ```

            /// Slice-based APIs for ECDSA-P256.
            #[derive(Debug, PartialEq)]
            pub struct $ty;
            use super::*;
            impl_sign_consts!(
                $ty,
                SIGNING_KEY_LEN,
                VERIFICATION_KEY_LEN,
                SIGNATURE_LEN,
                RAND_KEYGEN_LEN
            );

            // error type including wrong length
            #[derive(Debug)]
            pub enum SigningError {
                WrongSigningKeyLength,
                WrongSignatureLength,
                InvalidArgument,
                UnknownError,
            }

            // error type including wrong length
            #[derive(Debug)]
            pub enum VerificationError {
                WrongVerificationKeyLength,
                WrongSignatureLength,
                WrongPayloadLength,
                UnknownError,
            }

            #[derive(Debug)]
            pub enum KeygenError {
                InvalidRandomness,
                WrongSigningKeyLength,
                WrongVerificationKeyLength,
                UnknownError,
            }
        }

        impl KeyPair {
            #[cfg(feature = "rand")]
            /// Generate an ECDSA-P256 key pair
            pub fn generate(rng: &mut impl rand::CryptoRng) -> Result<KeyPair, slice::KeygenError> {
                let mut bytes = [0u8; arrayref::$ty::RAND_KEYGEN_LEN];
                rng.fill_bytes(&mut bytes);

                Self::generate_derand(bytes.classify())
            }

            /// Generate an ECDSA-P256 key pair (derand)
            pub fn generate_derand(
                bytes: [U8; RAND_KEYGEN_LEN],
            ) -> Result<KeyPair, slice::KeygenError> {
                let mut signing_key = [0u8; arrayref::$ty::SIGNING_KEY_LEN].classify();
                let mut verification_key = [0u8; arrayref::$ty::VERIFICATION_KEY_LEN];
                arrayref::$ty::keygen(&mut signing_key, &mut verification_key, bytes.classify())?;

                Ok(KeyPair {
                    signing_key: SigningKey::from(signing_key),
                    verification_key: VerificationKey::from(verification_key),
                })
            }
        }
        impl arrayref::$ty {
            /// Sign the `payload` with the `key`.
            pub fn sign(
                key: &[U8; Self::SIGNING_KEY_LEN],
                payload: &[u8],
                signature: &mut [u8; Self::SIGNATURE_LEN],
                nonce: &Nonce,
            ) -> Result<(), slice::SigningError> {
                let result = libcrux_p256::$sign_fn(
                    signature,
                    payload
                        .len()
                        .try_into()
                        .map_err(|_| slice::SigningError::InvalidArgument)?,
                    payload,
                    key.declassify_ref(),
                    &nonce.0,
                );
                if !result {
                    return Err(slice::SigningError::UnknownError);
                }
                Ok(())
            }

            /// Verify the `payload` and `signature` with the `key`.
            pub fn verify(
                key: &[u8; Self::VERIFICATION_KEY_LEN],
                payload: &[u8],
                signature: &[u8; Self::SIGNATURE_LEN],
            ) -> Result<(), slice::VerificationError> {
                let result = libcrux_p256::$verify_fn(
                    payload
                        .len()
                        .try_into()
                        .map_err(|_| slice::VerificationError::WrongPayloadLength)?,
                    payload,
                    key,
                    <&[u8; 32]>::try_from(&signature[0..32]).unwrap(),
                    <&[u8; 32]>::try_from(&signature[32..]).unwrap(),
                );
                if !result {
                    return Err(slice::VerificationError::UnknownError);
                }
                Ok(())
            }
            pub fn keygen(
                signing_key: &mut [U8; Self::SIGNING_KEY_LEN],
                verification_key: &mut [u8; Self::VERIFICATION_KEY_LEN],
                randomness: [U8; Self::RAND_KEYGEN_LEN],
            ) -> Result<(), slice::KeygenError> {
                use libcrux_p256::ecdh_api::EcdhArrayref;

                libcrux_p256::P256::generate_pair(verification_key, signing_key, &randomness)
                    .map_err(|err| match err {
                        libcrux_traits::ecdh::arrayref::GenerateSecretError::InvalidRandomness => {
                            slice::KeygenError::InvalidRandomness
                        }
                        libcrux_traits::ecdh::arrayref::GenerateSecretError::Unknown => {
                            slice::KeygenError::UnknownError
                        }
                    })?;

                Ok(())
            }
        }
        impl slice::$ty {
            /// Sign the `payload` with the `key`.
            pub fn sign(
                key: &[U8],
                payload: &[u8],
                signature: &mut [u8],
                nonce: &Nonce,
            ) -> Result<(), slice::SigningError> {
                let key = key
                    .try_into()
                    .map_err(|_| slice::SigningError::WrongSigningKeyLength)?;
                let signature = signature
                    .try_into()
                    .map_err(|_| slice::SigningError::WrongSignatureLength)?;

                arrayref::$ty::sign(&key, payload, signature, nonce)
                    .map_err(slice::SigningError::from)
            }
            /// Verify the `payload` and `signature` with the `key`.
            pub fn verify(
                key: &[u8],
                payload: &[u8],
                signature: &[u8],
            ) -> Result<(), slice::VerificationError> {
                let key = key
                    .try_into()
                    .map_err(|_| slice::VerificationError::WrongVerificationKeyLength)?;
                let signature = signature
                    .try_into()
                    .map_err(|_| slice::VerificationError::WrongSignatureLength)?;

                arrayref::$ty::verify(key, payload, signature)
                    .map_err(slice::VerificationError::from)
            }
            pub fn keygen(
                signing_key: &mut [U8],
                verification_key: &mut [u8],
                randomness: [U8; Self::RAND_KEYGEN_LEN],
            ) -> Result<(), slice::KeygenError> {
                let signing_key = signing_key
                    .try_into()
                    .map_err(|_| slice::KeygenError::WrongSigningKeyLength)?;
                let verification_key = verification_key
                    .try_into()
                    .map_err(|_| slice::KeygenError::WrongVerificationKeyLength)?;

                arrayref::$ty::keygen(signing_key, verification_key, randomness)
            }
        }
        impl<'a> SigningKeyRef<'a> {
            /// Sign the `payload`.
            pub fn sign(
                &self,
                payload: &[u8],
                signature: &mut [u8],
                nonce: &Nonce,
            ) -> Result<(), slice::SigningError> {
                slice::$ty::sign(self.as_ref(), payload, signature, nonce)
            }
        }
        impl<'a> VerificationKeyRef<'a> {
            /// Verify the `payload` and `signature`.
            pub fn verify(
                &self,
                payload: &[u8],
                signature: &[u8],
            ) -> Result<(), slice::VerificationError> {
                slice::$ty::verify(self.as_ref(), payload, signature)
            }
        }

        // key-centric API
        impl SigningKey {
            /// Sign the `payload`.
            pub fn sign(
                &self,
                payload: &[u8],
                nonce: &Nonce,
            ) -> Result<Signature, slice::SigningError> {
                let mut signature = [0u8; SIGNATURE_LEN];
                arrayref::$ty::sign(self.as_ref(), payload, &mut signature, nonce)
                    .map(|_| Signature::from(signature))
            }
        }
        impl VerificationKey {
            /// Verify the `payload` and `signature`.
            pub fn verify(
                &self,
                payload: &[u8],
                signature: &Signature,
            ) -> Result<(), slice::VerificationError> {
                arrayref::$ty::verify(self.as_ref(), payload, signature.as_ref())
            }
        }
    };
}

pub mod sha2_256 {
    impl_mod!(
        EcdsaP256,
        Sha2_256,
        ecdsa_sign_p256_sha2,
        ecdsa_verif_p256_sha2
    );
}

pub mod sha2_384 {
    impl_mod!(
        EcdsaP256,
        Sha2_384,
        ecdsa_sign_p256_sha384,
        ecdsa_verif_p256_sha384
    );
}

pub mod sha2_512 {
    impl_mod!(
        EcdsaP256,
        Sha2_512,
        ecdsa_sign_p256_sha512,
        ecdsa_verif_p256_sha512
    );
}

#[test]
#[cfg(all(feature = "rand", not(feature = "expose-secret-independence")))]
fn key_centric_owned() {
    use rand::TryRngCore;
    let mut rng = rand_core::OsRng;
    let mut rng = rng.unwrap_mut();
    use libcrux_traits::signature::SignConsts;

    use sha2_256::{EcdsaP256, KeyPair, SigningKey, VerificationKey};

    // keys can be created from arrays
    let _signing_key = SigningKey::from([0u8; EcdsaP256::SIGNING_KEY_LEN]);
    let _verification_key = VerificationKey::from([0u8; EcdsaP256::VERIFICATION_KEY_LEN]);

    // key-centric API
    let KeyPair {
        signing_key,
        verification_key,
    } = KeyPair::generate(&mut rng).unwrap();

    let signature = signing_key
        .sign(b"payload", &Nonce::random(&mut rng).unwrap())
        .unwrap();
    verification_key.verify(b"payload", &signature).unwrap();
}

#[test]
#[cfg(all(feature = "rand", not(feature = "expose-secret-independence")))]
fn key_centric_refs() {
    use libcrux_traits::signature::SignConsts;
    use sha2_256::{EcdsaP256, SigningKeyRef, VerificationKeyRef};

    use rand::{RngCore, TryRngCore};
    let mut rng = rand_core::OsRng;
    let mut rng = rng.unwrap_mut();

    let mut signing_key = [0u8; EcdsaP256::SIGNING_KEY_LEN];
    let mut verification_key = [0u8; EcdsaP256::VERIFICATION_KEY_LEN];

    let mut bytes = [0u8; EcdsaP256::RAND_KEYGEN_LEN];
    rng.fill_bytes(&mut bytes);
    EcdsaP256::keygen(&mut signing_key, &mut verification_key, bytes).unwrap();

    // create references from slice
    let signing_key = SigningKeyRef::from_slice(&signing_key).unwrap();
    let verification_key = VerificationKeyRef::from_slice(&verification_key).unwrap();

    let mut signature = [0u8; EcdsaP256::SIGNATURE_LEN];
    signing_key
        .sign(
            b"payload",
            &mut signature,
            &Nonce::random(&mut rng).unwrap(),
        )
        .unwrap();
    verification_key.verify(b"payload", &signature).unwrap();
}
