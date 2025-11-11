use crate::p256::Nonce;
use libcrux_traits::signature::{impl_key_centric_types, impl_sign_traits, SignConsts};

macro_rules! impl_mod {
    ($ty:ident, $module:ident,
            $sign_fn:ident,
            $verify_fn:ident) => {
        use libcrux_secrets::{DeclassifyRef, U8};

        const SIGNING_KEY_LEN: usize = 32;
        const VERIFICATION_KEY_LEN: usize = 64;
        const SIGNATURE_LEN: usize = 64;
        const RAND_KEYGEN_LEN: usize = 32;

        use super::*;
        // arrayref API
        #[doc(inline)]
        pub use arrayref::*;

        // TODO: different error type?
        #[derive(Debug)]
        /// An incorrect length when converting from slice.
        pub struct WrongLengthError;

        pub mod arrayref {
            #[derive(Debug, PartialEq)]
            pub struct $ty;
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
            #[derive(Debug, PartialEq)]
            pub struct $ty;
            use super::*;
            impl_sign_traits!(
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

        impl arrayref::$ty {
            #[cfg(feature = "rand")]
            pub fn generate_key_pair(
                rng: &mut impl rand::CryptoRng,
            ) -> Result<KeyPair, slice::KeygenError> {
                use libcrux_secrets::Classify;

                let mut bytes = [0u8; Self::RAND_KEYGEN_LEN];
                rng.fill_bytes(&mut bytes);
                let mut signing_key = [0u8; Self::SIGNING_KEY_LEN].classify();
                let mut verification_key = [0u8; Self::VERIFICATION_KEY_LEN];
                arrayref::$ty::keygen_derand(
                    &mut signing_key,
                    &mut verification_key,
                    bytes.classify(),
                )?;

                Ok(KeyPair {
                    signing_key: SigningKey::from(signing_key),
                    verification_key: VerificationKey::from(verification_key),
                })
            }
        }
        impl arrayref::$ty {
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
            pub fn keygen_derand(
                signing_key: &mut [U8; Self::SIGNING_KEY_LEN],
                verification_key: &mut [u8; Self::VERIFICATION_KEY_LEN],
                randomness: [U8; Self::RAND_KEYGEN_LEN],
            ) -> Result<(), slice::KeygenError> {
                use libcrux_traits::ecdh::arrayref::*;

                libcrux_p256::P256::secret_to_public(verification_key, &randomness).map_err(
                    |err| match err {
                        libcrux_traits::ecdh::arrayref::SecretToPublicError::InvalidSecret => {
                            slice::KeygenError::InvalidRandomness
                        }
                        libcrux_traits::ecdh::arrayref::SecretToPublicError::Unknown => {
                            slice::KeygenError::UnknownError
                        }
                    },
                )?;
                *signing_key = randomness;

                Ok(())
            }
        }
        impl slice::$ty {
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
            pub fn keygen_derand(
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

                arrayref::$ty::keygen_derand(signing_key, verification_key, randomness)
            }
        }
        impl<'a> SigningKeyRef<'a> {
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
    } = EcdsaP256::generate_key_pair(&mut rng).unwrap();

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
    EcdsaP256::keygen_derand(&mut signing_key, &mut verification_key, bytes).unwrap();

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

#[test]
#[cfg(not(feature = "expose-secret-independence"))]
fn arrayref_apis() {
    use libcrux_traits::signature::SignConsts;
    use sha2_256::EcdsaP256;

    use rand::{RngCore, TryRngCore};
    let mut rng = rand_core::OsRng;
    let mut rng = rng.unwrap_mut();

    let mut signing_key = [0u8; EcdsaP256::SIGNING_KEY_LEN];
    let mut verification_key = [0u8; EcdsaP256::VERIFICATION_KEY_LEN];

    let mut bytes = [0u8; EcdsaP256::RAND_KEYGEN_LEN];
    rng.fill_bytes(&mut bytes);
    EcdsaP256::keygen_derand(&mut signing_key, &mut verification_key, bytes).unwrap();

    // arrayref API
    let mut signature = [0u8; EcdsaP256::SIGNATURE_LEN];
    EcdsaP256::sign(
        &signing_key,
        b"payload",
        &mut signature,
        &Nonce::random(&mut rng).unwrap(),
    )
    .unwrap();
    EcdsaP256::verify(&verification_key, b"payload", &signature).unwrap();
}
#[test]
#[cfg(not(feature = "expose-secret-independence"))]
fn slice_apis() {
    use libcrux_traits::signature::SignConsts;
    use sha2_256::slice::EcdsaP256;

    use rand::{RngCore, TryRngCore};
    let mut rng = rand_core::OsRng;
    let mut rng = rng.unwrap_mut();

    let mut signing_key = [0u8; EcdsaP256::SIGNING_KEY_LEN];
    let mut verification_key = [0u8; EcdsaP256::VERIFICATION_KEY_LEN];

    let mut bytes = [0u8; EcdsaP256::RAND_KEYGEN_LEN];
    rng.fill_bytes(&mut bytes);
    EcdsaP256::keygen_derand(&mut signing_key, &mut verification_key, bytes).unwrap();

    // slice API
    let mut signature = [0u8; EcdsaP256::SIGNATURE_LEN];
    EcdsaP256::sign(
        &signing_key,
        b"payload",
        &mut signature,
        &Nonce::random(&mut rng).unwrap(),
    )
    .unwrap();
    EcdsaP256::verify(&verification_key, b"payload", &signature).unwrap();
}
