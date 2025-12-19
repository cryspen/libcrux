//! This module includes key-centric and slice-based APIs for Ed25519.
//!
//! ### Key-centric APIs
//! This module provides key-centric APIs for Ed25519.
//!
//! #### Key-centric (owned)
//! ```rust
//! use libcrux_ed25519::key_centric_apis::{SigningKey, KeyPair, VerificationKey};
//!
//! // generate key pair
//! let KeyPair { signing_key, verification_key } = KeyPair::generate_derand([0u8; 32]);
//!
//! // sign and verify
//! let signature = signing_key.sign(b"payload").unwrap();
//! verification_key.verify(b"payload", &signature).unwrap();
//! ```
//!
//! #### Key-centric (reference)
//! ```rust
//! # use libcrux_ed25519::key_centric_apis::{
//! #     Ed25519, SigningKeyRef, VerificationKeyRef,
//! # };
//! # use libcrux_traits::signature::SignConsts;
//! #
//! # // key generation
//! # let mut signing_key = [0u8; Ed25519::SIGNING_KEY_LEN];
//! # let mut verification_key = [0u8; Ed25519::VERIFICATION_KEY_LEN];
//! # Ed25519::keygen(&mut signing_key, &mut verification_key, [0; 32]).unwrap();
//! #
//! // create key structs from references
//! let signing_key = SigningKeyRef::from_slice(&signing_key).unwrap();
//! let verification_key = VerificationKeyRef::from_slice(&verification_key).unwrap();
//!
//! // signature buffer
//! let mut signature = [0u8; Ed25519::SIGNATURE_LEN];
//!
//! // sign and verify
//! signing_key
//!     .sign(b"payload", &mut signature)
//!     .unwrap();
//! verification_key
//!     .verify(b"payload", &signature)
//!     .unwrap();
//! ```
//!
//! ### Slice-based APIs
//! This module also provides slice-based APIs via the struct [`Ed25519`].
//!
//! ```rust
//! use libcrux_ed25519::key_centric_apis::Ed25519;
//! use libcrux_traits::signature::SignConsts;
//!
//! // keygen
//! let mut signing_key = [0u8; Ed25519::SIGNING_KEY_LEN];
//! let mut verification_key = [0u8; Ed25519::VERIFICATION_KEY_LEN];
//! Ed25519::keygen(&mut signing_key, &mut verification_key, [0; 32]);
//!
//! // signature buffer
//! let mut signature = [0u8; Ed25519::SIGNATURE_LEN];
//!
//! // sign and verify
//! Ed25519::sign(&signing_key, b"payload", &mut signature).unwrap();
//! Ed25519::verify(&verification_key, b"payload", &signature).unwrap();
//! ```
use libcrux_traits::signature::{
    impl_key_centric_types, impl_sign_consts, SignConsts, WrongLengthError,
};

use libcrux_secrets::{Classify, DeclassifyRef, U8};
const VERIFICATION_KEY_LEN: usize = 32;
const SIGNING_KEY_LEN: usize = 32;
const SIGNATURE_LEN: usize = 64;
const RAND_KEYGEN_LEN: usize = SIGNING_KEY_LEN;

#[doc(inline)]
pub use slice::Ed25519;

#[doc(inline)]
pub use arrayref::{SigningError, VerificationError};

impl_key_centric_types!(
    arrayref::Ed25519,
    SIGNING_KEY_LEN,
    VERIFICATION_KEY_LEN,
    SIGNATURE_LEN,
    RAND_KEYGEN_LEN,
    WrongLengthError,
    WrongLengthError
);
/// XXX: Decide whether we need these here (or need them to be public).
pub(crate) mod arrayref {
    #[derive(Debug, PartialEq)]
    pub(crate) struct Ed25519;

    /// An error when signing.
    #[derive(Debug, PartialEq)]
    pub enum SigningError {
        /// The length of the provided payload is invalid.
        InvalidPayloadLength,
    }

    impl From<SigningError> for super::slice::SigningError {
        fn from(e: SigningError) -> Self {
            match e {
                SigningError::InvalidPayloadLength => {
                    super::slice::SigningError::InvalidPayloadLength
                }
            }
        }
    }

    /// An error when verifying a signature.
    #[derive(Debug)]
    pub enum VerificationError {
        /// The provided signature is invalid.
        InvalidSignature,
        /// The length of the provided payload is invalid.
        InvalidPayloadLength,
    }

    impl From<VerificationError> for super::slice::VerificationError {
        fn from(e: VerificationError) -> Self {
            match e {
                VerificationError::InvalidSignature => {
                    super::slice::VerificationError::InvalidSignature
                }
                VerificationError::InvalidPayloadLength => {
                    super::slice::VerificationError::InvalidPayloadLength
                }
            }
        }
    }
}
/// XXX: Decide whether we need these here (or need them to be public).
pub(crate) mod slice {
    //! Slice-based APIs for Ed25519.
    //!
    //! ```rust
    //! use libcrux_traits::signature::SignConsts;
    //! use libcrux_ed25519::key_centric_apis::slice::Ed25519;
    //!
    //! // generate keypair
    //! let mut signing_key = [0u8; Ed25519::SIGNING_KEY_LEN];
    //! let mut verification_key = [0u8; Ed25519::VERIFICATION_KEY_LEN];
    //! Ed25519::keygen(&mut signing_key, &mut verification_key, [0; 32]);
    //!
    //! // create signature buffer
    //! let mut signature = [0u8; Ed25519::SIGNATURE_LEN];
    //!
    //! // sign
    //! Ed25519::sign(&signing_key, b"payload", &mut signature).unwrap();
    //!
    //! // verify
    //! Ed25519::verify(&verification_key, b"payload", &signature).unwrap();
    //!  ```

    /// Slice-based APIs for Ed25519.
    ///
    /// This struct provides slice-based APIs for Ed25519, as well as an implementation
    /// of the [`SignConsts`] trait, which can be used to retrieve constants defining
    /// the verification key length, signing key length, signature length, and the
    /// length of the randomness required for key generation for the signature scheme.
    #[derive(Debug, PartialEq)]
    pub struct Ed25519;
    use super::*;
    impl_sign_consts!(
        Ed25519,
        SIGNING_KEY_LEN,
        VERIFICATION_KEY_LEN,
        SIGNATURE_LEN,
        RAND_KEYGEN_LEN
    );

    /// An error when signing.
    #[derive(Debug)]
    pub enum SigningError {
        /// The length of the provided signing key is incorrect.
        WrongSigningKeyLength,
        /// The length of the provided signature buffer is incorrect.
        WrongSignatureLength,
        /// The length of the provided payload is invalid.
        InvalidPayloadLength,
    }

    /// An error when verifying a signature.
    #[derive(Debug)]
    pub enum VerificationError {
        /// The provided signature is invalid.
        InvalidSignature,
        /// The length of the provided verification key is incorrect.
        WrongVerificationKeyLength,
        /// The length of the provided signature is incorrect.
        WrongSignatureLength,
        /// The length of the provided payload is invalid.
        InvalidPayloadLength,
    }

    /// An error when generating a signature key pair.
    #[derive(Debug)]
    pub enum KeygenError {
        /// The length of the provided signing key buffer is incorrect.
        WrongSigningKeyLength,
        /// The length of the provided verification key buffer is incorrect.
        WrongVerificationKeyLength,
    }
}

impl crate::Ed25519KeyPair {
    #[cfg(feature = "rand")]
    /// Generate an Ed25519 key pair
    pub fn generate(rng: &mut impl rand_core::CryptoRng) -> Self {
        crate::generate_key_pair(rng)
    }

    /// Generate an Ed25519 key pair (derand)
    pub fn generate_derand(bytes: [U8; RAND_KEYGEN_LEN]) -> crate::Ed25519KeyPair {
        let mut signing_key = [0u8; arrayref::Ed25519::SIGNING_KEY_LEN].classify();
        let mut verification_key = [0u8; arrayref::Ed25519::VERIFICATION_KEY_LEN];
        arrayref::Ed25519::keygen(&mut signing_key, &mut verification_key, bytes);

        crate::Ed25519KeyPair {
            signing_key: crate::SigningKey::from_bytes(signing_key),
            verification_key: crate::VerificationKey::from_bytes(verification_key),
        }
    }
}

/// XXX: Decide whether we need these here (or need them to be public).                
impl arrayref::Ed25519 {
    pub(crate) fn sign(
        key: &[U8; Self::SIGNING_KEY_LEN],
        payload: &[u8],
        signature: &mut [u8; Self::SIGNATURE_LEN],
    ) -> Result<(), arrayref::SigningError> {
        let payload_len: u32 = payload
            .len()
            .try_into()
            .map_err(|_| arrayref::SigningError::InvalidPayloadLength)?;

        crate::hacl::ed25519::sign(signature, key.declassify_ref(), payload_len, payload);

        Ok(())
    }

    #[inline(always)]
    pub(crate) fn verify(
        key: &[u8; Self::VERIFICATION_KEY_LEN],
        payload: &[u8],
        signature: &[u8; Self::SIGNATURE_LEN],
    ) -> Result<(), arrayref::VerificationError> {
        let payload_len: u32 = payload
            .len()
            .try_into()
            .map_err(|_| arrayref::VerificationError::InvalidPayloadLength)?;

        if crate::hacl::ed25519::verify(key, payload_len, payload, signature) {
            Ok(())
        } else {
            Err(arrayref::VerificationError::InvalidSignature)
        }
    }
    pub(crate) fn keygen(
        signing_key: &mut [U8; Self::SIGNING_KEY_LEN],
        verification_key: &mut [u8; Self::VERIFICATION_KEY_LEN],
        randomness: [U8; Self::RAND_KEYGEN_LEN],
    ) {
        *signing_key = randomness;
        crate::secret_to_public(verification_key, signing_key.declassify_ref());
    }
}

/// XXX: Decide whether we need these here (or need them to be public).
impl slice::Ed25519 {
    pub(crate) fn sign(
        key: &[U8],
        payload: &[u8],
        signature: &mut [u8],
    ) -> Result<(), slice::SigningError> {
        let key = key
            .try_into()
            .map_err(|_| slice::SigningError::WrongSigningKeyLength)?;
        let signature = signature
            .try_into()
            .map_err(|_| slice::SigningError::WrongSignatureLength)?;

        arrayref::Ed25519::sign(&key, payload, signature).map_err(slice::SigningError::from)
    }

    pub(crate) fn verify(
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

        arrayref::Ed25519::verify(key, payload, signature).map_err(slice::VerificationError::from)
    }

    pub(crate) fn keygen(
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

        arrayref::Ed25519::keygen(signing_key, verification_key, randomness);

        Ok(())
    }
}

/// XXX: Decide whether we need these here (or need them to be public).
impl<'a> SigningKeyRef<'a> {
    pub(crate) fn sign(
        &self,
        payload: &[u8],
        signature: &mut [u8],
    ) -> Result<(), slice::SigningError> {
        slice::Ed25519::sign(self.as_ref(), payload, signature)
    }
}
/// XXX: Decide whether we need these here (or need them to be public).
impl<'a> VerificationKeyRef<'a> {
    pub(crate) fn verify(
        &self,
        payload: &[u8],
        signature: &[u8],
    ) -> Result<(), slice::VerificationError> {
        slice::Ed25519::verify(self.as_ref(), payload, signature)
    }
}

// key-centric API
impl crate::SigningKey {
    pub fn sign(&self, message: &[u8]) -> Result<crate::Signature, crate::Error> {
        crate::sign(message, &self.value).map(|sig_bytes| sig_bytes.into())
    }
}

impl crate::VerificationKey {
    pub fn verify(&self, message: &[u8], signature: &crate::Signature) -> Result<(), crate::Error> {
        crate::verify(message, &self.value, &signature.0)
    }
}

#[test]
#[cfg(feature = "rand")]
fn key_centric_owned() {
    use rand::TryRngCore;
    let mut rng = rand::rngs::OsRng;
    let mut rng = rng.unwrap_mut();
    use libcrux_traits::signature::SignConsts;

    // keys can be created from arrays
    let _signing_key = SigningKey::from([0u8; Ed25519::SIGNING_KEY_LEN].classify());
    let _verification_key = VerificationKey::from([0u8; Ed25519::VERIFICATION_KEY_LEN]);

    // key-centric API
    let KeyPair {
        signing_key,
        verification_key,
    } = KeyPair::generate(&mut rng);

    let signature = signing_key.sign(b"payload").unwrap();
    verification_key.verify(b"payload", &signature).unwrap();
}

#[test]
#[cfg(all(feature = "rand", not(feature = "expose-secret-independence")))]
fn key_centric_refs() {
    use libcrux_traits::signature::SignConsts;

    let mut signing_key = [0u8; Ed25519::SIGNING_KEY_LEN];
    let mut verification_key = [0u8; Ed25519::VERIFICATION_KEY_LEN];
    Ed25519::keygen(&mut signing_key, &mut verification_key, [0; 32]).unwrap();

    // create references from slice
    let signing_key = SigningKeyRef::from_slice(&signing_key).unwrap();
    let verification_key = VerificationKeyRef::from_slice(&verification_key).unwrap();

    let mut signature = [0u8; Ed25519::SIGNATURE_LEN];
    signing_key.sign(b"payload", &mut signature).unwrap();
    verification_key.verify(b"payload", &signature).unwrap();
}

#[test]
#[cfg(not(feature = "expose-secret-independence"))]
fn arrayref_apis() {
    use libcrux_traits::signature::SignConsts;

    let mut signing_key = [0u8; arrayref::Ed25519::SIGNING_KEY_LEN];
    let mut verification_key = [0u8; arrayref::Ed25519::VERIFICATION_KEY_LEN];
    arrayref::Ed25519::keygen(&mut signing_key, &mut verification_key, [0; 32]);

    // arrayref API
    let mut signature = [0u8; arrayref::Ed25519::SIGNATURE_LEN];
    arrayref::Ed25519::sign(&signing_key, b"payload", &mut signature).unwrap();
    arrayref::Ed25519::verify(&verification_key, b"payload", &signature).unwrap();
}
