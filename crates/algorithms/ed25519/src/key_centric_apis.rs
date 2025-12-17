use libcrux_traits::signature::{impl_key_centric_types, impl_sign_consts, SignConsts};

use libcrux_secrets::{Classify, DeclassifyRef, U8};
const VERIFICATION_KEY_LEN: usize = 32;
const SIGNING_KEY_LEN: usize = 32;
const SIGNATURE_LEN: usize = 64;
const RAND_KEYGEN_LEN: usize = SIGNING_KEY_LEN;

#[doc(inline)]
pub use slice::Ed25519;

#[doc(inline)]
pub use arrayref::{SigningError, VerificationError};

// TODO: different error type?
#[derive(Debug)]
/// An incorrect length when converting from slice.
pub struct WrongLengthError;

impl_key_centric_types!(
    arrayref::Ed25519,
    SIGNING_KEY_LEN,
    VERIFICATION_KEY_LEN,
    SIGNATURE_LEN,
    RAND_KEYGEN_LEN,
    WrongLengthError,
    WrongLengthError
);

pub(crate) mod arrayref {
    #[derive(Debug, PartialEq)]
    pub(crate) struct Ed25519;

    #[derive(Debug, PartialEq)]
    pub enum SigningError {
        WrongPayloadLength,
    }

    impl From<SigningError> for super::slice::SigningError {
        fn from(e: SigningError) -> Self {
            match e {
                SigningError::WrongPayloadLength => super::slice::SigningError::WrongPayloadLength,
            }
        }
    }

    #[derive(Debug)]
    pub enum VerificationError {
        InvalidSignature,
        WrongPayloadLength,
    }

    impl From<VerificationError> for super::slice::VerificationError {
        fn from(e: VerificationError) -> Self {
            match e {
                VerificationError::InvalidSignature => {
                    super::slice::VerificationError::InvalidSignature
                }
                VerificationError::WrongPayloadLength => {
                    super::slice::VerificationError::WrongPayloadLength
                }
            }
        }
    }
}
pub mod slice {
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

    #[derive(Debug, PartialEq)]
    /// Slice-based APIs for Ed25519.
    pub struct Ed25519;
    use super::*;
    impl_sign_consts!(
        Ed25519,
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
        WrongPayloadLength,
    }

    // error type including wrong length
    #[derive(Debug)]
    pub enum VerificationError {
        InvalidSignature,
        WrongVerificationKeyLength,
        WrongSignatureLength,
        WrongPayloadLength,
    }

    #[derive(Debug)]
    pub enum KeygenError {
        WrongSigningKeyLength,
        WrongVerificationKeyLength,
    }
}

impl KeyPair {
    #[cfg(feature = "rand")]
    pub fn generate(rng: &mut impl rand_core::CryptoRng) -> KeyPair {
        let mut bytes = [0u8; arrayref::Ed25519::RAND_KEYGEN_LEN];
        rng.fill_bytes(&mut bytes);
        let mut signing_key = [0u8; arrayref::Ed25519::SIGNING_KEY_LEN].classify();
        let mut verification_key = [0u8; arrayref::Ed25519::VERIFICATION_KEY_LEN];
        arrayref::Ed25519::keygen(&mut signing_key, &mut verification_key, bytes.classify());

        KeyPair {
            signing_key: SigningKey::from(signing_key),
            verification_key: VerificationKey::from(verification_key),
        }
    }
}
impl arrayref::Ed25519 {
    /// The hacl implementation requires that
    /// - the private key is a 32 byte buffer
    /// - the signature is a 64 byte buffer,
    /// - the payload buffer is not shorter than payload_len.
    ///
    /// We enforce the first two using types, and the latter by using `payload.len()` and `payload_len`.
    /// This has the caveat that `payload_len` must be <= u32::MAX, so we return an error if that is
    /// not the case.
    pub fn sign(
        key: &[U8; Self::SIGNING_KEY_LEN],
        payload: &[u8],
        signature: &mut [u8; Self::SIGNATURE_LEN],
    ) -> Result<(), arrayref::SigningError> {
        crate::hacl::ed25519::sign(
            signature,
            key.declassify_ref(),
            payload
                .len()
                .try_into()
                .map_err(|_| arrayref::SigningError::WrongPayloadLength)?,
            payload,
        );

        Ok(())
    }

    /// The hacl implementation requires that
    /// - the public key is a 32 byte buffer
    /// - the signature is a 64 byte buffer,
    /// - the payload buffer is not shorter than payload_len.
    ///
    /// We enforce the first two using types, and the latter by using `payload.len()` and `payload_len`.
    /// This has the caveat that `payload_len` must be <= u32::MAX, so we return an error if that is
    /// not the case.
    #[inline(always)]
    pub fn verify(
        key: &[u8; Self::VERIFICATION_KEY_LEN],
        payload: &[u8],
        signature: &[u8; Self::SIGNATURE_LEN],
    ) -> Result<(), arrayref::VerificationError> {
        if crate::hacl::ed25519::verify(
            key,
            payload
                .len()
                .try_into()
                .map_err(|_| arrayref::VerificationError::WrongPayloadLength)?,
            payload,
            signature,
        ) {
            Ok(())
        } else {
            Err(arrayref::VerificationError::InvalidSignature)
        }
    }
    pub fn keygen(
        signing_key: &mut [U8; Self::SIGNING_KEY_LEN],
        verification_key: &mut [u8; Self::VERIFICATION_KEY_LEN],
        randomness: [U8; Self::RAND_KEYGEN_LEN],
    ) {
        *signing_key = randomness;
        crate::secret_to_public(verification_key, signing_key.declassify_ref());
    }
}
impl slice::Ed25519 {
    /// The hacl implementation requires that
    /// - the private key is a 32 byte buffer
    /// - the signature is a 64 byte buffer,
    /// - the payload buffer is not shorter than payload_len.
    ///
    /// We enforce the first two using types, and the latter by using `payload.len()` and `payload_len`.
    /// This has the caveat that `payload_len` must be <= u32::MAX, so we return an error if that is
    /// not the case.
    pub fn sign(
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

    /// The hacl implementation requires that
    /// - the public key is a 32 byte buffer
    /// - the signature is a 64 byte buffer,
    /// - the payload buffer is not shorter than payload_len.
    ///
    /// We enforce the first two using types, and the latter by using `payload.len()` and `payload_len`.
    /// This has the caveat that `payload_len` must be <= u32::MAX, so we return an error if that is
    /// not the case.
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

        arrayref::Ed25519::verify(key, payload, signature).map_err(slice::VerificationError::from)
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

        arrayref::Ed25519::keygen(signing_key, verification_key, randomness);

        Ok(())
    }
}
impl<'a> SigningKeyRef<'a> {
    /// The hacl implementation requires that
    /// - the private key is a 32 byte buffer
    /// - the signature is a 64 byte buffer,
    /// - the payload buffer is not shorter than payload_len.
    ///
    /// We enforce the first two using types, and the latter by using `payload.len()` and `payload_len`.
    /// This has the caveat that `payload_len` must be <= u32::MAX, so we return an error if that is
    /// not the case.
    pub fn sign(&self, payload: &[u8], signature: &mut [u8]) -> Result<(), slice::SigningError> {
        slice::Ed25519::sign(self.as_ref(), payload, signature)
    }
}
impl<'a> VerificationKeyRef<'a> {
    /// The hacl implementation requires that
    /// - the public key is a 32 byte buffer
    /// - the signature is a 64 byte buffer,
    /// - the payload buffer is not shorter than payload_len.
    ///
    /// We enforce the first two using types, and the latter by using `payload.len()` and `payload_len`.
    /// This has the caveat that `payload_len` must be <= u32::MAX, so we return an error if that is
    /// not the case.
    pub fn verify(&self, payload: &[u8], signature: &[u8]) -> Result<(), slice::VerificationError> {
        slice::Ed25519::verify(self.as_ref(), payload, signature)
    }
}

// key-centric API
impl SigningKey {
    /// The hacl implementation requires that
    /// - the private key is a 32 byte buffer
    /// - the signature is a 64 byte buffer,
    /// - the payload buffer is not shorter than payload_len.
    ///
    /// We enforce the first two using types, and the latter by using `payload.len()` and `payload_len`.
    /// This has the caveat that `payload_len` must be <= u32::MAX, so we return an error if that is
    /// not the case.
    pub fn sign(&self, payload: &[u8]) -> Result<Signature, arrayref::SigningError> {
        let mut signature = [0u8; SIGNATURE_LEN];
        arrayref::Ed25519::sign(self.as_ref(), payload, &mut signature)
            .map(|_| Signature::from(signature))
    }
}
impl VerificationKey {
    /// The hacl implementation requires that
    /// - the public key is a 32 byte buffer
    /// - the signature is a 64 byte buffer,
    /// - the payload buffer is not shorter than payload_len.
    ///
    /// We enforce the first two using types, and the latter by using `payload.len()` and `payload_len`.
    /// This has the caveat that `payload_len` must be <= u32::MAX, so we return an error if that is
    /// not the case.
    pub fn verify(
        &self,
        payload: &[u8],
        signature: &Signature,
    ) -> Result<(), arrayref::VerificationError> {
        arrayref::Ed25519::verify(self.as_ref(), payload, signature.as_ref())
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
    Ed25519::keygen(&mut signing_key, &mut verification_key, [0; 32]);

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

    let mut signing_key = [0u8; Ed25519::SIGNING_KEY_LEN];
    let mut verification_key = [0u8; Ed25519::VERIFICATION_KEY_LEN];
    Ed25519::keygen(&mut signing_key, &mut verification_key, [0; 32]);

    // arrayref API
    let mut signature = [0u8; Ed25519::SIGNATURE_LEN];
    Ed25519::sign(&signing_key, b"payload", &mut signature).unwrap();
    Ed25519::verify(&verification_key, b"payload", &signature).unwrap();
}
