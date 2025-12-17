use libcrux_traits::signature::{impl_key_centric_types, impl_sign_consts, SignConsts};

macro_rules! impl_mod {
    ($ty:ident, $module:ident) => {
        use libcrux_secrets::{Declassify, DeclassifyRef, DeclassifyRefMut, U8};

        pub(super) const VERIFICATION_KEY_LEN: usize =
            crate::ml_dsa_generic::$module::VERIFICATION_KEY_SIZE;
        pub(super) const SIGNING_KEY_LEN: usize = crate::ml_dsa_generic::$module::SIGNING_KEY_SIZE;
        pub(super) const SIGNATURE_LEN: usize = crate::ml_dsa_generic::$module::SIGNATURE_SIZE;
        pub(super) const RAND_KEYGEN_LEN: usize = 32;

        use super::*;

        #[doc(inline)]
        pub use arrayref::*;

        // TODO: different error type?
        #[derive(Debug)]
        /// An incorrect length when converting from slice.
        pub struct WrongLengthError;

        pub(crate) mod arrayref {
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
            //! Slice-based APIs for ML-DSA.
            //!
            //! Usage example:
            //! ```rust
            //! use libcrux_traits::signature::SignConsts;
            //! use libcrux_ml_dsa::key_centric_apis::ml_dsa_44::slice::MlDsa44;
            //!
            //! let context = b"context";
            //!
            //! let mut signing_key = [0u8; MlDsa44::SIGNING_KEY_LEN];
            //! let mut verification_key = [0u8; MlDsa44::VERIFICATION_KEY_LEN];
            //! MlDsa44::keygen(&mut signing_key, &mut verification_key, [0; 32]).unwrap();
            //!
            //! // slice API
            //! let mut signature = [0u8; MlDsa44::SIGNATURE_LEN];
            //! MlDsa44::sign(&signing_key, b"payload", &mut signature, context, [0u8; 32]).unwrap();
            //! MlDsa44::verify(&verification_key, b"payload", &signature, context).unwrap();
            //!
            //! MlDsa44::sign_pre_hashed_shake128(
            //!     signing_key.as_ref(),
            //!     b"payload",
            //!     &mut signature,
            //!     context,
            //!     [0u8; 32],
            //! )
            //! .unwrap();
            //! MlDsa44::verify_pre_hashed_shake128(
            //!     verification_key.as_ref(),
            //!     b"payload",
            //!     &signature,
            //!     context,
            //! )
            //! .unwrap();
            //! ```

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
                RejectionSamplingError,
                ContextTooLongError,
                WrongSigningKeyLength,
                WrongSignatureLength,
            }

            impl From<crate::SigningError> for SigningError {
                fn from(e: crate::SigningError) -> Self {
                    match e {
                        crate::SigningError::RejectionSamplingError => {
                            SigningError::RejectionSamplingError
                        }
                        crate::SigningError::ContextTooLongError => {
                            SigningError::ContextTooLongError
                        }
                    }
                }
            }

            // error type including wrong length
            #[derive(Debug)]
            pub enum VerificationError {
                MalformedHintError,
                SignerResponseExceedsBoundError,
                CommitmentHashesDontMatchError,
                VerificationContextTooLongError,
                WrongVerificationKeyLength,
                WrongSignatureLength,
            }

            impl From<crate::VerificationError> for VerificationError {
                fn from(e: crate::VerificationError) -> Self {
                    match e {
                        crate::VerificationError::MalformedHintError => {
                            VerificationError::MalformedHintError
                        }
                        crate::VerificationError::SignerResponseExceedsBoundError => {
                            VerificationError::SignerResponseExceedsBoundError
                        }
                        crate::VerificationError::CommitmentHashesDontMatchError => {
                            VerificationError::CommitmentHashesDontMatchError
                        }
                        crate::VerificationError::VerificationContextTooLongError => {
                            VerificationError::VerificationContextTooLongError
                        }
                    }
                }
            }

            #[derive(Debug)]
            pub enum KeygenError {
                WrongSigningKeyLength,
                WrongVerificationKeyLength,
            }
        }

        impl KeyPair {
            #[cfg(feature = "rand")]
            pub fn generate(rng: &mut impl rand::CryptoRng) -> KeyPair {
                use libcrux_secrets::Classify;

                let mut bytes = [0u8; arrayref::$ty::RAND_KEYGEN_LEN];
                rng.fill_bytes(&mut bytes);
                let mut signing_key = [0u8; arrayref::$ty::SIGNING_KEY_LEN].classify();
                let mut verification_key = [0u8; arrayref::$ty::VERIFICATION_KEY_LEN];
                arrayref::$ty::keygen(&mut signing_key, &mut verification_key, bytes.classify());

                KeyPair {
                    signing_key: SigningKey::from(signing_key),
                    verification_key: VerificationKey::from(verification_key),
                }
            }
        }
        impl arrayref::$ty {
            /// Generate an ML-DSA signature
            ///
            /// The parameter `context` is used for domain separation
            /// and is a byte string of length at most 255 bytes. It
            /// may also be empty.
            pub fn sign(
                key: &[U8; Self::SIGNING_KEY_LEN],
                payload: &[u8],
                signature: &mut [u8; Self::SIGNATURE_LEN],
                context: &[u8],
                randomness: [U8; 32],
            ) -> Result<(), crate::SigningError> {
                crate::ml_dsa_generic::multiplexing::$module::sign_mut(
                    // length is already validated
                    key.declassify_ref().try_into().unwrap(),
                    payload,
                    context,
                    randomness.declassify(),
                    signature,
                )
            }
            /// Generate a HashML-DSA Signature, with a SHAKE128 pre-hashing
            ///
            /// The parameter `context` is used for domain separation
            /// and is a byte string of length at most 255 bytes. It
            /// may also be empty.
            pub fn sign_pre_hashed_shake128(
                key: &[U8; Self::SIGNING_KEY_LEN],
                payload: &[u8],
                signature: &mut [u8; Self::SIGNATURE_LEN],
                context: &[u8],
                randomness: [U8; 32],
            ) -> Result<(), crate::SigningError> {
                // TODO: use mut version
                let mut pre_hash_buffer = [0; 32];
                let signature_out =
                    crate::ml_dsa_generic::multiplexing::$module::sign_pre_hashed_shake128(
                        key.declassify_ref().try_into().unwrap(),
                        payload,
                        context,
                        &mut pre_hash_buffer,
                        randomness.declassify(),
                    )?;

                signature.copy_from_slice(signature_out.as_slice());

                Ok(())
            }

            /// Verify an ML-DSA Signature
            ///
            /// The parameter `context` is used for domain separation
            /// and is a byte string of length at most 255 bytes. It
            /// may also be empty.
            pub fn verify(
                key: &[u8; Self::VERIFICATION_KEY_LEN],
                payload: &[u8],
                signature: &[u8; Self::SIGNATURE_LEN],
                context: &[u8],
            ) -> Result<(), crate::VerificationError> {
                crate::ml_dsa_generic::multiplexing::$module::verify(
                    key, payload, context, signature,
                )
            }

            /// Verify an ML-DSA Signature, with a SHAKE128 pre-hashing
            ///
            /// The parameter `context` is used for domain separation
            /// and is a byte string of length at most 255 bytes. It
            /// may also be empty.
            pub fn verify_pre_hashed_shake128(
                key: &[u8; Self::VERIFICATION_KEY_LEN],
                payload: &[u8],
                signature: &[u8; Self::SIGNATURE_LEN],
                context: &[u8],
            ) -> Result<(), crate::VerificationError> {
                let mut pre_hash_buffer = [0; 32];
                crate::ml_dsa_generic::multiplexing::$module::verify_pre_hashed_shake128(
                    key,
                    payload,
                    context,
                    &mut pre_hash_buffer,
                    signature,
                )
            }
            /// Generate an ML-DSA Key Pair
            pub fn keygen(
                signing_key: &mut [U8; Self::SIGNING_KEY_LEN],
                verification_key: &mut [u8; Self::VERIFICATION_KEY_LEN],
                randomness: [U8; Self::RAND_KEYGEN_LEN],
            ) {
                crate::ml_dsa_generic::multiplexing::$module::generate_key_pair(
                    randomness.declassify(),
                    signing_key.declassify_ref_mut(),
                    verification_key,
                );
            }
        }
        impl slice::$ty {
            /// Generate an ML-DSA signature
            ///
            /// The parameter `context` is used for domain separation
            /// and is a byte string of length at most 255 bytes. It
            /// may also be empty.
            pub fn sign(
                key: &[U8],
                payload: &[u8],
                signature: &mut [u8],
                context: &[u8],
                randomness: [U8; 32],
            ) -> Result<(), slice::SigningError> {
                let key = key
                    .try_into()
                    .map_err(|_| slice::SigningError::WrongSigningKeyLength)?;
                let signature = signature
                    .try_into()
                    .map_err(|_| slice::SigningError::WrongSignatureLength)?;

                arrayref::$ty::sign(&key, payload, signature, context, randomness)
                    .map_err(slice::SigningError::from)
            }

            /// Generate a HashML-DSA Signature, with a SHAKE128 pre-hashing
            ///
            /// The parameter `context` is used for domain separation
            /// and is a byte string of length at most 255 bytes. It
            /// may also be empty.
            pub fn sign_pre_hashed_shake128(
                key: &[U8],
                payload: &[u8],
                signature: &mut [u8],
                context: &[u8],
                randomness: [U8; 32],
            ) -> Result<(), slice::SigningError> {
                let key = key
                    .try_into()
                    .map_err(|_| slice::SigningError::WrongSigningKeyLength)?;
                let signature = signature
                    .try_into()
                    .map_err(|_| slice::SigningError::WrongSignatureLength)?;

                arrayref::$ty::sign_pre_hashed_shake128(
                    &key, payload, signature, context, randomness,
                )
                .map_err(slice::SigningError::from)
            }

            /// Verify an ML-DSA Signature
            ///
            /// The parameter `context` is used for domain separation
            /// and is a byte string of length at most 255 bytes. It
            /// may also be empty.
            pub fn verify(
                key: &[u8],
                payload: &[u8],
                signature: &[u8],
                context: &[u8],
            ) -> Result<(), slice::VerificationError> {
                let key = key
                    .try_into()
                    .map_err(|_| slice::VerificationError::WrongVerificationKeyLength)?;
                let signature = signature
                    .try_into()
                    .map_err(|_| slice::VerificationError::WrongSignatureLength)?;

                arrayref::$ty::verify(key, payload, signature, context)
                    .map_err(slice::VerificationError::from)
            }

            /// Verify an ML-DSA Signature, with a SHAKE128 pre-hashing
            ///
            /// The parameter `context` is used for domain separation
            /// and is a byte string of length at most 255 bytes. It
            /// may also be empty.
            pub fn verify_pre_hashed_shake128(
                key: &[u8],
                payload: &[u8],
                signature: &[u8],
                context: &[u8],
            ) -> Result<(), slice::VerificationError> {
                let key = key
                    .try_into()
                    .map_err(|_| slice::VerificationError::WrongVerificationKeyLength)?;
                let signature = signature
                    .try_into()
                    .map_err(|_| slice::VerificationError::WrongSignatureLength)?;

                arrayref::$ty::verify_pre_hashed_shake128(key, payload, signature, context)
                    .map_err(slice::VerificationError::from)
            }

            /// Generate an ML-DSA Key Pair
            #[cfg(not(eurydice))]
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

                arrayref::$ty::keygen(signing_key, verification_key, randomness);

                Ok(())
            }
        }
        impl<'a> SigningKeyRef<'a> {
            /// Generate an ML-DSA signature
            ///
            /// The parameter `context` is used for domain separation
            /// and is a byte string of length at most 255 bytes. It
            /// may also be empty.
            pub fn sign(
                &self,
                payload: &[u8],
                signature: &mut [u8],
                context: &[u8],
                randomness: [U8; 32],
            ) -> Result<(), slice::SigningError> {
                slice::$ty::sign(self.as_ref(), payload, signature, context, randomness)
            }

            /// Generate a HashML-DSA Signature, with a SHAKE128 pre-hashing
            ///
            /// The parameter `context` is used for domain separation
            /// and is a byte string of length at most 255 bytes. It
            /// may also be empty.
            pub fn sign_pre_hashed_shake128(
                &self,
                payload: &[u8],
                signature: &mut [u8],
                context: &[u8],
                randomness: [U8; 32],
            ) -> Result<(), slice::SigningError> {
                slice::$ty::sign_pre_hashed_shake128(
                    self.as_ref(),
                    payload,
                    signature,
                    context,
                    randomness,
                )
            }
        }
        impl<'a> VerificationKeyRef<'a> {
            /// Verify an ML-DSA Signature
            ///
            /// The parameter `context` is used for domain separation
            /// and is a byte string of length at most 255 bytes. It
            /// may also be empty.
            pub fn verify(
                &self,
                payload: &[u8],
                signature: &[u8],
                context: &[u8],
            ) -> Result<(), slice::VerificationError> {
                slice::$ty::verify(self.as_ref(), payload, signature, context)
            }

            /// Verify an ML-DSA Signature, with a SHAKE128 pre-hashing
            ///
            /// The parameter `context` is used for domain separation
            /// and is a byte string of length at most 255 bytes. It
            /// may also be empty.
            pub fn verify_pre_hashed_shake128(
                &self,
                payload: &[u8],
                signature: &[u8],
                context: &[u8],
            ) -> Result<(), slice::VerificationError> {
                slice::$ty::verify_pre_hashed_shake128(self.as_ref(), payload, signature, context)
            }
        }

        // key-centric API
        impl SigningKey {
            /// Generate an ML-DSA signature
            ///
            /// The parameter `context` is used for domain separation
            /// and is a byte string of length at most 255 bytes. It
            /// may also be empty.
            pub fn sign(
                &self,
                payload: &[u8],
                context: &[u8],
                randomness: [U8; 32],
            ) -> Result<Signature, crate::SigningError> {
                let mut signature = [0u8; SIGNATURE_LEN];
                arrayref::$ty::sign(self.as_ref(), payload, &mut signature, context, randomness)
                    .map(|_| Signature::from(signature))
            }

            /// Generate a HashML-DSA Signature, with a SHAKE128 pre-hashing
            ///
            /// The parameter `context` is used for domain separation
            /// and is a byte string of length at most 255 bytes. It
            /// may also be empty.
            pub fn sign_pre_hashed_shake128(
                &self,
                payload: &[u8],
                context: &[u8],
                randomness: [U8; 32],
            ) -> Result<Signature, crate::SigningError> {
                let mut signature = [0u8; SIGNATURE_LEN];
                arrayref::$ty::sign_pre_hashed_shake128(
                    self.as_ref(),
                    payload,
                    &mut signature,
                    context,
                    randomness,
                )
                .map(|_| Signature::from(signature))
            }
        }
        impl VerificationKey {
            /// Verify an ML-DSA Signature
            ///
            /// The parameter `context` is used for domain separation
            /// and is a byte string of length at most 255 bytes. It
            /// may also be empty.
            pub fn verify(
                &self,
                payload: &[u8],
                signature: &Signature,
                context: &[u8],
            ) -> Result<(), crate::VerificationError> {
                arrayref::$ty::verify(self.as_ref(), payload, signature.as_ref(), context)
            }

            /// Verify an ML-DSA Signature, with a SHAKE128 pre-hashing
            ///
            /// The parameter `context` is used for domain separation
            /// and is a byte string of length at most 255 bytes. It
            /// may also be empty.
            pub fn verify_pre_hashed_shake128(
                &self,
                payload: &[u8],
                signature: &Signature,
                context: &[u8],
            ) -> Result<(), crate::VerificationError> {
                arrayref::$ty::verify_pre_hashed_shake128(
                    self.as_ref(),
                    payload,
                    signature.as_ref(),
                    context,
                )
            }
        }
    };
}

#[cfg(feature = "mldsa44")]
pub mod ml_dsa_44 {
    impl_mod!(MlDsa44, ml_dsa_44);
}

#[cfg(feature = "mldsa65")]
pub mod ml_dsa_65 {
    impl_mod!(MlDsa65, ml_dsa_65);
}

#[cfg(feature = "mldsa87")]
pub mod ml_dsa_87 {
    impl_mod!(MlDsa87, ml_dsa_87);
}

#[test]
#[cfg(all(
    feature = "mldsa44",
    feature = "rand",
    not(feature = "expose-secret-independence")
))]
fn key_centric_owned() {
    use rand::TryRngCore;
    let mut rng = rand::rngs::OsRng;
    let mut rng = rng.unwrap_mut();
    use libcrux_traits::signature::SignConsts;

    use ml_dsa_44::{KeyPair, MlDsa44, SigningKey, VerificationKey};

    let context = b"context";

    // keys can be created from arrays
    let _signing_key = SigningKey::from([0u8; MlDsa44::SIGNING_KEY_LEN]);
    let _verification_key = VerificationKey::from([0u8; MlDsa44::VERIFICATION_KEY_LEN]);

    // key-centric API
    let KeyPair {
        signing_key,
        verification_key,
    } = KeyPair::generate(&mut rng);

    let signature = signing_key.sign(b"payload", context, [0u8; 32]).unwrap();
    verification_key
        .verify(b"payload", &signature, context)
        .unwrap();

    let pre_hashed = b"pre-hashed";

    let signature_from_pre_hashed = signing_key
        .sign_pre_hashed_shake128(pre_hashed, context, [0u8; 32])
        .unwrap();
    verification_key
        .verify_pre_hashed_shake128(pre_hashed, &signature_from_pre_hashed, context)
        .unwrap();
}

#[test]
#[cfg(all(
    feature = "mldsa44",
    feature = "rand",
    not(feature = "expose-secret-independence")
))]
fn key_centric_refs() {
    use libcrux_traits::signature::SignConsts;
    use ml_dsa_44::*;

    let context = b"context";

    let mut signing_key = [0u8; MlDsa44::SIGNING_KEY_LEN];
    let mut verification_key = [0u8; MlDsa44::VERIFICATION_KEY_LEN];
    MlDsa44::keygen(&mut signing_key, &mut verification_key, [0; 32]);

    // create references from slice
    let signing_key = SigningKeyRef::from_slice(&signing_key).unwrap();
    let verification_key = VerificationKeyRef::from_slice(&verification_key).unwrap();

    let mut signature = [0u8; MlDsa44::SIGNATURE_LEN];
    signing_key
        .sign(b"payload", &mut signature, context, [0u8; 32])
        .unwrap();
    verification_key
        .verify(b"payload", &signature, context)
        .unwrap();

    signing_key
        .sign_pre_hashed_shake128(b"payload", &mut signature, context, [0u8; 32])
        .unwrap();
    verification_key
        .verify_pre_hashed_shake128(b"payload", &signature, context)
        .unwrap();
}

#[test]
#[cfg(all(feature = "mldsa44", not(feature = "expose-secret-independence")))]
fn arrayref_apis() {
    use libcrux_traits::signature::SignConsts;
    use ml_dsa_44::MlDsa44;

    let context = b"context";

    let mut signing_key = [0u8; MlDsa44::SIGNING_KEY_LEN];
    let mut verification_key = [0u8; MlDsa44::VERIFICATION_KEY_LEN];
    MlDsa44::keygen(&mut signing_key, &mut verification_key, [0; 32]);

    // arrayref API
    let mut signature = [0u8; MlDsa44::SIGNATURE_LEN];
    MlDsa44::sign(&signing_key, b"payload", &mut signature, context, [0u8; 32]).unwrap();
    MlDsa44::verify(&verification_key, b"payload", &signature, context).unwrap();

    // pre-hashed
    MlDsa44::sign_pre_hashed_shake128(&signing_key, b"payload", &mut signature, context, [0u8; 32])
        .unwrap();
    MlDsa44::verify_pre_hashed_shake128(&verification_key, b"payload", &signature, context)
        .unwrap();
}
