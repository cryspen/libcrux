//! This module provides common interface traits and helper macros for signature scheme implementations.
//!
//! Instead of a fully trait-based API for signature operations, this crate provides traits and
//! macros that can be used to implement signature APIs with a given shape.
//!
//! ### Defining useful constants with the [`SignConsts`] trait
//!
//! Structs that implement the [`SignConsts`] trait allow retrieving useful constants for that
//! signature algorithm. These can be used as the lengths of new buffers representing the
//! signing key, verification key, signature, or the randomness input to keygen functions.
//!
//! Example:
//! ```rust
//! use libcrux_traits::signature::SignConsts;
//! use libcrux_signature::mldsa::ml_dsa_44::MlDsa44;
//!
//! // the length of the signing key in bytes.
//! assert_eq!(MlDsa44::SIGNING_KEY_LEN, 2560);
//!
//! // the length of the verification key in bytes.
//! assert_eq!(MlDsa44::VERIFICATION_KEY_LEN, 1312);
//!
//! // the length of the signature in bytes.
//! assert_eq!(MlDsa44::SIGNATURE_LEN, 2420);
//!
//! // the length of the rand_keygen buffer in bytes.
//! assert_eq!(MlDsa44::RAND_KEYGEN_LEN, 32);
//! ```
//!
//! ### Implementing key-centric APIs
//!
//! The [`impl_key_centric_types!()`] macro can be used to conveniently define types
//! used by key-centric signature APIs.
//! - `SigningKey`, `SigningKeyRef`: owned and borrowed signing keys.
//! - `VerificationKey`, `VerificationKeyRef`: owned and borrowed verification keys.
//! - `Signature`: an owned signature.
//! - `KeyPair`: an owned signature keypair (contains a `SigningKey` and a `VerificationKey`)
//!
//! Key-centric APIs can be defined on the above structs.
//! - `SigningKey::sign()`: The first argument should be the `payload`, followed by other
//! arguments. This API should return an owned `Signature`.
//! - `SigningKeyRef::sign()`: The first argument should be the `payload`, followed by a
//! `signature: &mut [u8]` representing the signature buffer to write into.
//! - `VerificationKey::verify()`: The first argument should be a slice representing the payload,
//! followed by a reference to a `Signature`.
//! - `VerificationKeyRef::verify()`: The first argument should be a slice representing the
//! payload, followed by a `signature: &[u8]` representing the signature.
//!
//!  ```rust
//! use libcrux_signature::ed25519::{
//!     Ed25519, KeyPair, SigningKey, VerificationKey, SigningKeyRef, VerificationKeyRef,
//! };
//! use libcrux_traits::signature::SignConsts;
//!
//! // generate a new signature keypair
//! use rand::TryRngCore;
//! let mut rng = rand::rngs::OsRng;
//! let KeyPair { signing_key, verification_key } = KeyPair::generate(&mut rng.unwrap_mut());
//!
//! // sign and verify
//! let signature = signing_key.sign(b"payload").unwrap();
//! verification_key.verify(b"payload", &signature).unwrap();
//!  ```

/// Constants defining the sizes of cryptographic elements for a signature algorithm.
pub trait SignConsts {
    /// Length of verification (public) keys in bytes.
    const VERIFICATION_KEY_LEN: usize;
    /// Length of signing (private) keys in bytes.
    const SIGNING_KEY_LEN: usize;
    /// Length of signatures in bytes.
    const SIGNATURE_LEN: usize;
    /// Length of randomness required for key generation in bytes.
    const RAND_KEYGEN_LEN: usize;
}

/// Helper macro for implementing the [`SignConsts`] trait.
#[macro_export]
macro_rules! impl_sign_consts {
    ($algorithm:ty, $signing_key_len:expr, $verification_key_len:expr, $signature_len:expr, $rand_keygen_len:expr) => {
        impl $crate::signature::SignConsts for $algorithm {
            const SIGNING_KEY_LEN: usize = $signing_key_len;
            const VERIFICATION_KEY_LEN: usize = $verification_key_len;
            const SIGNATURE_LEN: usize = $signature_len;
            const RAND_KEYGEN_LEN: usize = $rand_keygen_len;
        }
    };
}

pub use impl_sign_consts;

/// Helper macro for implementing types for key-centric APIs
#[macro_export]
macro_rules! impl_key_centric_types {
    ($algorithm:ty, $signing_key_len:expr, $verification_key_len:expr, $signature_len:expr, $rand_keygen_len:expr, $from_slice_error:ty, $from_slice_error_variant:expr) => {
        $crate::signature::impl_sign_consts!(
            $algorithm,
            $signing_key_len,
            $verification_key_len,
            $signature_len,
            $rand_keygen_len
        );

        // internal types
        type SigningKeyArray = [$crate::libcrux_secrets::U8; $signing_key_len];
        type VerificationKeyArray = [u8; $verification_key_len];
        type SignatureArray = [u8; $signature_len];

        /// A signing key. The bytes are borrowed.
        pub struct SigningKeyRef<'a> {
            key: &'a [$crate::libcrux_secrets::U8],
        }
        impl<'a> AsRef<[$crate::libcrux_secrets::U8]> for SigningKeyRef<'a> {
            fn as_ref(&self) -> &[$crate::libcrux_secrets::U8] {
                self.key.as_ref()
            }
        }
        impl<'a> AsRef<[u8]> for VerificationKeyRef<'a> {
            fn as_ref(&self) -> &[u8] {
                self.key.as_ref()
            }
        }

        /// A verification key. The bytes are borrowed.
        pub struct VerificationKeyRef<'a> {
            key: &'a [u8],
        }

        /// A signing key. The bytes are owned.
        pub struct SigningKey {
            key: SigningKeyArray,
        }

        /// A verification key. The bytes are owned.
        pub struct VerificationKey {
            key: VerificationKeyArray,
        }

        /// A signature.
        #[derive(Debug, PartialEq)]
        pub struct Signature {
            signature: SignatureArray,
        }

        /// A key pair, containing a [`SigningKey`] and a [`VerificationKey`].
        pub struct KeyPair {
            pub signing_key: SigningKey,
            pub verification_key: VerificationKey,
        }

        impl<'a> SigningKeyRef<'a> {
            /// Create a signing key from a byte slice.
            pub fn from_slice(
                key: &'a [$crate::libcrux_secrets::U8],
            ) -> Result<Self, $from_slice_error> {
                if key.len() != $signing_key_len {
                    return Err($from_slice_error_variant);
                } else {
                    return Ok(Self { key });
                }
            }
        }

        impl From<SigningKeyArray> for SigningKey {
            fn from(key: SigningKeyArray) -> Self {
                Self { key }
            }
        }

        impl AsRef<[$crate::libcrux_secrets::U8]> for SigningKey {
            fn as_ref(&self) -> &[$crate::libcrux_secrets::U8] {
                self.key.as_ref()
            }
        }
        impl AsRef<SigningKeyArray> for SigningKey {
            fn as_ref(&self) -> &SigningKeyArray {
                &self.key
            }
        }

        impl<'a> VerificationKeyRef<'a> {
            /// Create a verification key from a byte slice.
            pub fn from_slice(key: &'a [u8]) -> Result<Self, $from_slice_error> {
                if key.len() != $verification_key_len {
                    return Err($from_slice_error_variant);
                } else {
                    return Ok(Self { key });
                }
            }
        }
        impl From<VerificationKeyArray> for VerificationKey {
            fn from(key: VerificationKeyArray) -> Self {
                Self { key }
            }
        }
        impl AsRef<[u8]> for VerificationKey {
            fn as_ref(&self) -> &[u8] {
                self.key.as_ref()
            }
        }
        impl AsRef<VerificationKeyArray> for VerificationKey {
            fn as_ref(&self) -> &VerificationKeyArray {
                &self.key
            }
        }
        impl AsRef<[u8]> for Signature {
            fn as_ref(&self) -> &[u8] {
                self.signature.as_ref()
            }
        }
        impl AsRef<SignatureArray> for Signature {
            fn as_ref(&self) -> &SignatureArray {
                &self.signature
            }
        }
        impl From<SignatureArray> for Signature {
            fn from(signature: SignatureArray) -> Self {
                Self { signature }
            }
        }
    };
}

pub use impl_key_centric_types;
