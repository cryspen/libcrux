//! This module provides common interface traits for signature scheme implementations.

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

/// Associated types for signature algorithm components.
///
/// This trait defines the concrete types used by a signature algorithm for keys,
/// signatures, randomness, and auxiliary signing data.
pub trait SignTypes {
    /// The type representing signing (private) keys.
    type SigningKey;
    /// The type representing verification (public) keys.
    type VerificationKey;
    /// The type representing signatures.
    type Signature;
}

/// Helper macro for implementing signing-related traits
#[macro_export]
macro_rules! impl_sign_traits {
    ($algorithm:ty, $signing_key_len:expr, $verification_key_len:expr, $signature_len:expr, $rand_keygen_len:expr) => {
        use $crate::libcrux_secrets::U8;
        impl $crate::signature::SignConsts for $algorithm {
            const SIGNING_KEY_LEN: usize = $signing_key_len;
            const VERIFICATION_KEY_LEN: usize = $verification_key_len;
            const SIGNATURE_LEN: usize = $signature_len;
            const RAND_KEYGEN_LEN: usize = $rand_keygen_len;
        }

        // internal types
        type SigningKeyArray = [U8; $signing_key_len];
        type VerificationKeyArray = [u8; $verification_key_len];
        type SignatureArray = [u8; $signature_len];

        impl $crate::signature::SignTypes for $algorithm {
            type SigningKey = SigningKeyArray;
            type VerificationKey = VerificationKeyArray;
            type Signature = SignatureArray;
        }
    };
}

pub use impl_sign_traits;

/// Helper macro for implementing types for key-centric APIs
#[macro_export]
macro_rules! impl_key_centric_types {
    ($algorithm:ty, $signing_key_len:expr, $verification_key_len:expr, $signature_len:expr, $rand_keygen_len:expr, $from_slice_error:ty, $from_slice_error_variant:expr) => {
        impl_sign_traits!(
            $algorithm,
            $signing_key_len,
            $verification_key_len,
            $signature_len,
            $rand_keygen_len
        );

        pub struct SigningKeyRef<'a> {
            key: &'a [U8],
        }
        impl<'a> AsRef<[U8]> for SigningKeyRef<'a> {
            fn as_ref(&self) -> &[U8] {
                self.key.as_ref()
            }
        }
        impl<'a> AsRef<[u8]> for VerificationKeyRef<'a> {
            fn as_ref(&self) -> &[u8] {
                self.key.as_ref()
            }
        }
        pub struct VerificationKeyRef<'a> {
            key: &'a [u8],
        }

        pub struct SigningKey {
            key: SigningKeyArray,
        }
        pub struct VerificationKey {
            key: VerificationKeyArray,
        }
        #[derive(Debug, PartialEq)]
        pub struct Signature {
            signature: SignatureArray,
        }

        pub struct KeyPair {
            pub signing_key: SigningKey,
            pub verification_key: VerificationKey,
        }

        impl<'a> SigningKeyRef<'a> {
            pub fn from_slice(key: &'a [U8]) -> Result<Self, $from_slice_error> {
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

        impl AsRef<[U8]> for SigningKey {
            fn as_ref(&self) -> &[U8] {
                self.key.as_ref()
            }
        }
        impl AsRef<SigningKeyArray> for SigningKey {
            fn as_ref(&self) -> &SigningKeyArray {
                &self.key
            }
        }
        impl<'a> VerificationKeyRef<'a> {
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
