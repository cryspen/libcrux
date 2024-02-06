//! # HPKE Errors
//!
//! The high-level, public HPKE APIs specified in this document are all fallible.
//! These include the Setup functions and all encryption context functions.
//! For example, `Decap()` can fail if the encapsulated key `enc` is invalid,
//! and `Open()` may fail if ciphertext decryption fails. The explicit errors
//! generated throughout this specification, along with the conditions that
//! lead to each error, are as follows:
//!
//! - `ValidationError`: KEM input or output validation failure.
//! - `DeserializeError`: Public or private key deserialization failure.
//! - `EncapError`: `Encap()` failure.
//! - `DecapError`: `Decap()` failure.
//! - `OpenError`: Context AEAD `Open()` failure.
//! - `MessageLimitReachedError`: Context AEAD sequence number overflow.
//! - `DeriveKeyPairError`: Key pair derivation failure.
//!
//! Implicit errors may also occur. As an example, certain classes of failures,
//! e.g., malformed recipient public keys, may not yield explicit errors.
//! For example, for the DHKEM variant described in this specification,
//! the `Encap()` algorithm fails when given an invalid recipient public key.
//! However, other KEM algorithms may not have an efficient algorithm for verifying
//! the validity of public keys. As a result, an equivalent error may not manifest
//! until AEAD decryption at the recipient. As another example, DHKEM's `AuthDecap()`
//! function will produce invalid output if given the wrong sender public key.
//! This error is not detectable until subsequent AEAD decryption.
//!
//! The errors in this document are meant as a guide for implementors. They are not
//! an exhaustive list of all the errors an implementation might emit. For example,
//! future KEMs might have internal failure cases, or an implementation might run
//! out of memory.
//!
//! How these errors are expressed in an API or handled by applications is an
//! implementation-specific detail. For example, some implementations may abort or
//! panic upon a `DeriveKeyPairError` failure given that it only occurs with
//! negligible probability, whereas other implementations may retry the failed
//! DeriveKeyPair operation.
//! As another example, some implementations of the DHKEM specified in this document
//! may choose to transform `ValidationError` from `DH()` into an `EncapError` or
//! `DecapError` from `Encap()` or `Decap()`, respectively, whereas others may choose
//! to raise `ValidationError` unmodified.
//!
//! Applications using HPKE APIs should not assume that the errors here are complete,
//! nor should they assume certain classes of errors will always manifest the same way
//! for all ciphersuites. For example, the DHKEM specified in this document will emit
//! a `DeserializationError` or `ValidationError` if a KEM public key is invalid. However,
//! a new KEM might not have an efficient algorithm for determining whether or not a
//! public key is valid. In this case, an invalid public key might instead yield an
//! `OpenError` when trying to decrypt a ciphertext.
//!
//! ## Exceptions
//! The exceptions raised in the HPKE RFC are modelled as errors here as well:
//!
//! - `InconsistentPskInputs`: PSK inputs are inconsistent.
//! - `UnnecessaryPsk`: PSK input provided when not needed.
//! - `MissingPsk`: Missing required PSK input.
//!
//! ## hacspec Extensions
//! In order to implement HPKE a number of additional errors are added here:
//!
//! - `UnsupportedAlgorithm`: An algorithm is not supported by the implementation
//! - `InvalidParameters`: Parameters to an algorithm are inconsistent or wrong.
//! - `CryptoError`: An opaque error happened in a crypto operation outside of this code.

use crate::aead::InvalidArgumentError;

/// Explicit errors generated throughout this specification.
#[derive(Debug, Copy, Clone, PartialEq)]
pub enum HpkeError {
    /// KEM input or output validation failure.
    ValidationError,
    /// Public or private key deserialization failure.
    DeserializeError,
    /// `Encap()` failure.
    EncapError,
    /// `Decap()` failure.
    DecapError,
    /// Context AEAD `Open()` failure.
    OpenError,
    /// Context AEAD sequence number overflow.
    MessageLimitReachedError,
    /// Key pair derivation failure.
    DeriveKeyPairError,

    /// PSK inputs are inconsistent.
    InconsistentPskInputs,
    /// PSK input provided when not needed.
    UnnecessaryPsk,
    /// Missing required PSK input.
    MissingPsk,

    /// An algorithm is not supported by the implementation.
    UnsupportedAlgorithm,
    /// Parameters to an algorithm are inconsistent or wrong.
    InvalidParameters,
    /// An opaque error happened in a crypto operation outside of this code.
    CryptoError,
}

/// A [`Result`] type that returns a [`Bytes`] or an [`HpkeError`].
pub type HpkeBytesResult = Result<Vec<u8>, HpkeError>;

impl From<crate::aead::EncryptError> for HpkeError {
    fn from(value: crate::aead::EncryptError) -> Self {
        match value {
            crate::aead::EncryptError::InternalError => Self::CryptoError,
            crate::aead::EncryptError::InvalidArgument(
                InvalidArgumentError::UnsupportedAlgorithm,
            ) => Self::UnsupportedAlgorithm,
            crate::aead::EncryptError::InvalidArgument(_) => Self::InvalidParameters,
        }
    }
}

impl From<crate::aead::DecryptError> for HpkeError {
    fn from(value: crate::aead::DecryptError) -> Self {
        match value {
            crate::aead::DecryptError::InvalidArgument(
                InvalidArgumentError::UnsupportedAlgorithm,
            ) => Self::UnsupportedAlgorithm,

            crate::aead::DecryptError::InvalidArgument(_) => Self::CryptoError,
            crate::aead::DecryptError::InternalError => Self::CryptoError,
            crate::aead::DecryptError::DecryptionFailed => Self::OpenError,
        }
    }
}

impl From<crate::aead::InvalidArgumentError> for HpkeError {
    fn from(err: crate::aead::InvalidArgumentError) -> Self {
        match err {
            InvalidArgumentError::UnsupportedAlgorithm => Self::UnsupportedAlgorithm,
            _ => Self::InvalidParameters,
        }
    }
}
