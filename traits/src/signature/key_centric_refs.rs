//! Key-centric signature API with reference key types.
//!
//! This module provides a higher-level, key-centric interface for signature operations
//! using reference key wrapper types. It builds on the foundational `arrayref` and `owned` APIs
//! to provide a more ergonomic interface where keys are wrapped in type-safe structs.
//!
//! # Key Features
//! - Type-safe key wrappers that prevent mixing different algorithm keys
//! - Automatic length validation when constructing from byte slices
//! - Seamless integration with owned key types

pub use super::slice::{KeyGenError, SignError, VerifyError};
use libcrux_secrets::U8;

/// A reference wrapper for signing (private) keys.
///
/// This type holds a reference to signing key material and associates it with
/// a specific signature algorithm, providing type safety.
pub struct SigningKeyRef<'a, Algorithm> {
    key: &'a [U8],
    _marker: core::marker::PhantomData<Algorithm>,
}

/// Error type for key construction from byte slices.
///
/// Indicates that the provided byte slice has an incorrect length for the
/// expected key type.
#[derive(Debug)]
pub enum FromBytesError {
    /// The provided byte slice has an invalid length for this key type.
    InvalidLength,
}

impl<
        'a,
        const SIGNING_KEY_LEN: usize,
        const VERIFICATION_KEY_LEN: usize,
        const SIGNATURE_LEN: usize,
        const RAND_KEYGEN_LEN: usize,
        Algorithm: super::key_centric_owned::SignTypes<
                SigningKey = [U8; SIGNING_KEY_LEN],
                VerificationKey = [u8; VERIFICATION_KEY_LEN],
                Signature = [u8; SIGNATURE_LEN],
                KeyGenRandomness = [U8; RAND_KEYGEN_LEN],
            > + super::owned::Sign<
                SIGNING_KEY_LEN,
                VERIFICATION_KEY_LEN,
                SIGNATURE_LEN,
                RAND_KEYGEN_LEN,
            >,
    > SigningKeyRef<'a, Algorithm>
{
    /// Create a signing key reference from a byte slice.
    ///
    /// # Parameters
    /// - `key`: A byte slice containing the signing key material
    ///
    /// # Returns
    /// A new [`SigningKeyRef`] if the byte slice has the correct length,
    /// or [`FromBytesError::InvalidLength`] if the length is incorrect.
    ///
    /// # Security
    /// This function does not validate the key beyond the length.
    pub fn from_bytes(key: &'a [U8]) -> Result<Self, FromBytesError> {
        if key.len() != SIGNING_KEY_LEN {
            return Err(FromBytesError::InvalidLength);
        }

        Ok(Self {
            key,
            _marker: Default::default(),
        })
    }

    /// Sign a payload using this signing key reference.
    ///
    /// # Parameters
    /// - `payload`: The data to be signed
    /// - `aux`: Algorithm-specific auxiliary data required for signing
    ///
    /// # Returns
    /// The signature on success, or [`SignError`] if signing fails.
    pub fn sign(
        &self,
        payload: &[u8],
        aux: <Algorithm as super::key_centric_owned::SignTypes>::SignAux<'_>,
    ) -> Result<Algorithm::Signature, SignError> {
        let key: &[U8; SIGNING_KEY_LEN] = self
            .key
            .try_into()
            .map_err(|_| SignError::InvalidSigningKeyLength)?;

        Algorithm::sign(payload, key, aux).map_err(SignError::from)
    }
}

/// A reference wrapper for verification (public) keys.
///
/// This type holds a reference to verification key material and associates it with
/// a specific signature algorithm, providing type safety.
pub struct VerificationKeyRef<'a, Algorithm> {
    key: &'a [u8],
    _marker: core::marker::PhantomData<Algorithm>,
}

impl<
        'a,
        const SIGNING_KEY_LEN: usize,
        const VERIFICATION_KEY_LEN: usize,
        const SIGNATURE_LEN: usize,
        const RAND_KEYGEN_LEN: usize,
        Algorithm: super::key_centric_owned::SignTypes<
                SigningKey = [U8; SIGNING_KEY_LEN],
                VerificationKey = [u8; VERIFICATION_KEY_LEN],
                Signature = [u8; SIGNATURE_LEN],
                KeyGenRandomness = [U8; RAND_KEYGEN_LEN],
            > + super::owned::Sign<
                SIGNING_KEY_LEN,
                VERIFICATION_KEY_LEN,
                SIGNATURE_LEN,
                RAND_KEYGEN_LEN,
            >,
    > VerificationKeyRef<'a, Algorithm>
{
    /// Create a verification key reference from a byte slice.
    ///
    /// # Parameters
    /// - `key`: A byte slice containing the verification key material
    ///
    /// # Returns
    /// A new [`VerificationKeyRef`] if the byte slice has the correct length,
    /// or [`FromBytesError::InvalidLength`] if the length is incorrect.
    ///
    /// # Security
    /// This function does not validate the key beyond the length.
    pub fn from_bytes(key: &'a [u8]) -> Result<Self, FromBytesError> {
        if key.len() != VERIFICATION_KEY_LEN {
            return Err(FromBytesError::InvalidLength);
        }

        Ok(Self {
            key,
            _marker: Default::default(),
        })
    }
    /// Verify a signature using this verification key reference.
    ///
    /// # Parameters
    /// - `payload`: The original data that was signed
    /// - `signature`: The signature to verify
    ///
    /// # Returns
    /// `Ok(())` if the signature is valid, or [`VerifyError`] if verification fails.
    pub fn verify(
        &self,
        payload: &[u8],
        signature: &Algorithm::Signature,
    ) -> Result<(), VerifyError> {
        let key: &[u8; VERIFICATION_KEY_LEN] = self
            .key
            .try_into()
            .map_err(|_| VerifyError::InvalidVerificationKeyLength)?;

        Algorithm::verify(payload, key, signature).map_err(VerifyError::from)
    }
}
