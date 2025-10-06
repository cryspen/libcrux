//! Value-returning signature API.
//!
//! This module provides a signature API that returns values instead of writing to mutable
//! output parameters. It builds on the foundational `arrayref` API to provide a more
//! ergonomic interface for applications that prefer functional-style APIs.
//!
//! # Key Features
//! - Functions return values instead of writing to output parameters
//! - Built-in convenience methods for key generation with RNG integration
//! - Automatic blanket implementation for any `arrayref::Sign` implementer
//! - Zero-allocation operation through compile-time array sizes

pub use super::arrayref::{KeyGenError, SignError, VerifyError};
use super::key_centric_owned::SignTypes;
use libcrux_secrets::{ClassifyRef, U8};

/// Signature trait that returns values instead of writing to output parameters.
///
/// This trait provides a functional-style interface for signature operations where
/// functions return their results as values rather than writing to mutable references.
/// This can be more ergonomic for many use cases.
///
/// # Type Parameters
/// - `SIGNING_KEY_LEN`: Length of signing (private) keys in bytes
/// - `VERIFICATION_KEY_LEN`: Length of verification (public) keys in bytes
/// - `SIGNATURE_LEN`: Length of signatures in bytes
/// - `RAND_KEYGEN_LEN`: Length of randomness required for key generation
///
/// # Associated Types
/// The `SignAux` type represents auxiliary information required for signing operations.
pub trait Sign<
    const SIGNING_KEY_LEN: usize,
    const VERIFICATION_KEY_LEN: usize,
    const SIGNATURE_LEN: usize,
    const RAND_KEYGEN_LEN: usize,
>:
    Sized
    + SignTypes<
        SigningKey = [U8; SIGNING_KEY_LEN],
        VerificationKey = [u8; VERIFICATION_KEY_LEN],
        Signature = [u8; SIGNATURE_LEN],
        KeyGenRandomness = [U8; RAND_KEYGEN_LEN],
    >
{
    /// Sign a payload using the provided signing key.
    ///
    /// # Parameters
    /// - `payload`: The data to be signed
    /// - `signing_key`: The private key for signing (secured with `U8`)
    /// - `aux`: Algorithm-specific auxiliary data required for signing
    ///
    /// # Returns
    /// The signature as an array on success, or [`SignError`] if signing fails.
    fn sign(
        payload: &[u8],
        signing_key: &[U8; SIGNING_KEY_LEN],
        aux: Self::SignAux<'_>,
    ) -> Result<[u8; SIGNATURE_LEN], SignError>;

    /// Verify a signature using the provided verification key.
    ///
    /// # Parameters
    /// - `payload`: The original data that was signed
    /// - `verification_key`: The public key for verification
    /// - `signature`: The signature to verify
    ///
    /// # Returns
    /// `Ok(())` if the signature is valid, or [`VerifyError`] if verification fails.
    fn verify(
        payload: &[u8],
        verification_key: &[u8; VERIFICATION_KEY_LEN],
        signature: &[u8; SIGNATURE_LEN],
    ) -> Result<(), VerifyError>;

    /// Generate a pair of signing and verification keys.
    ///
    /// # Parameters
    /// - `rand`: Cryptographically secure randomness for key generation
    ///
    /// # Returns
    /// A tuple of `(signing_key, verification_key)` on success, or [`KeyGenError`] if generation fails.
    ///
    /// # Security
    /// It is the caller's responsibility to ensure that the `rand` argument contains
    /// cryptographically secure random data.
    fn keygen_derand(
        rand: &[U8; RAND_KEYGEN_LEN],
    ) -> Result<([U8; SIGNING_KEY_LEN], [u8; VERIFICATION_KEY_LEN]), KeyGenError>;

    /// Generate a pair of signing and verification keys.
    ///
    /// # Parameters
    /// - `rng`: A cryptographic random number generator
    ///
    /// # Returns
    /// A tuple of `(signing_key, verification_key)` on success, or [`KeyGenError`] if generation fails.
    fn keygen(
        rng: &mut impl rand::CryptoRng,
    ) -> Result<([U8; SIGNING_KEY_LEN], [u8; VERIFICATION_KEY_LEN]), KeyGenError> {
        let mut rand = [0u8; RAND_KEYGEN_LEN];
        rng.fill_bytes(&mut rand);
        Self::keygen_derand(rand.classify_ref())
    }
}

impl<
        const SIGNING_KEY_LEN: usize,
        const VERIFICATION_KEY_LEN: usize,
        const SIGNATURE_LEN: usize,
        const RAND_KEYGEN_LEN: usize,
        T: super::arrayref::Sign<
                SIGNING_KEY_LEN,
                VERIFICATION_KEY_LEN,
                SIGNATURE_LEN,
                RAND_KEYGEN_LEN,
            > + SignTypes<
                SigningKey = [U8; SIGNING_KEY_LEN],
                VerificationKey = [u8; VERIFICATION_KEY_LEN],
                Signature = [u8; SIGNATURE_LEN],
                KeyGenRandomness = [U8; RAND_KEYGEN_LEN],
            >,
    > Sign<SIGNING_KEY_LEN, VERIFICATION_KEY_LEN, SIGNATURE_LEN, RAND_KEYGEN_LEN> for T
{
    fn sign(
        payload: &[u8],
        signing_key: &[U8; SIGNING_KEY_LEN],
        aux: Self::SignAux<'_>,
    ) -> Result<[u8; SIGNATURE_LEN], SignError> {
        let mut signature = [0; SIGNATURE_LEN];
        T::sign(payload, signing_key, &mut signature, aux).map(|_| signature)
    }

    fn verify(
        payload: &[u8],
        verification_key: &[u8; VERIFICATION_KEY_LEN],
        signature: &[u8; SIGNATURE_LEN],
    ) -> Result<(), VerifyError> {
        T::verify(payload, verification_key, signature)
    }
    fn keygen_derand(
        randomness: &[U8; RAND_KEYGEN_LEN],
    ) -> Result<([U8; SIGNING_KEY_LEN], [u8; VERIFICATION_KEY_LEN]), KeyGenError> {
        use libcrux_secrets::Classify;

        let mut signing_key = [0; SIGNING_KEY_LEN].classify();
        let mut verification_key = [0; VERIFICATION_KEY_LEN];
        T::keygen_derand(&mut signing_key, &mut verification_key, randomness)
            .map(|_| (signing_key, verification_key))
    }
}
