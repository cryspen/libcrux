//! This module provides a trait for a generic signature primitive.
use crate::Error;

/// A generic signature primitive.
pub trait Credential {
    /// The credentials' signature objects.
    type Signature;
    /// The credentials' signing key objects.
    type SigningKey;
    /// The credentials' verification key objects.
    type VerificationKey;
    /// Length (in bytes) of a serialized verification key.
    const VK_LEN: usize;
    /// Length (in bytes) of a serialized signature.
    const SIG_LEN: usize;

    /// Return a signature, as well as the verification key needed to
    /// verify the signature.
    fn sign(
        signing_key: &Self::SigningKey,
        message: &[u8],
    ) -> Result<(Self::Signature, Self::VerificationKey), Error>;

    /// Verify a signature.
    fn verify(
        verification_key: &Self::VerificationKey,
        signature: &Self::Signature,
        message: &[u8],
    ) -> Result<(), Error>;

    /// Serialize a signature to bytes.
    fn serialize_signature(signature: &Self::Signature) -> Vec<u8>;

    /// Serialize a verification key to bytes.
    fn serialize_verification_key(verification_key: &Self::VerificationKey) -> Vec<u8>;

    /// Deserialize a verification key.
    fn deserialize_verification_key(bytes: &[u8]) -> Result<Self::VerificationKey, Error>;

    /// Deserialize a signature.
    fn deserialize_signature(bytes: &[u8]) -> Result<Self::Signature, Error>;
}

/// A no-op signature primitive that does nothing.
pub struct NoAuth {}

impl Credential for NoAuth {
    type Signature = ();
    type SigningKey = ();
    type VerificationKey = ();

    const VK_LEN: usize = 0;
    const SIG_LEN: usize = 0;

    fn sign(
        _signing_key: &Self::SigningKey,
        _message: &[u8],
    ) -> Result<(Self::Signature, Self::VerificationKey), Error> {
        Ok(((), ()))
    }

    fn verify(
        _verification_key: &Self::VerificationKey,
        _signature: &Self::Signature,
        _message: &[u8],
    ) -> Result<(), Error> {
        Ok(())
    }

    fn serialize_signature(_signature: &Self::Signature) -> Vec<u8> {
        Vec::new()
    }

    fn serialize_verification_key(_verification_key: &Self::VerificationKey) -> Vec<u8> {
        Vec::new()
    }

    fn deserialize_verification_key(_bytes: &[u8]) -> Result<Self::VerificationKey, Error> {
        Ok(())
    }

    fn deserialize_signature(_bytes: &[u8]) -> Result<Self::Signature, Error> {
        Ok(())
    }
}
