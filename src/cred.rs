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

/// A credential based on Ed25519 signatures.
pub struct Ed25519 {}

impl Credential for Ed25519 {
    type Signature = [u8; 64];

    type SigningKey = [u8; 32];

    type VerificationKey = [u8; 32];

    const VK_LEN: usize = 32;

    const SIG_LEN: usize = 64;

    fn sign(
        signing_key: &Self::SigningKey,
        message: &[u8],
    ) -> Result<(Self::Signature, Self::VerificationKey), Error> {
        let sig = libcrux_ed25519::sign(message, signing_key).map_err(|_| Error::CredError)?;
        let mut vk = [0u8; 32];
        libcrux_ed25519::secret_to_public(&mut vk, signing_key);
        Ok((sig, vk))
    }

    fn verify(
        verification_key: &Self::VerificationKey,
        signature: &Self::Signature,
        message: &[u8],
    ) -> Result<(), Error> {
        libcrux_ed25519::verify(message, verification_key, signature).map_err(|_| Error::CredError)
    }

    fn serialize_signature(signature: &Self::Signature) -> Vec<u8> {
        signature.to_vec()
    }

    fn serialize_verification_key(verification_key: &Self::VerificationKey) -> Vec<u8> {
        verification_key.to_vec()
    }

    /// CAUTION: This does not perform validation of the verification key.
    fn deserialize_verification_key(bytes: &[u8]) -> Result<Self::VerificationKey, Error> {
        bytes.try_into().map_err(|_| Error::CredError)
    }

    fn deserialize_signature(bytes: &[u8]) -> Result<Self::Signature, Error> {
        bytes.try_into().map_err(|_| Error::CredError)
    }
}
