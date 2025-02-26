//! This module provides a trait for a generic authenticator.
use crate::Error;

/// A generic authentication primitive.
///
/// The authenticator can be used to create and verify signatures
/// under some identity. Given a signature and a credential, the
/// signature can be verified as being done under some identity, if
/// the credential has a matching certificate, which ties it to that
/// identity.
pub trait Authenticator {
    /// The authenticator's signature objects.
    type Signature: AsRef<[u8]>;
    /// The authenticator's signing key objects.
    type SigningKey;
    /// The authenticator's verification key objects.
    type VerificationKey;
    /// The client's credential.
    type Credential: AsRef<[u8]>;
    /// Information necessary to validate the credential.
    type Certificate;
    /// Length (in bytes) of a serialized credential key.
    const CRED_LEN: usize;
    /// Length (in bytes) of a serialized signature.
    const SIG_LEN: usize;

    /// Return a signature
    fn sign(signing_key: &Self::SigningKey, message: &[u8]) -> Result<Self::Signature, Error>;

    /// Retrieve the client verification key from a valid credential.
    fn validate_credential(
        credential: Self::Credential,
        certificate: &Self::Certificate,
    ) -> Result<Self::VerificationKey, Error>;

    /// Verify a signature.
    fn verify(
        verification_key: &Self::VerificationKey,
        signature: &Self::Signature,
        message: &[u8],
    ) -> Result<(), Error>;

    /// Deserialize a verification key.
    fn deserialize_credential(bytes: &[u8]) -> Result<Self::Credential, Error>;

    /// Deserialize a signature.
    fn deserialize_signature(bytes: &[u8]) -> Result<Self::Signature, Error>;
}

/// A no-op authenticator that does nothing.
pub struct NoAuth {}

impl Authenticator for NoAuth {
    type Signature = [u8; 0];
    type SigningKey = [u8; 0];
    type VerificationKey = [u8; 0];
    type Credential = [u8; 0];
    type Certificate = [u8; 0];

    const CRED_LEN: usize = 0;
    const SIG_LEN: usize = 0;

    fn sign(_signing_key: &Self::SigningKey, _message: &[u8]) -> Result<Self::Signature, Error> {
        Ok([0; 0])
    }

    fn verify(
        _verification_key: &Self::VerificationKey,
        _signature: &Self::Signature,
        _message: &[u8],
    ) -> Result<(), Error> {
        Ok(())
    }

    fn deserialize_credential(_bytes: &[u8]) -> Result<Self::VerificationKey, Error> {
        Ok([0; 0])
    }

    fn deserialize_signature(_bytes: &[u8]) -> Result<Self::Signature, Error> {
        Ok([0; 0])
    }

    fn validate_credential(
        _credential: Self::Credential,
        _certificate: &Self::Certificate,
    ) -> Result<Self::VerificationKey, Error> {
        Ok([0; 0])
    }
}

/// A simple authenticator based on Ed25519 signatures, where it is
/// assumed that the responder obtains the initiators verification key
/// out of band and the verification key itself serves as the
/// certificate.
pub struct Ed25519 {}

impl Authenticator for Ed25519 {
    type Signature = [u8; 64];

    type SigningKey = [u8; 32];

    type VerificationKey = [u8; 32];

    type Credential = Self::VerificationKey;

    type Certificate = Self::VerificationKey;

    const CRED_LEN: usize = 32;

    const SIG_LEN: usize = 64;

    fn sign(signing_key: &Self::SigningKey, message: &[u8]) -> Result<Self::Signature, Error> {
        libcrux_ed25519::sign(message, signing_key).map_err(|_| Error::CredError)
    }

    fn verify(
        verification_key: &Self::VerificationKey,
        signature: &Self::Signature,
        message: &[u8],
    ) -> Result<(), Error> {
        libcrux_ed25519::verify(message, verification_key, signature).map_err(|_| Error::CredError)
    }

    /// CAUTION: This does not perform validation of the verification key.
    fn deserialize_credential(bytes: &[u8]) -> Result<Self::VerificationKey, Error> {
        bytes.try_into().map_err(|_| Error::CredError)
    }

    fn deserialize_signature(bytes: &[u8]) -> Result<Self::Signature, Error> {
        bytes.try_into().map_err(|_| Error::CredError)
    }

    fn validate_credential(
        credential: Self::Credential,
        cert: &Self::Certificate,
    ) -> Result<Self::VerificationKey, Error> {
        // We only check that the out of band key is the same as the
        // key that is provided as the credential.
        (credential == *cert)
            .then_some(credential)
            .ok_or(Error::CredError)
    }
}
