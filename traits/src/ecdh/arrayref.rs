//! This module contains the trait and related errors for an ECDH
//! implementation that takes array references as arguments and writes
//! outputs to mutable array references.

use libcrux_secrets::U8;

/// An Elliptic Curve Diffie-Hellman (ECDH) key exchange. This trait is the most low-level and mostly used in the
/// implementation of other, more usabe APIs on top.
pub trait ECDHArrayref<const RAND_LEN: usize, const SECRET_LEN: usize, const PUBLIC_LEN: usize> {
    /// Generate a Diffie-Hellman secret value.
    /// It is the responsibility of the caller to ensure  that the `rand` argument is actually
    /// random.
    fn generate_secret(
        secret: &mut [U8; SECRET_LEN],
        rand: &[U8; RAND_LEN],
    ) -> Result<(), ECDHError>;

    /// Derive a Diffie-Hellman public value from a secret value.
    fn secret_to_public(
        public: &mut [u8; PUBLIC_LEN],
        secret: &[U8; SECRET_LEN],
    ) -> Result<(), ECDHError>;

    /// Derive a Diffie-Hellman shared secret from a public and a
    /// secret value.
    ///
    /// This value is NOT (!) safe for use as a key and needs to be processed in a round of key
    /// derivation, to ensure both that the output is uniformly random and that unkown key share
    /// attacks can not happen.
    fn derive_ecdh(
        derived: &mut [U8; PUBLIC_LEN],
        public: &[u8; PUBLIC_LEN],
        secret: &[U8; SECRET_LEN],
    ) -> Result<(), ECDHError>;

    /// Check the validity of a Diffie-Hellman secret value.
    fn validate_secret(secret: &[U8; SECRET_LEN]) -> Result<(), ECDHError>;
}

#[derive(Debug)]
pub enum ECDHError {
    /// An error during secret value generation.
    GenerateSecret,
    /// An error derivation of a public value from a secret value.
    SecretToPublic,
    /// An error derivation of Diffie-Hellman shared secret.
    Derive,
    /// A Diffie-Hellman secret value was found to be invalid.
    ValidateSecret,
}

impl core::fmt::Display for ECDHError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let text = match self {
            ECDHError::GenerateSecret => "error generating ECDH secret value",
            ECDHError::SecretToPublic => {
                "error transforming secret ECDH value to public ECDH value"
            }
            ECDHError::Derive => "error deriving ECDH shared secret",
            ECDHError::ValidateSecret => "invalid ECDH secret value",
        };

        f.write_str(text)
    }
}

#[cfg(feature = "error-in-core")]
/// Here we implement the Error trait. This has only been added to core relatively recently, so we
/// are hiding that behind a feature.
mod error_in_core {
    impl core::error::Error for super::ECDHError {}
}
