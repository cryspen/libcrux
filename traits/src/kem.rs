//! This module provides a common interface trait for key
//! encapsulation mechanisms (KEMs).
use rand::CryptoRng;

/// A KEM keypair.
pub type KeyPair<DK, EK> = (DK, EK);

/// Errors during KEM operations.
#[derive(Debug)]
pub enum KEMError {
    /// An error that occurred during key generation.
    KeyGeneration,
    /// An error that occurred during encapsulation.
    Encapsulation,
    /// An error that occurred during decapsulation.
    Decapsulation,
}

/// This trait captures the required interface of a key encapsulation
/// mechanism (KEM).
pub trait KEM {
    /// The KEM's ciphertext.
    type Ciphertext;
    /// The KEM's shared secret.
    type SharedSecret;
    /// The KEM's encapsulation key.
    type EncapsulationKey;
    /// The KEM's decapsulation key.
    type DecapsulationKey;

    /// Generate a pair of encapsulation and decapsulation keys.
    fn generate_key_pair(
        rng: &mut impl CryptoRng,
    ) -> Result<KeyPair<Self::DecapsulationKey, Self::EncapsulationKey>, KEMError>;

    /// Encapsulate a shared secret towards a given encapsulation key.
    fn encapsulate(
        ek: &Self::EncapsulationKey,
        rng: &mut impl CryptoRng,
    ) -> Result<(Self::SharedSecret, Self::Ciphertext), KEMError>;

    /// Decapsulate a shared secret.
    fn decapsulate(
        dk: &Self::DecapsulationKey,
        ctxt: &Self::Ciphertext,
    ) -> Result<Self::SharedSecret, KEMError>;
}
