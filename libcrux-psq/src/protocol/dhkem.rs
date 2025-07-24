//! Diffie-Hellman KEM type wrappers
//!
//! This module provides wrappers around KEM types, assuming a DH-KEM
//! style API.
use libcrux_ecdh::{secret_to_public, Algorithm};
use rand::CryptoRng;
use tls_codec::{TlsDeserialize, TlsDeserializeBytes, TlsSerialize, TlsSerializeBytes, TlsSize};

use crate::protocol::api::Error;

#[derive(TlsSerializeBytes, TlsSize)]
/// A wrapper around a KEM shared secret.
///
/// We don't directly expose this.
pub(crate) struct DHSharedSecret(Vec<u8>);

impl AsRef<[u8]> for DHSharedSecret {
    fn as_ref(&self) -> &[u8] {
        self.0.as_slice()
    }
}

#[derive(
    Eq,
    Debug,
    Hash,
    PartialEq,
    Clone,
    TlsDeserializeBytes,
    TlsSerializeBytes,
    TlsSize,
    TlsSerialize,
    TlsDeserialize,
)]
/// A wrapper around a KEM public key.
pub struct DHPublicKey(Vec<u8>);

impl AsRef<[u8]> for DHPublicKey {
    fn as_ref(&self) -> &[u8] {
        self.0.as_slice()
    }
}

/// A wrapper around a KEM private key.
pub struct DHPrivateKey(Vec<u8>);

impl AsRef<[u8]> for DHPrivateKey {
    fn as_ref(&self) -> &[u8] {
        self.0.as_slice()
    }
}

impl DHSharedSecret {
    /// Derive a shared secret, DH-KEM style.
    pub(crate) fn derive(sk: &DHPrivateKey, pk: &DHPublicKey) -> Result<DHSharedSecret, Error> {
        Ok(DHSharedSecret(
            libcrux_ecdh::derive(Algorithm::X25519, &pk.0, &sk.0)
                .map_err(|_| Error::CryptoError)?,
        ))
    }
}

impl DHPrivateKey {
    /// Creates a new KEM private key.
    pub fn new(rng: &mut impl CryptoRng) -> Self {
        Self(
            libcrux_ecdh::generate_secret(libcrux_ecdh::Algorithm::X25519, rng)
                .expect("Insufficient Randomness"),
        )
    }

    /// Compute the KEM public key from the KEM private key.
    pub fn to_public(&self) -> DHPublicKey {
        DHPublicKey(
            secret_to_public(libcrux_ecdh::Algorithm::X25519, &self.0)
                .expect("secret key is honestly generated X25519 key"),
        )
    }
}

pub struct DHKeyPair {
    pub(crate) sk: DHPrivateKey,
    pub pk: DHPublicKey,
}

impl DHKeyPair {
    pub fn new(rng: &mut impl CryptoRng) -> Self {
        let sk = DHPrivateKey::new(rng);
        let pk = sk.to_public();
        Self { sk, pk }
    }
}
