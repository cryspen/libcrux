//! KEM type wrappers
//!
//! This module provides wrappers around KEM types, assuming a DH-KEM
//! style API (for now). In the future this module should become
//! obsolete, since we can use libcrux KEM trait implementers
//! directly. (cf. https://github.com/cryspen/libcrux/issues/1035)
use libcrux_ecdh::{secret_to_public, Algorithm};
use rand::CryptoRng;
use tls_codec::{TlsDeserializeBytes, TlsSerializeBytes, TlsSize};

use crate::Error;

#[derive(TlsSerializeBytes, TlsSize)]
/// A wrapper around a KEM shared secret.
///
/// We don't directly expose this.
pub(crate) struct SharedSecret(Vec<u8>);

impl AsRef<[u8]> for SharedSecret {
    fn as_ref(&self) -> &[u8] {
        self.0.as_slice()
    }
}

#[derive(Clone, TlsDeserializeBytes, TlsSerializeBytes, TlsSize)]
/// A wrapper around a KEM public key.
pub struct PublicKey(Vec<u8>);

impl AsRef<[u8]> for PublicKey {
    fn as_ref(&self) -> &[u8] {
        self.0.as_slice()
    }
}

#[derive(Clone)]
/// A wrapper around a KEM private key.
pub struct PrivateKey(Vec<u8>);

impl AsRef<[u8]> for PrivateKey {
    fn as_ref(&self) -> &[u8] {
        self.0.as_slice()
    }
}

impl SharedSecret {
    /// Derive a shared secret, DH-KEM style.
    pub(crate) fn derive(sk: &PrivateKey, pk: &PublicKey) -> Result<SharedSecret, Error> {
        Ok(SharedSecret(
            libcrux_ecdh::derive(Algorithm::X25519, &pk.0, &sk.0)
                .map_err(|_| Error::CryptoError)?,
        ))
    }
}

impl PrivateKey {
    /// Creates a new KEM private key.
    pub fn new(rng: &mut impl CryptoRng) -> Self {
        Self(
            libcrux_ecdh::generate_secret(libcrux_ecdh::Algorithm::X25519, rng)
                .expect("Insufficient Randomness"),
        )
    }

    /// Compute the KEM public key from the KEM private key.
    pub fn to_public(&self) -> PublicKey {
        PublicKey(secret_to_public(libcrux_ecdh::Algorithm::X25519, &self.0).unwrap())
    }
}

#[derive(Clone)]
pub struct KEMKeyPair {
    pub(crate) sk: PrivateKey,
    pub(crate) pk: PublicKey,
}

impl KEMKeyPair {
    pub fn new(rng: &mut impl CryptoRng) -> Self {
        let sk = PrivateKey::new(rng);
        let pk = sk.to_public();
        Self { sk, pk }
    }
}
