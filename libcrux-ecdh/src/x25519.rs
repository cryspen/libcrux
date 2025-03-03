// XXX: This could be simplified with the pure Rust version now.

use alloc::format;
use rand::{CryptoRng, Rng, TryRngCore};

use super::Error;

pub struct PrivateKey(pub [u8; 32]);

#[derive(Debug)]
pub struct PublicKey(pub [u8; 32]);

/// Output of a scalar multiplication between a public key and a secret key.
///
/// This value is NOT (!) safe for use as a key and needs to be processed in a round of key
/// derivation, to ensure both that the output is uniformly random and that unkown key share
/// attacks can not happen.
pub struct SharedSecret(pub [u8; 32]);

impl From<&[u8; 32]> for PublicKey {
    fn from(value: &[u8; 32]) -> Self {
        Self(*value)
    }
}

impl TryFrom<&[u8]> for PublicKey {
    type Error = Error;

    fn try_from(value: &[u8]) -> Result<Self, Self::Error> {
        Ok(Self(value.try_into().map_err(|_| Error::InvalidPoint)?))
    }
}

impl From<&[u8; 32]> for PrivateKey {
    fn from(value: &[u8; 32]) -> Self {
        Self(*value)
    }
}

impl TryFrom<&[u8]> for PrivateKey {
    type Error = Error;

    fn try_from(value: &[u8]) -> Result<Self, Self::Error> {
        Ok(Self(value.try_into().map_err(|_| Error::InvalidScalar)?))
    }
}

impl From<&[u8; 32]> for SharedSecret {
    fn from(value: &[u8; 32]) -> Self {
        Self(*value)
    }
}

impl TryFrom<&[u8]> for SharedSecret {
    type Error = Error;

    fn try_from(value: &[u8]) -> Result<Self, Self::Error> {
        Ok(Self(value.try_into().map_err(|_| Error::InvalidScalar)?))
    }
}

impl AsRef<[u8]> for PrivateKey {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}

impl AsRef<[u8]> for PublicKey {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}

impl AsRef<[u8]> for SharedSecret {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}

impl AsRef<[u8; 32]> for PrivateKey {
    fn as_ref(&self) -> &[u8; 32] {
        &self.0
    }
}

impl AsRef<[u8; 32]> for PublicKey {
    fn as_ref(&self) -> &[u8; 32] {
        &self.0
    }
}

impl AsRef<[u8; 32]> for SharedSecret {
    fn as_ref(&self) -> &[u8; 32] {
        &self.0
    }
}

pub fn derive(p: &PublicKey, s: &PrivateKey) -> Result<SharedSecret, Error> {
    // Use the portable HACL implementation.
    use crate::hacl::curve25519;

    curve25519::ecdh(s, p)
        .map_err(|e| Error::Custom(format!("HACL Error {:?}", e)))
        .map(SharedSecret)
}

pub(crate) fn secret_to_public(s: &PrivateKey) -> Result<PublicKey, Error> {
    // Use the portable HACL implementation.
    use crate::hacl::curve25519;

    Ok(PublicKey(curve25519::secret_to_public(s)))
}

/// Generate a new x25519 secret.
pub fn generate_secret(rng: &mut (impl CryptoRng + Rng)) -> Result<PrivateKey, Error> {
    const LIMIT: usize = 100;
    for _ in 0..LIMIT {
        let mut out = [0u8; 32];
        rng.try_fill_bytes(&mut out)
            .map_err(|_| Error::KeyGenError)?;

        // We don't want a 0 key.
        if out.iter().all(|&b| b == 0) {
            continue;
        }

        // We clamp the key already to make sure it can't be misused.
        out[0] &= 248u8;
        out[31] &= 127u8;
        out[31] |= 64u8;

        return Ok(PrivateKey(out));
    }

    Err(Error::KeyGenError)
}

/// Generate a new P256 key pair
pub fn key_gen(rng: &mut (impl CryptoRng + Rng)) -> Result<(PrivateKey, PublicKey), Error> {
    let sk = generate_secret(rng)?;
    let pk = secret_to_public(&sk)?;
    Ok((sk, pk))
}
