//! # Key Encapsulation Mechanism
//!
//! A KEM interface.

use rand::{CryptoRng, Rng};

use crate::ecdh;

/// KEM Algorithms
///
/// This includes named elliptic curves or dedicated KEM algorithms like Kyber.
///
/// Currently only `Secp256r1` and `X25519` are supported.
#[derive(Clone, Copy, PartialEq, Debug)]
pub enum Algorithm {
    X25519,
    X448,
    Secp256r1,
    Secp384r1,
    Secp521r1,
}

#[derive(Debug, PartialEq, Eq)]
pub enum Error {
    EcDhError(ecdh::Error),
    KeyGen,
    UnsupportedAlgorithm,
}

impl From<Algorithm> for ecdh::Algorithm {
    fn from(value: Algorithm) -> Self {
        match value {
            Algorithm::X25519 => ecdh::Algorithm::X25519,
            Algorithm::X448 => ecdh::Algorithm::X448,
            Algorithm::Secp256r1 => ecdh::Algorithm::P256,
            Algorithm::Secp384r1 => ecdh::Algorithm::P384,
            Algorithm::Secp521r1 => ecdh::Algorithm::P521,
        }
    }
}

impl From<ecdh::Error> for Error {
    fn from(value: ecdh::Error) -> Self {
        Error::EcDhError(value)
    }
}

/// A KEM private key.
pub enum PrivateKey {
    X25519([u8; 32]),
    P256([u8; 32]),
}

/// A KEM public key.
pub enum PublicKey {
    X25519([u8; 32]),
    P256([u8; 64]),
}

/// Compute the public key for a private key of the given [`Algorithm`].
pub fn secret_to_public(alg: Algorithm, sk: impl AsRef<[u8]>) -> Result<Vec<u8>, Error> {
    match alg {
        Algorithm::X25519 | Algorithm::Secp256r1 => {
            ecdh::secret_to_public(alg.into(), sk.as_ref()).map_err(|e| e.into())
        }
        _ => Err(Error::UnsupportedAlgorithm),
    }
}

/// Generate a key pair for the [`Algorithm`] using the provided rng.
///
/// The function returns a fresh key or a [`Error::KeyGen`] error if
/// * not enough entropy was available
/// * it was not possible to generate a valid key within a reasonable amount of iterations.
pub fn key_gen(
    alg: Algorithm,
    rng: &mut (impl CryptoRng + Rng),
) -> Result<(Vec<u8>, Vec<u8>), Error> {
    match alg {
        Algorithm::X25519 | Algorithm::Secp256r1 => {
            ecdh::key_gen(alg.into(), rng).map_err(|e| e.into())
        }
        _ => Err(Error::UnsupportedAlgorithm),
    }
}

/// Encapsulate a shared secret to the provided `pk` and return the `(Key, Enc)` tuple.
pub fn encapsulate(
    alg: Algorithm,
    pk: &[u8],
    rng: &mut (impl CryptoRng + Rng),
) -> Result<(Vec<u8>, Vec<u8>), Error> {
    let (new_sk, new_pk) = key_gen(alg, rng)?;
    match alg {
        Algorithm::X25519 | Algorithm::Secp256r1 => {
            let gxy = ecdh::derive(alg.into(), pk, &new_sk)?;
            Ok((gxy, new_pk))
        }
        _ => Err(Error::UnsupportedAlgorithm),
    }
}

/// Decapsulate the shared secret in `ct` using the private key `sk`.
pub fn decapsulate(alg: Algorithm, ct: &[u8], sk: &[u8]) -> Result<Vec<u8>, Error> {
    match alg {
        Algorithm::X25519 | Algorithm::Secp256r1 => {
            let gxy = ecdh::derive(alg.into(), ct, sk)?;
            Ok(gxy)
        }
        _ => Err(Error::UnsupportedAlgorithm),
    }
}
