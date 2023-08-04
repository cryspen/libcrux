//! # Key Encapsulation Mechanism
//!
//! A KEM interface.

use rand::{CryptoRng, Rng};

use crate::ecdh;
use crate::kyber768;

/// KEM Algorithms
///
/// This includes named elliptic curves or dedicated KEM algorithms like Kyber.
#[derive(Clone, Copy, PartialEq, Debug)]
pub enum Algorithm {
    X25519,
    X448,
    Secp256r1,
    Secp384r1,
    Secp521r1,
    Kyber768,
}

#[derive(Debug, PartialEq, Eq)]
pub enum Error {
    EcDhError(ecdh::Error),
    KeyGen,
    Encapsulate,
    Decapsulate,
    UnsupportedAlgorithm,
}

impl TryFrom<Algorithm> for ecdh::Algorithm {
    type Error = &'static str;

    fn try_from(value: Algorithm) -> Result<Self, Self::Error> {
        match value {
            Algorithm::X25519 => Ok(ecdh::Algorithm::X25519),
            Algorithm::X448 => Ok(ecdh::Algorithm::X448),
            Algorithm::Secp256r1 => Ok(ecdh::Algorithm::P256),
            Algorithm::Secp384r1 => Ok(ecdh::Algorithm::P384),
            Algorithm::Secp521r1 => Ok(ecdh::Algorithm::P521),
            _ => Err("provided algorithm is not an ECDH algorithm")
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
    Kyber768([u8; kyber768::SECRET_KEY_SIZE]),
}

/// A KEM public key.
pub enum PublicKey {
    X25519([u8; 32]),
    P256([u8; 64]),
    Kyber768([u8; kyber768::PUBLIC_KEY_SIZE]),
}

/// Compute the public key for a private key of the given [`Algorithm`].
pub fn secret_to_public(alg: Algorithm, sk: impl AsRef<[u8]>) -> Result<Vec<u8>, Error> {
    match alg {
        Algorithm::X25519 | Algorithm::Secp256r1 => {
            ecdh::secret_to_public(alg.try_into().unwrap(), sk.as_ref()).map_err(|e| e.into())
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
            ecdh::key_gen(alg.try_into().unwrap(), rng).map_err(|e| e.into())
        }

        Algorithm::Kyber768 => {
            let mut seed = [0; kyber768::KEY_GENERATION_SEED_SIZE];
            rng.try_fill_bytes(&mut seed).map_err(|_| Error::KeyGen)?;

            if let Ok((pk, sk)) = kyber768::generate_keypair(seed) {
                Ok((sk.into(), pk.into()))
            } else {
                Err(Error::KeyGen)
            }
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
            let gxy = ecdh::derive(alg.try_into().unwrap(), pk, &new_sk)?;
            Ok((gxy, new_pk))
        }

        Algorithm::Kyber768 => {
            let mut seed = [0; kyber768::SHARED_SECRET_SIZE];
            rng.try_fill_bytes(&mut seed).map_err(|_| Error::KeyGen)?;

            if let Ok((ct, ss)) = kyber768::encapsulate(pk.try_into().unwrap(), seed) {
                Ok((ss.into(), ct.into()))
            } else {
                Err(Error::Encapsulate)
            }
        }

        _ => Err(Error::UnsupportedAlgorithm),
    }
}

/// Decapsulate the shared secret in `ct` using the private key `sk`.
pub fn decapsulate(alg: Algorithm, ct: &[u8], sk: &[u8]) -> Result<Vec<u8>, Error> {
    match alg {
        Algorithm::X25519 | Algorithm::Secp256r1 => {
            let gxy = ecdh::derive(alg.try_into().unwrap(), ct, sk)?;
            Ok(gxy)
        }
        Algorithm::Kyber768 => {
            let ss = kyber768::decapsulate(sk.try_into().unwrap(), ct.try_into().unwrap());

            Ok(ss.into())
        }
        _ => Err(Error::UnsupportedAlgorithm),
    }
}
