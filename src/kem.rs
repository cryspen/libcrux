//! # Key Encapsulation Mechanism
//!
//! A KEM interface.

use rand::{CryptoRng, Rng};

use crate::ecdh;
use crate::jasmin::kyber_derand;

/// KEM Algorithms
///
/// This includes named elliptic curves or dedicated KEM algorithms like Kyber.
///
/// Currently only `Secp256r1` and `X25519` are supported for all platforms, and
/// `Kyber768` is available if the following two conditions are satisfied:
///
/// 1. The architecture is `x86` or `x86_64`
/// 2. The target operating system is Linux or macOS
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
    Kyber768([u8; 2400]),
}

/// A KEM public key.
pub enum PublicKey {
    X25519([u8; 32]),
    P256([u8; 64]),
    Kyber768([u8; 2400]),
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

        #[cfg(all(
            any(target_arch = "x86", target_arch = "x86_64"),
            any(target_os = "linux", target_os = "macos")
        ))]
        Algorithm::Kyber768 => {
            let mut seed = [0; 64];
            rng.fill(&mut seed);

            if let Ok((pk, sk)) = kyber_derand::kyber768_keypair_derand_ref(seed) {
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

        #[cfg(all(
            any(target_arch = "x86", target_arch = "x86_64"),
            any(target_os = "linux", target_os = "macos")
        ))]
        Algorithm::Kyber768 => {
            let mut seed = [0; 32];
            rng.fill(&mut seed);

            if let Ok((ct, ss)) = kyber_derand::kyber768_enc_derand_ref(pk.try_into().unwrap(), seed) {
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

        #[cfg(all(
            any(target_arch = "x86", target_arch = "x86_64"),
            any(target_os = "linux", target_os = "macos")
        ))]
        Algorithm::Kyber768 => {
            if let Ok(ss) = kyber_derand::kyber768_dec_ref(ct.try_into().unwrap(), sk.try_into().unwrap()) {
                Ok(ss.into())
            } else {
                Err(Error::Decapsulate)
            }
        }

        _ => Err(Error::UnsupportedAlgorithm),
    }
}
