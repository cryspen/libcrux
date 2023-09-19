//! # Key Encapsulation Mechanism
//!
//! A KEM interface.

use rand::{CryptoRng, Rng};

use crate::ecdh;
use crate::ecdh::p256;
use crate::ecdh::x25519;

mod kyber768;

// TODO: These functions are currently exposed simply in order to make NIST KAT
// testing possible without an implementation of the NIST AES-CTR DRBG. Remove them
// (and change the visibility of the exported functions to pub(crate)) the
// moment we have an implementation of one. This is tracked by:
// https://github.com/cryspen/libcrux/issues/36
pub use kyber768::decapsulate as kyber768_decapsulate_derand;
pub use kyber768::encapsulate as kyber768_encapsulate_derand;
pub use kyber768::generate_keypair as kyber768_generate_keypair_derand;

use self::kyber768::Kyber768PrivateKey;
use self::kyber768::Kyber768PublicKey;

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
    Kyber768X25519,
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
            Algorithm::Kyber768X25519 => Ok(ecdh::Algorithm::X25519),
            _ => Err("provided algorithm is not an ECDH algorithm"),
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
    X25519(x25519::PrivateKey),
    P256(p256::PrivateKey),
    Kyber768(Kyber768PrivateKey),
    Kyber768X25519(Kyber768PrivateKey, x25519::PrivateKey),
}

/// A KEM public key.
pub enum PublicKey {
    X25519(x25519::PublicKey),
    P256(p256::PublicKey),
    Kyber768(Kyber768PublicKey),
    Kyber768X25519(Kyber768PublicKey, x25519::PublicKey),
}

/// Compute the public key for a private key of the given [`Algorithm`].
/// Applicable only to X25519 and secp256r1.
pub fn secret_to_public(alg: Algorithm, sk: impl AsRef<[u8]>) -> Result<Vec<u8>, Error> {
    match alg {
        Algorithm::X25519 | Algorithm::Secp256r1 => {
            ecdh::secret_to_public(alg.try_into().unwrap(), sk.as_ref()).map_err(|e| e.into())
        }
        _ => Err(Error::UnsupportedAlgorithm),
    }
}

fn gen_kyber768(
    rng: &mut (impl CryptoRng + Rng),
) -> Result<(Kyber768PrivateKey, Kyber768PublicKey), Error> {
    let mut seed = [0; kyber768::KEY_GENERATION_SEED_SIZE];
    rng.try_fill_bytes(&mut seed).map_err(|_| Error::KeyGen)?;

    if let Ok((pk, sk)) = kyber768::generate_keypair(seed) {
        Ok((sk, pk))
    } else {
        Err(Error::KeyGen)
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
) -> Result<(PrivateKey, PublicKey), Error> {
    match alg {
        Algorithm::X25519 => ecdh::x25519_key_gen(rng)
            .map_err(|e| e.into())
            .map(|(private, public)| (PrivateKey::X25519(private), PublicKey::X25519(public))),
        Algorithm::Secp256r1 => ecdh::p256_key_gen(rng)
            .map_err(|e| e.into())
            .map(|(private, public)| (PrivateKey::P256(private), PublicKey::P256(public))),
        Algorithm::Kyber768 => gen_kyber768(rng)
            .map(|(private, public)| (PrivateKey::Kyber768(private), PublicKey::Kyber768(public))),
        Algorithm::Kyber768X25519 => {
            let (kyber_private, kyber_public) = gen_kyber768(rng)?;
            let (x25519_private, x25519_public) = ecdh::x25519_key_gen(rng)?;
            Ok((
                PrivateKey::Kyber768X25519(kyber_private, x25519_private),
                PublicKey::Kyber768X25519(kyber_public, x25519_public),
            ))
        }
        _ => Err(Error::UnsupportedAlgorithm),
    }
}

/// Encapsulate a shared secret to the provided `pk` and return the `(Key, Enc)` tuple.
pub fn encapsulate(
    pk: &PublicKey,
    rng: &mut (impl CryptoRng + Rng),
) -> Result<(Vec<u8>, Vec<u8>), Error> {
    match pk {
        PublicKey::X25519(pk) => {
            let (new_sk, new_pk) = ecdh::x25519_key_gen(rng)?;
            let gxy = ecdh::derive(ecdh::Algorithm::X25519, pk, new_sk)?;
            Ok((gxy, new_pk.0.to_vec()))
        }
        PublicKey::P256(pk) => {
            let (new_sk, new_pk) = ecdh::p256_key_gen(rng)?;
            let gxy = ecdh::derive(ecdh::Algorithm::P256, pk, new_sk)?;
            Ok((gxy, new_pk.0.to_vec()))
        }

        PublicKey::Kyber768(pk) => kyber768_encaps(rng, pk),

        PublicKey::Kyber768X25519((pk)) => {
            let (mut kyber_ss, mut kyber_ct) =
                kyber768_encaps(rng, &pk.as_ref()[0..kyber768::PUBLIC_KEY_SIZE])?;
            let (new_sk, new_pk) = ecdh::x25519_key_gen(rng)?;
            let mut shared_secret = ecdh::derive(
                alg.try_into().unwrap(),
                &pk.as_ref()[kyber768::PUBLIC_KEY_SIZE..],
                new_sk,
            )?;
            shared_secret.append(&mut kyber_ss);
            let mut ct = new_pk.0.to_vec();
            ct.append(&mut kyber_ct);
            Ok((shared_secret, ct))
        }

        _ => Err(Error::UnsupportedAlgorithm),
    }
}

fn kyber768_encaps(
    rng: &mut (impl CryptoRng + Rng),
    pk: impl AsRef<[u8]>,
) -> Result<(Vec<u8>, Vec<u8>), Error> {
    let mut seed = [0; kyber768::SHARED_SECRET_SIZE];
    rng.try_fill_bytes(&mut seed).map_err(|_| Error::KeyGen)?;

    if let Ok((ct, ss)) = kyber768::encapsulate(
        pk.as_ref().try_into().map_err(|_| Error::Encapsulate)?,
        seed,
    ) {
        Ok((ss.into(), ct.into()))
    } else {
        Err(Error::Encapsulate)
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
            // TODO: Don't unwrap() here. See
            // https://github.com/cryspen/libcrux/issues/35
            let ss = kyber768::decapsulate(sk.try_into().unwrap(), ct.try_into().unwrap());

            Ok(ss.into())
        }
        _ => Err(Error::UnsupportedAlgorithm),
    }
}
