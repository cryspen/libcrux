//! # Rust Crypto DH provider
//!
//! Pipe DH calls through to the P256 and x25519-dalek

use crate::kem::{Error, KemKeyType};
use p256::{elliptic_curve::ecdh::diffie_hellman, EncodedPoint, PublicKey, SecretKey};
use rand::rngs::OsRng;
use x25519_dalek_ng::{PublicKey as X25519PublicKey, StaticSecret as X25519StaticSecret};

#[inline(always)]
pub(super) fn derive(alg: KemKeyType, pk: &[u8], sk: &[u8]) -> Result<Vec<u8>, Error> {
    match alg {
        KemKeyType::X25519 => {
            if sk.len() != 32 {
                return Err(Error::InvalidSecretKey);
            }
            if pk.len() != 32 {
                return Err(Error::InvalidPublicKey);
            }
            let mut sk_array = [0u8; 32];
            sk_array.clone_from_slice(sk);
            let mut pk_array = [0u8; 32];
            pk_array.clone_from_slice(pk);
            let sk = X25519StaticSecret::from(sk_array);
            Ok(sk
                .diffie_hellman(&X25519PublicKey::from(pk_array))
                .as_bytes()
                .to_vec())
        }
        KemKeyType::P256 => {
            let sk = SecretKey::from_bytes(sk).map_err(|_| Error::InvalidSecretKey)?;
            let pk = PublicKey::from_sec1_bytes(pk).map_err(|_| Error::InvalidPublicKey)?;
            Ok(diffie_hellman(sk.to_secret_scalar(), pk.as_affine())
                .as_bytes()
                .as_slice()
                .into())
        }
        _ => Err(Error::UnknownMode),
    }
}

#[inline(always)]
pub(super) fn derive_base(alg: KemKeyType, sk: &[u8]) -> Result<Vec<u8>, Error> {
    match alg {
        KemKeyType::X25519 => {
            if sk.len() != 32 {
                return Err(Error::InvalidSecretKey);
            }
            let mut sk_array = [0u8; 32];
            sk_array.clone_from_slice(sk);
            let sk = X25519StaticSecret::from(sk_array);
            Ok(X25519PublicKey::from(&sk).as_bytes().to_vec())
        }
        KemKeyType::P256 => {
            let sk = SecretKey::from_bytes(sk).map_err(|_| Error::InvalidSecretKey)?;
            Ok(
                EncodedPoint::encode(PublicKey::from_secret_scalar(&sk.to_secret_scalar()), false)
                    .as_bytes()
                    .into(),
            )
        }
        _ => Err(Error::UnknownMode),
    }
}

#[inline(always)]
pub(super) fn key_gen(alg: KemKeyType) -> Result<Vec<u8>, Error> {
    match alg {
        KemKeyType::X25519 => Ok(X25519StaticSecret::new(&mut OsRng).to_bytes().to_vec()),
        KemKeyType::P256 => Ok(SecretKey::random(&mut OsRng).to_bytes().as_slice().into()),
        _ => Err(Error::UnknownMode),
    }
}

#[inline(always)]
pub(super) fn validate_p256_sk(candidate: &[u8]) -> Result<Vec<u8>, Error> {
    SecretKey::from_bytes(candidate)
        .map_err(|_| Error::InvalidSecretKey)
        .map(|_| candidate.into())
}
