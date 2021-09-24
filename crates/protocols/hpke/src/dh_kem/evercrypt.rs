//! # Evercrypt DH provider
//!
//! Pipe DH calls through to evercrypt

use evercrypt::prelude::*;

use crate::kem::{Error, KemKeyType};

impl From<EcdhError> for Error {
    fn from(e: EcdhError) -> Self {
        match e {
            EcdhError::UnknownAlgorithm => Self::UnknownMode,
            _ => Self::CryptoError,
        }
    }
}

/// Prepend 0x04 for uncompressed NIST curve points.
#[inline(always)]
fn nist_format_uncompressed(mut pk: Vec<u8>) -> Vec<u8> {
    let mut tmp = Vec::with_capacity(pk.len() + 1);
    tmp.push(0x04);
    tmp.append(&mut pk);
    tmp
}

#[inline(always)]
fn kem_key_type_to_mode(alg: KemKeyType) -> Result<EcdhMode, Error> {
    match alg {
        KemKeyType::X25519 => Ok(EcdhMode::X25519),
        KemKeyType::P256 => Ok(EcdhMode::P256),
        _ => Err(Error::UnknownMode),
    }
}

#[inline(always)]
pub(super) fn derive(alg: KemKeyType, pk: &[u8], sk: &[u8]) -> Result<Vec<u8>, Error> {
    let evercrypt_mode = kem_key_type_to_mode(alg)?;
    ecdh_derive(evercrypt_mode, pk, sk).map_err(|e| e.into())
}

#[inline(always)]
pub(super) fn derive_base(alg: KemKeyType, sk: &[u8]) -> Result<Vec<u8>, Error> {
    let evercrypt_mode = kem_key_type_to_mode(alg)?;
    ecdh_derive_base(evercrypt_mode, sk)
        .map_err(|e| e.into())
        .map(|p| {
            if evercrypt_mode == EcdhMode::P256 {
                nist_format_uncompressed(p)
            } else {
                p
            }
        })
}

#[inline(always)]
pub(super) fn key_gen(alg: KemKeyType) -> Result<Vec<u8>, Error> {
    let evercrypt_mode = kem_key_type_to_mode(alg)?;
    ecdh::key_gen(evercrypt_mode).map_err(|e| e.into())
}

#[inline(always)]
pub(super) fn validate_p256_sk(candidate: &[u8]) -> Result<Vec<u8>, Error> {
    p256_validate_sk(&candidate)
        .map_err(|_| Error::CryptoError)
        .map(|sk| sk.to_vec())
}
