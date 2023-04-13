//! # Signatures
//!
//! * EcDSA P256 with Sha256, Sha384, and Sha512
//! * EdDSA 25519

use hacl::hazmat::{self, ed25519, p256};
use rand::{CryptoRng, Rng, RngCore};

use crate::ecdh;

/// Signature Errors
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Error {
    SigningError,
    InvalidSignature,
    KeyGenError,
}

/// The digest algorithm used for the signature scheme (when required).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DigestAlgorithm {
    Sha256,
    Sha384,
    Sha512,
}

/// The Signature Algorithm
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Algorithm {
    EcDsaP256(DigestAlgorithm),
    Ed25519,
}

/// The signature
#[derive(Debug)]
pub enum Signature {
    EcDsaP256(EcDsaP256Signature),
    Ed25519(Ed25519Signature),
}

/// A [`Algorithm::EcDsaP256`] Signature
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct EcDsaP256Signature {
    r: [u8; 32],
    s: [u8; 32],
    alg: Algorithm,
}

/// A [`Algorithm::Ed25519`] Signature
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Ed25519Signature {
    signature: [u8; 32],
}

impl Ed25519Signature {
    /// Generate a signature from the raw 32 bytes.
    pub fn from_bytes(signature: [u8; 32]) -> Self {
        Self { signature }
    }
}

impl EcDsaP256Signature {
    /// Generate a signature from the raw values r and s.
    pub fn from_raw(r: [u8; 32], s: [u8; 32], alg: Algorithm) -> Self {
        Self { r, s, alg }
    }

    /// Generate a signature from the raw values r || s.
    pub fn from_bytes(signature_bytes: [u8; 64], alg: Algorithm) -> Self {
        Self {
            r: signature_bytes[0..32].try_into().unwrap(),
            s: signature_bytes[32..].try_into().unwrap(),
            alg,
        }
    }
}

/// Prepare the nonce for EcDSA and validate the key
fn ecdsa_p256_sign_prep(
    private_key: &[u8],
    rng: &mut (impl CryptoRng + RngCore),
) -> Result<([u8; 32], [u8; 32]), Error> {
    let private_key = p256::validate_scalar_slice(private_key).map_err(|_| Error::SigningError)?;

    let mut nonce = [0u8; 32];
    loop {
        rng.try_fill_bytes(&mut nonce)
            .map_err(|_| Error::SigningError)?;
        // Make sure it's a valid nonce.
        if p256::validate_scalar(&nonce).is_ok() {
            break;
        }
    }

    Ok((private_key, nonce))
}

/// Wrap EcDSA result into a signature
fn ecdsa_p256_sign_post(signature: [u8; 64], alg: Algorithm) -> Result<Signature, Error> {
    Ok(Signature::EcDsaP256(EcDsaP256Signature {
        r: signature[..32]
            .try_into()
            .map_err(|_| Error::SigningError)?,
        s: signature[32..]
            .try_into()
            .map_err(|_| Error::SigningError)?,
        alg,
    }))
}

fn into_signing_error(_e: impl Into<hazmat::Error>) -> Error {
    Error::SigningError
}

/// Sign the `payload` with the given [`Algorithm`] and `private_key`.
///
/// Returns the [`Signature`] or an [`Error::SigningError`].
pub fn sign(
    alg: Algorithm,
    payload: &[u8],
    private_key: &[u8],
    rng: &mut (impl CryptoRng + RngCore),
) -> Result<Signature, Error> {
    let signature = match alg {
        Algorithm::EcDsaP256(DigestAlgorithm::Sha256) => {
            let (private_key, nonce) = ecdsa_p256_sign_prep(private_key, rng)?;
            ecdsa_p256_sign_post(
                p256::ecdsa::sign_sha256(payload, &private_key, &nonce)
                    .map_err(into_signing_error)?,
                alg,
            )?
        }
        Algorithm::EcDsaP256(DigestAlgorithm::Sha384) => {
            let (private_key, nonce) = ecdsa_p256_sign_prep(private_key, rng)?;
            ecdsa_p256_sign_post(
                p256::ecdsa::sign_sha384(payload, &private_key, &nonce)
                    .map_err(into_signing_error)?,
                alg,
            )?
        }
        Algorithm::EcDsaP256(DigestAlgorithm::Sha512) => {
            let (private_key, nonce) = ecdsa_p256_sign_prep(private_key, rng)?;
            ecdsa_p256_sign_post(
                p256::ecdsa::sign_sha512(payload, &private_key, &nonce)
                    .map_err(into_signing_error)?,
                alg,
            )?
        }
        Algorithm::Ed25519 => {
            let signature = ed25519::sign(
                payload,
                private_key.try_into().map_err(|_| Error::SigningError)?,
            )
            .map_err(into_signing_error)?;
            Signature::Ed25519(Ed25519Signature { signature })
        }
    };

    Ok(signature)
}

fn into_verify_error(_e: impl Into<hazmat::Error>) -> Error {
    Error::InvalidSignature
}

/// Prepare the public key for EcDSA
fn ecdsa_p256_verify_prep(public_key: &[u8]) -> Result<[u8; 64], Error> {
    if public_key.is_empty() {
        return Err(Error::SigningError);
    }

    // Parse the public key.
    let pk = if let Ok(pk) = p256::uncompressed_to_coordinates(public_key) {
        pk
    } else {
        // Might be uncompressed
        if let Ok(pk) = p256::compressed_to_coordinates(public_key) {
            pk
        } else {
            // Might be a simple concatenation
            public_key.try_into().map_err(|_| Error::InvalidSignature)?
        }
    };

    p256::validate_point(&pk)
        .map(|()| pk)
        .map_err(into_verify_error)
}

/// Verify the `payload` and `signature` with the `public_key`.
///
/// Return `()` or [`Error::InvalidSignature`].
pub fn verify(payload: &[u8], signature: &Signature, public_key: &[u8]) -> Result<(), Error> {
    match signature {
        Signature::EcDsaP256(signature) => match signature.alg {
            Algorithm::EcDsaP256(DigestAlgorithm::Sha256) => {
                let pk = ecdsa_p256_verify_prep(public_key)?;
                p256::ecdsa::verify_sha256(payload, &pk, &signature.r, &signature.s)
            }
            Algorithm::EcDsaP256(DigestAlgorithm::Sha384) => {
                let pk = ecdsa_p256_verify_prep(public_key)?;
                p256::ecdsa::verify_sha384(payload, &pk, &signature.r, &signature.s)
            }
            Algorithm::EcDsaP256(DigestAlgorithm::Sha512) => {
                let pk = ecdsa_p256_verify_prep(public_key)?;
                p256::ecdsa::verify_sha512(payload, &pk, &signature.r, &signature.s)
            }
            _ => Err(p256::Error::InvalidInput),
        }
        .map_err(into_verify_error),
        Signature::Ed25519(signature) => {
            let public_key = public_key.try_into().map_err(|_| Error::InvalidSignature)?;
            ed25519::verify(payload, public_key, &signature.signature).map_err(into_verify_error)
        }
    }
}

/// Generate a fresh key pair.
///
/// The function returns the (secret key, public key) tuple, or an [`Error`].
pub fn key_gen(
    alg: Algorithm,
    rng: &mut (impl CryptoRng + Rng),
) -> Result<(Vec<u8>, Vec<u8>), Error> {
    match alg {
        Algorithm::EcDsaP256(_) => {
            ecdh::key_gen(ecdh::Algorithm::P256, rng).map_err(|_| Error::KeyGenError)
        }
        Algorithm::Ed25519 => {
            const LIMIT: usize = 100;
            let mut sk = [0u8; 32];
            for _ in 0..LIMIT {
                rng.try_fill_bytes(&mut sk)
                    .map_err(|_| Error::KeyGenError)?;

                // We don't want a 0 key.
                if sk.iter().all(|&b| b == 0) {
                    sk = [0u8; 32];
                    continue;
                }

                // We clamp the key already to make sure it can't be misused.
                sk[0] = sk[0] & 248u8;
                sk[31] = sk[31] & 127u8;
                sk[31] = sk[31] | 64u8;

                break;
            }
            let pk = ed25519::secret_to_public(&sk);

            Ok((sk.to_vec(), pk.to_vec()))
        }
    }
}
