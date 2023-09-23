//! # ECDH
//!
//! Depending on the platform and available features the most efficient implementation
//! is chosen.
//!
//! ## x25519
//! For x25519 the portable HACL implementation is used unless running on an x64
//! CPU with BMI2 and ADX support. In this case the libjade implementation is
//! used.
//!
//! ## P256
//! For P256 the portable HACL implementation is used.

use crate::hacl;

#[derive(Debug, PartialEq, Eq)]
pub enum LowLevelError {
    Jasmin(String),
    Hacl(hacl::Error),
}

#[derive(Debug, PartialEq, Eq)]
pub enum Error {
    InvalidPoint,
    InvalidScalar,
    UnknownAlgorithm,
    KeyGenError,
    Custom(String),
    Wrap(LowLevelError),
}

impl From<hacl::p256::Error> for Error {
    fn from(value: hacl::p256::Error) -> Self {
        Error::Wrap(LowLevelError::Hacl(hacl::Error::P256(value)))
    }
}

/// ECDH algorithm.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Algorithm {
    X25519,
    X448,
    P256,
    P384,
    P521,
}

pub(crate) mod x25519 {
    use super::Error;

    #[cfg(all(bmi2, adx, target_arch = "x86_64"))]
    pub(super) fn derive(p: &[u8; 32], s: &[u8; 32]) -> Result<[u8; 32], Error> {
        use crate::hacl::curve25519;
        use libcrux_platform::x25519_support;
        // On x64 we use vale if available or hacl as fallback.
        // Jasmin exists but is not verified yet.

        if x25519_support() {
            curve25519::vale::ecdh(s, p).map_err(|e| Error::Custom(format!("HACL Error {:?}", e)))
            // XXX: not verified yet
            // crate::jasmin::x25519::mulx::derive(s, p)
            //     .map_err(|e| Error::Custom(format!("Libjade Error {:?}", e)))
        } else {
            curve25519::ecdh(s, p).map_err(|e| Error::Custom(format!("HACL Error {:?}", e)))
            // XXX: not verified yet
            // crate::jasmin::x25519::derive(s, p)
            //     .map_err(|e| Error::Custom(format!("Libjade Error {:?}", e)))
        }
    }

    #[cfg(any(
        all(target_arch = "x86_64", any(not(bmi2), not(adx))),
        target_arch = "x86"
    ))]
    pub(super) fn derive(p: &[u8; 32], s: &[u8; 32]) -> Result<[u8; 32], Error> {
        use crate::hacl::curve25519;
        // On x64 we use vale if available or hacl as fallback.
        // Jasmin exists but is not verified yet.

        curve25519::ecdh(s, p).map_err(|e| Error::Custom(format!("HACL Error {:?}", e)))
        // XXX: not verified yet
        // crate::jasmin::x25519::derive(s, p)
        //     .map_err(|e| Error::Custom(format!("Libjade Error {:?}", e)))
    }

    #[cfg(not(any(target_arch = "x86", target_arch = "x86_64")))]
    pub(super) fn derive(p: &[u8; 32], s: &[u8; 32]) -> Result<[u8; 32], Error> {
        // On any other platform we use the portable HACL implementation.
        use crate::hacl::curve25519;

        curve25519::ecdh(s, p).map_err(|e| Error::Custom(format!("HACL Error {:?}", e)))
    }

    // XXX: libjade's secret to public is broken on Windows (overflows the stack).
    // #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
    // pub(super) fn secret_to_public(s: &[u8; 32]) -> Result<[u8; 32], Error> {
    //     crate::jasmin::x25519::secret_to_public(s).map_err(|e| Error::Custom(format!("Libjade Error {:?}", e)))
    // }

    // #[cfg(not(any(target_arch = "x86", target_arch = "x86_64")))]
    pub(super) fn secret_to_public(s: &[u8; 32]) -> Result<[u8; 32], Error> {
        // On any other platform we use the portable HACL implementation.
        use crate::hacl::curve25519;

        Ok(curve25519::secret_to_public(s))
    }
}

pub(crate) mod p256 {
    // P256 we only have in HACL
    use crate::hacl::p256;

    use super::Error;

    pub(super) fn derive(p: &[u8; 64], s: &[u8; 32]) -> Result<[u8; 64], Error> {
        // We assume that the private key has been validated.
        p256::ecdh(s, p).map_err(|e| Error::Custom(format!("HACL Error {:?}", e)))
    }

    pub(super) fn secret_to_public(s: &[u8; 32]) -> Result<[u8; 64], Error> {
        p256::validate_scalar(s).map_err(|e| Error::Custom(format!("HACL Error {:?}", e)))?;
        p256::secret_to_public(s).map_err(|e| Error::Custom(format!("HACL Error {:?}", e)))
    }

    pub fn validate_scalar(s: &[u8; 32]) -> Result<(), Error> {
        p256::validate_scalar(s).map_err(|e| e.into())
    }

    #[allow(unused)]
    pub fn validate_point(p: &[u8; 64]) -> Result<(), Error> {
        p256::validate_point(p).map_err(|e| e.into())
    }

    pub(super) fn prepare_public_key(public_key: &[u8]) -> Result<[u8; 64], Error> {
        if public_key.is_empty() {
            return Err(Error::InvalidPoint);
        }

        // Parse the public key.
        let pk = if let Ok(pk) = p256::uncompressed_to_coordinates(public_key) {
            pk
        } else {
            // Might be uncompressed
            if public_key.len() == 33 {
                p256::compressed_to_coordinates(public_key).map_err(|_| Error::InvalidPoint)?
            } else {
                // Might be a simple concatenation
                public_key.try_into().map_err(|_| Error::InvalidPoint)?
            }
        };

        p256::validate_point(&pk)
            .map(|()| pk)
            .map_err(|_| Error::InvalidPoint)
    }
}

pub use p256::validate_scalar as p256_validate_scalar;

/// Derive the ECDH shared secret.
/// Returns `Ok(point * scalar)` on the provided curve [`Algorithm`] or an error.
pub fn derive(
    alg: Algorithm,
    point: impl AsRef<[u8]>,
    scalar: impl AsRef<[u8]>,
) -> Result<Vec<u8>, Error> {
    match alg {
        Algorithm::X25519 => x25519::derive(
            point.as_ref().try_into().map_err(|_| Error::InvalidPoint)?,
            scalar
                .as_ref()
                .try_into()
                .map_err(|_| Error::InvalidScalar)?,
        )
        .map(|r| r.into()),
        Algorithm::P256 => {
            let point = p256::prepare_public_key(point.as_ref())?;
            let scalar = hacl::p256::validate_scalar_slice(scalar.as_ref())
                .map_err(|_| Error::InvalidScalar)?;

            p256::derive(&point, &scalar).map(|r| r.into())
        }
        _ => Err(Error::UnknownAlgorithm),
    }
}

/// Derive the public key for the provided secret key `scalar`.
pub fn secret_to_public(alg: Algorithm, scalar: &[u8]) -> Result<Vec<u8>, Error> {
    match alg {
        Algorithm::X25519 => {
            x25519::secret_to_public(scalar.try_into().map_err(|_| Error::InvalidScalar)?)
                .map(|r| r.into())
        }
        Algorithm::P256 => {
            p256::secret_to_public(scalar.try_into().map_err(|_| Error::InvalidScalar)?)
                .map(|r| r.into())
        }
        _ => Err(Error::UnknownAlgorithm),
    }
}

/// Validate a secret key.
pub fn validate_scalar(alg: Algorithm, s: impl AsRef<[u8]>) -> Result<(), Error> {
    match alg {
        Algorithm::X25519 => {
            if s.as_ref().iter().all(|&b| b == 0) {
                Err(Error::InvalidScalar)
            } else {
                Ok(())
            }
        }
        Algorithm::P256 => {
            p256::validate_scalar(s.as_ref().try_into().map_err(|_| Error::InvalidScalar)?)
        }
        _ => Err(Error::UnknownAlgorithm),
    }
}

use rand::{CryptoRng, Rng};

/// Generate a new private key scalar.
///
/// The function returns the new scalar or an [`Error::KeyGenError`] if it was unable to
/// generate a new key. If this happens, the provided `rng` is probably faulty.
pub fn generate_secret(alg: Algorithm, rng: &mut (impl CryptoRng + Rng)) -> Result<Vec<u8>, Error> {
    // We don't want to have an endless loop. 100 are more than enough
    // iterations. If this doesn't work, the rng is broken.
    const LIMIT: usize = 100;
    match alg {
        Algorithm::X25519 => {
            for _ in 0..LIMIT {
                let mut out = [0u8; 32];
                rng.try_fill_bytes(&mut out)
                    .map_err(|_| Error::KeyGenError)?;

                // We don't want a 0 key.
                if out.iter().all(|&b| b == 0) {
                    continue;
                }

                // We clamp the key already to make sure it can't be misused.
                out[0] = out[0] & 248u8;
                out[31] = out[31] & 127u8;
                out[31] = out[31] | 64u8;

                return Ok(out.into());
            }
            return Err(Error::KeyGenError);
        }
        Algorithm::P256 => {
            for _ in 0..LIMIT {
                let mut out = [0u8; 32];
                rng.try_fill_bytes(&mut out)
                    .map_err(|_| Error::KeyGenError)?;

                if p256_validate_scalar(&out).is_ok() {
                    return Ok(out.into());
                }
            }
            return Err(Error::KeyGenError);
        }
        _ => Err(Error::UnknownAlgorithm),
    }
}

/// Generate a fresh key pair.
///
/// The function returns the (secret key, public key) tuple, or an [`Error`].
pub fn key_gen(
    alg: Algorithm,
    rng: &mut (impl CryptoRng + Rng),
) -> Result<(Vec<u8>, Vec<u8>), Error> {
    let sk = generate_secret(alg, rng)?;
    let pk = secret_to_public(alg, &sk)?;
    Ok((sk, pk))
}
