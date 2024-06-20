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

mod hacl;

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

pub(crate) mod x25519_internal {
    use rand::{CryptoRng, Rng};

    use super::Error;

    pub struct PrivateKey(pub [u8; 32]);

    #[derive(Debug)]
    pub struct PublicKey(pub [u8; 32]);

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

    #[cfg(all(bmi2, adx, target_arch = "x86_64"))]
    pub fn derive(p: &PublicKey, s: &PrivateKey) -> Result<PublicKey, Error> {
        use crate::hacl::curve25519;
        use libcrux_platform::x25519_support;
        // On x64 we use vale if available or hacl as fallback.
        // Jasmin exists but is not verified yet.

        if x25519_support() {
            curve25519::vale::ecdh(s, p)
                .map_err(|e| Error::Custom(format!("HACL Error {:?}", e)))
                .map(|p| PublicKey(p))
            // XXX: not verified yet
            // crate::jasmin::x25519::mulx::derive(s, p)
            //     .map_err(|e| Error::Custom(format!("Libjade Error {:?}", e)))
        } else {
            curve25519::ecdh(s, p)
                .map_err(|e| Error::Custom(format!("HACL Error {:?}", e)))
                .map(|p| PublicKey(p))
            // XXX: not verified yet
            // crate::jasmin::x25519::derive(s, p)
            //     .map_err(|e| Error::Custom(format!("Libjade Error {:?}", e)))
        }
    }

    #[cfg(any(
        all(target_arch = "x86_64", any(not(bmi2), not(adx))),
        target_arch = "x86"
    ))]
    pub fn derive(p: &PublicKey, s: &PrivateKey) -> Result<PublicKey, Error> {
        use crate::hacl::curve25519;
        // On x64 we use vale if available or hacl as fallback.
        // Jasmin exists but is not verified yet.

        curve25519::ecdh(s, p)
            .map_err(|e| Error::Custom(format!("HACL Error {:?}", e)))
            .map(|p| PublicKey(p))
        // XXX: not verified yet
        // crate::jasmin::x25519::derive(s, p)
        //     .map_err(|e| Error::Custom(format!("Libjade Error {:?}", e)))
    }

    #[cfg(not(any(target_arch = "x86", target_arch = "x86_64")))]
    pub fn derive(p: &PublicKey, s: &PrivateKey) -> Result<PublicKey, Error> {
        // On any other platform we use the portable HACL implementation.
        use crate::hacl::curve25519;

        curve25519::ecdh(s, p)
            .map_err(|e| Error::Custom(format!("HACL Error {:?}", e)))
            .map(PublicKey)
    }

    // XXX: libjade's secret to public is broken on Windows (overflows the stack).
    // #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
    // pub(super) fn secret_to_public(p: &PrivateKey) -> Result<[u8; 32], Error> {
    //     crate::jasmin::x25519::secret_to_public(s).map_err(|e| Error::Custom(format!("Libjade Error {:?}", e)))
    // }

    // #[cfg(not(any(target_arch = "x86", target_arch = "x86_64")))]
    pub(crate) fn secret_to_public(s: &PrivateKey) -> Result<PublicKey, Error> {
        // On any other platform we use the portable HACL implementation.
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
}

pub use x25519_internal::derive as x25519_derive;
pub use x25519_internal::generate_secret as x25519_generate_secret;
pub use x25519_internal::key_gen as x25519_key_gen;
pub use x25519_internal::PrivateKey as X25519PrivateKey;
pub use x25519_internal::PublicKey as X25519PublicKey;

pub mod curve25519 {
    use super::hacl;
    pub use hacl::curve25519::Error;
}
pub(crate) mod p256_internal {
    use rand::{CryptoRng, Rng};

    // P256 we only have in HACL
    use crate::hacl::p256;

    use super::Error;

    pub struct PrivateKey(pub [u8; 32]);

    #[derive(Debug)]
    pub struct PublicKey(pub [u8; 64]);

    impl From<&[u8; 64]> for PublicKey {
        fn from(value: &[u8; 64]) -> Self {
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

    impl AsRef<[u8; 32]> for PrivateKey {
        fn as_ref(&self) -> &[u8; 32] {
            &self.0
        }
    }

    impl AsRef<[u8; 64]> for PublicKey {
        fn as_ref(&self) -> &[u8; 64] {
            &self.0
        }
    }

    pub(super) fn derive(p: &PublicKey, s: &PrivateKey) -> Result<PublicKey, Error> {
        // We assume that the private key has been validated.
        p256::ecdh(s, p)
            .map_err(|e| Error::Custom(format!("HACL Error {:?}", e)))
            .map(PublicKey)
    }

    pub(super) fn secret_to_public(s: &PrivateKey) -> Result<PublicKey, Error> {
        p256::validate_scalar(s).map_err(|e| Error::Custom(format!("HACL Error {:?}", e)))?;
        p256::secret_to_public(s)
            .map_err(|e| Error::Custom(format!("HACL Error {:?}", e)))
            .map(PublicKey)
    }

    pub fn validate_scalar(s: &PrivateKey) -> Result<(), Error> {
        p256::validate_scalar(s).map_err(|e| e.into())
    }

    #[allow(unused)]
    pub fn validate_point(p: &PublicKey) -> Result<(), Error> {
        p256::validate_point(p).map_err(|e| e.into())
    }

    pub(crate) fn prepare_public_key(public_key: &[u8]) -> Result<PublicKey, Error> {
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
        let pk = PublicKey(pk);

        p256::validate_point(&pk)
            .map(|()| pk)
            .map_err(|_| Error::InvalidPoint)
    }

    /// Generate a new p256 secret (scalar)
    pub fn generate_secret(rng: &mut (impl CryptoRng + Rng)) -> Result<PrivateKey, Error> {
        const LIMIT: usize = 100;
        for _ in 0..LIMIT {
            let mut out = [0u8; 32];
            rng.try_fill_bytes(&mut out)
                .map_err(|_| Error::KeyGenError)?;

            let out = PrivateKey(out);
            if validate_scalar(&out).is_ok() {
                return Ok(out);
            }
        }
        Err(Error::KeyGenError)
    }

    /// Generate a new P256 key pair
    pub fn key_gen(rng: &mut (impl CryptoRng + Rng)) -> Result<(PrivateKey, PublicKey), Error> {
        let sk = generate_secret(rng)?;
        let pk = secret_to_public(&sk)?;
        Ok((sk, pk))
    }
}

pub mod p256 {
    use super::hacl;
    pub use hacl::p256::compressed_to_coordinates;
    pub use hacl::p256::uncompressed_to_coordinates;
    pub use hacl::p256::validate_point;
    pub use hacl::p256::validate_scalar_slice;
    pub use hacl::p256::Error;
}

pub use p256_internal::generate_secret as p256_generate_secret;
pub use p256_internal::key_gen as p256_key_gen;
pub use p256_internal::validate_scalar as p256_validate_scalar;
pub use p256_internal::PrivateKey as P256PrivateKey;
pub use p256_internal::PublicKey as P256PublicKey;

/// Derive the ECDH shared secret.
/// Returns `Ok(point * scalar)` on the provided curve [`Algorithm`] or an error.
pub fn derive(
    alg: Algorithm,
    point: impl AsRef<[u8]>,
    scalar: impl AsRef<[u8]>,
) -> Result<Vec<u8>, Error> {
    match alg {
        Algorithm::X25519 => {
            x25519_internal::derive(&point.as_ref().try_into()?, &scalar.as_ref().try_into()?)
                .map(|r| r.0.into())
        }
        Algorithm::P256 => {
            let point = p256_internal::prepare_public_key(point.as_ref())?;
            let scalar = hacl::p256::validate_scalar_slice(scalar.as_ref())
                .map_err(|_| Error::InvalidScalar)?;

            p256_internal::derive(&point, &scalar).map(|r| r.0.into())
        }
        _ => Err(Error::UnknownAlgorithm),
    }
}

pub fn p256_derive(
    point: &p256_internal::PublicKey,
    scalar: &p256_internal::PrivateKey,
) -> Result<p256_internal::PublicKey, Error> {
    p256_internal::validate_point(point)?;
    p256_internal::validate_scalar(scalar)?;

    p256_internal::derive(point, scalar)
}

/// Derive the public key for the provided secret key `scalar`.
pub fn secret_to_public(alg: Algorithm, scalar: impl AsRef<[u8]>) -> Result<Vec<u8>, Error> {
    match alg {
        Algorithm::X25519 => {
            x25519_internal::secret_to_public(&scalar.as_ref().try_into()?).map(|r| r.0.into())
        }
        Algorithm::P256 => {
            p256_internal::secret_to_public(&scalar.as_ref().try_into()?).map(|r| r.0.into())
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
        Algorithm::P256 => p256_internal::validate_scalar(&s.as_ref().try_into()?),
        _ => Err(Error::UnknownAlgorithm),
    }
}

use rand::{CryptoRng, Rng};

/// Generate a new private key scalar.
///
/// The function returns the new scalar or an [`Error::KeyGenError`] if it was unable to
/// generate a new key. If this happens, the provided `rng` is probably faulty.
pub fn generate_secret(alg: Algorithm, rng: &mut (impl CryptoRng + Rng)) -> Result<Vec<u8>, Error> {
    match alg {
        Algorithm::X25519 => x25519_internal::generate_secret(rng).map(|k| k.0.to_vec()),
        Algorithm::P256 => p256_internal::generate_secret(rng).map(|k| k.0.to_vec()),
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
