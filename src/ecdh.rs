#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
use crate::jasmin;

#[derive(Debug, PartialEq, Eq)]
pub enum Error {
    InvalidPoint,
    InvalidScalar,
    UnknownAlgorithm,
    KeyGenError,
    Custom(&'static str),
}

/// ECDH algorithm.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Algorithm {
    X25519,
    P256,
}

/// Derive the ECDH shared secret.
/// Returns `Ok(p * s)` on the provided curve [`Algorithm`] or an error.
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
pub fn derive(mode: Algorithm, p: &[u8], s: &[u8]) -> Result<Vec<u8>, Error> {
    match mode {
        Algorithm::X25519 => {
            if p.len() != 32 {
                return Err(Error::InvalidPoint);
            }
            if s.len() != 32 {
                return Err(Error::InvalidScalar);
            }

            jasmin::x25519::x25519(s, p)
                .map_err(|e| Error::Custom(e))
                .map(|r| r.into())
        }
        Algorithm::P256 => unimplemented!(),
    }
}

/// Derive the ECDH shared secret.
/// Returns `Ok(p * s)` on the provided curve [`Algorithm`] or an error.
#[cfg(not(any(target_arch = "x86", target_arch = "x86_64")))]
pub fn derive(mode: Algorithm, p: &[u8], s: &[u8]) -> Result<Vec<u8>, Error> {
    use crate::hacl;

    match mode {
        Algorithm::X25519 => {
            if p.len() != 32 {
                return Err(Error::InvalidPoint);
            }
            if s.len() != 32 {
                return Err(Error::InvalidScalar);
            }

            hacl::curve25519::derive(p, s)
                .map_err(|s| Error::Custom(s))
                .map(|r| r.into())
        }
        Algorithm::P256 => unimplemented!(),
    }
}
