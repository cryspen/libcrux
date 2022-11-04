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
pub fn derive(mode: Algorithm, p: &[u8], s: &[u8]) -> Result<Vec<u8>, Error> {
    match mode {
        Algorithm::X25519 => {
            if p.len() != 32 {
                return Err(Error::InvalidPoint);
            }
            if s.len() != 32 {
                return Err(Error::InvalidScalar);
            }

            // FIXME: x64 only. Switch between jasmin and hacl here
            jasmin::x25519::x25519(s, p)
                .map_err(|e| Error::Custom(e))
                .map(|r| r.into())
        }
        Algorithm::P256 => unimplemented!(),
    }
}
