use libcrux_hacl::{Hacl_Ed25519_secret_to_public, Hacl_Ed25519_sign, Hacl_Ed25519_verify};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Error {
    SigningError,
    InvalidSignature,
}

pub fn sign(payload: &[u8], private_key: &[u8; 32]) -> Result<[u8; 64], Error> {
    let mut signature = [0u8; 64];
    unsafe {
        Hacl_Ed25519_sign(
            signature.as_mut_ptr(),
            private_key.as_ptr() as _,
            payload.len().try_into().map_err(|_| Error::SigningError)?,
            payload.as_ptr() as _,
        );
    }

    Ok(signature)
}

pub fn verify(payload: &[u8], public_key: &[u8; 32], signature: &[u8; 64]) -> Result<(), Error> {
    if unsafe {
        Hacl_Ed25519_verify(
            public_key.as_ptr() as _,
            payload.len().try_into().map_err(|_| Error::SigningError)?,
            payload.as_ptr() as _,
            signature.as_ptr() as _,
        )
    } {
        Ok(())
    } else {
        Err(Error::InvalidSignature)
    }
}

/// Compute the public point for the given secret key `sk`.
pub fn secret_to_public(sk: &[u8; 32]) -> [u8; 32] {
    let mut out = [0u8; 32];
    unsafe {
        Hacl_Ed25519_secret_to_public(out.as_mut_ptr(), sk.as_ptr() as _);
    }
    out
}
