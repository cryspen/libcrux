use libcrux_hacl::{
    Hacl_P256_compressed_to_raw, Hacl_P256_dh_initiator, Hacl_P256_dh_responder,
    Hacl_P256_uncompressed_to_raw, Hacl_P256_validate_private_key, Hacl_P256_validate_public_key,
};

use crate::p256_internal::PrivateKey;

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Error {
    InvalidInput,
    InvalidScalar,
    InvalidPoint,
    NoCompressedPoint,
    NoUnCompressedPoint,
}

/// Parse an uncompressed P256 point and return the 64 byte array with the
/// concatenation of X||Y
pub fn uncompressed_to_coordinates(point: &[u8]) -> Result<[u8; 64], Error> {
    let mut concat_point = [0u8; 64];
    if point.len() >= 65 {
        let ok = unsafe {
            Hacl_P256_uncompressed_to_raw(point.as_ptr() as _, concat_point.as_mut_ptr())
        };
        if ok {
            Ok(concat_point)
        } else {
            Err(Error::InvalidInput)
        }
    } else {
        Err(Error::NoCompressedPoint)
    }
}

/// Parse an compressed P256 point and return the 64 byte array with the
/// concatenation of `X` and `Y`.
pub fn compressed_to_coordinates(point: &[u8]) -> Result<[u8; 64], Error> {
    let mut concat_point = [0u8; 64];
    if point.len() >= 33 {
        let ok =
            unsafe { Hacl_P256_compressed_to_raw(point.as_ptr() as _, concat_point.as_mut_ptr()) };
        if ok {
            Ok(concat_point)
        } else {
            Err(Error::InvalidInput)
        }
    } else {
        Err(Error::NoUnCompressedPoint)
    }
}

/// Validate a P256 point, where `point` is a 64 byte array with the
/// concatenation of `X` and `Y`.
///
/// Returns [`Error::InvalidPoint`] if the `point` is not valid.
pub fn validate_point(point: impl AsRef<[u8; 64]>) -> Result<(), Error> {
    if unsafe { Hacl_P256_validate_public_key(point.as_ref().as_ptr() as _) } {
        Ok(())
    } else {
        Err(Error::InvalidPoint)
    }
}

/// Validate a P256 secret key (scalar).
///
/// Returns [`Error::InvalidScalar`] if the `scalar` is not valid.
pub fn validate_scalar(scalar: &impl AsRef<[u8; 32]>) -> Result<(), Error> {
    validate_scalar_(scalar.as_ref())
}

/// Validate a P256 secret key (scalar).
///
/// Returns [`Error::InvalidScalar`] if the `scalar` is not valid.
pub fn validate_scalar_(scalar: &[u8; 32]) -> Result<(), Error> {
    if scalar.as_ref().iter().all(|b| *b == 0) {
        return Err(Error::InvalidScalar);
    }

    // Ensure that the key is in range  [1, p-1]
    if unsafe { Hacl_P256_validate_private_key(scalar.as_ref().as_ptr() as _) } {
        Ok(())
    } else {
        Err(Error::InvalidScalar)
    }
}

/// Validate a P256 secret key (scalar).
pub fn validate_scalar_slice(scalar: &[u8]) -> Result<PrivateKey, Error> {
    if scalar.is_empty() {
        return Err(Error::InvalidScalar);
    }

    let mut private = [0u8; 32];
    // Force the length of `sk` to 32 bytes.
    let sk_len = if scalar.len() >= 32 { 32 } else { scalar.len() };
    for i in 0..sk_len {
        private[31 - i] = scalar[scalar.len() - 1 - i];
    }

    validate_scalar_(&private).map(|_| PrivateKey(private))
}

/// Compute the ECDH with the `private_key` and `public_key`.
///
/// Returns the 64 bytes shared key.
pub fn ecdh(
    private_key: impl AsRef<[u8; 32]>,
    public_key: impl AsRef<[u8; 64]>,
) -> Result<[u8; 64], Error> {
    let mut shared = [0u8; 64];
    let ok = unsafe {
        Hacl_P256_dh_responder(
            shared.as_mut_ptr(),
            public_key.as_ref().as_ptr() as _,
            private_key.as_ref().as_ptr() as _,
        )
    };
    if !ok {
        Err(Error::InvalidInput)
    } else {
        Ok(shared)
    }
}

/// Compute the public key for the provided `private_key`.
///
/// Returns the 64 bytes public key.
pub fn secret_to_public(s: impl AsRef<[u8; 32]>) -> Result<[u8; 64], Error> {
    validate_scalar(&s)?;

    let mut out = [0u8; 64];
    if unsafe { Hacl_P256_dh_initiator(out.as_mut_ptr(), s.as_ref().as_ptr() as _) } {
        Ok(out)
    } else {
        Err(Error::InvalidScalar)
    }
}
