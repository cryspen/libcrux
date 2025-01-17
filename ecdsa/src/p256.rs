//! ECDSA on P-256

use libcrux_p256::{
    compressed_to_raw, ecdsa_sign_p256_sha2, ecdsa_verif_p256_sha2, uncompressed_to_raw,
    validate_private_key, validate_public_key,
};
use rand::{CryptoRng, RngCore};

use super::Error;

/// A P-256 Signature
#[derive(Clone, Default)]
pub struct Signature {
    r: [u8; 32],
    s: [u8; 32],
}

/// An ECDSA P-256 private key
pub struct PrivateKey([u8; 32]);

#[derive(Debug)]
pub struct PublicKey(pub [u8; 64]);

mod conversions {
    use super::*;

    impl Signature {
        /// Generate a signature from the raw values r and s.
        pub fn from_raw(r: [u8; 32], s: [u8; 32]) -> Self {
            Self { r, s }
        }

        /// Generate a signature from the raw values r || s.
        pub fn from_bytes(signature_bytes: [u8; 64]) -> Self {
            Self {
                r: signature_bytes[0..32].try_into().unwrap(),
                s: signature_bytes[32..].try_into().unwrap(),
            }
        }

        /// Get the signature as the two raw 32 bytes `(r, s)`.
        pub fn as_bytes(&self) -> (&[u8; 32], &[u8; 32]) {
            (&self.r, &self.s)
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

    impl AsRef<[u8; 32]> for PrivateKey {
        fn as_ref(&self) -> &[u8; 32] {
            &self.0
        }
    }

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

    impl AsRef<[u8]> for PublicKey {
        fn as_ref(&self) -> &[u8] {
            &self.0
        }
    }

    impl AsRef<[u8; 64]> for PublicKey {
        fn as_ref(&self) -> &[u8; 64] {
            &self.0
        }
    }
}

/// Parse an uncompressed P256 point and return the 64 byte array with the
/// concatenation of X||Y
pub fn uncompressed_to_coordinates(point: &[u8]) -> Result<[u8; 64], Error> {
    let mut concat_point = [0u8; 64];
    if point.len() >= 65 {
        if uncompressed_to_raw(point, &mut concat_point) {
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
        if compressed_to_raw(point, &mut concat_point) {
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
    if validate_public_key(point.as_ref()) {
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
fn validate_scalar_(scalar: &[u8; 32]) -> Result<(), Error> {
    if scalar.as_ref().iter().all(|b| *b == 0) {
        return Err(Error::InvalidScalar);
    }

    // Ensure that the key is in range  [1, p-1]
    if validate_private_key(scalar.as_ref()) {
        Ok(())
    } else {
        Err(Error::InvalidScalar)
    }
}

/// Validate a P256 secret key (scalar).
fn validate_scalar_slice(scalar: &[u8]) -> Result<PrivateKey, Error> {
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

/// Prepare the nonce for EcDSA and validate the key
fn ecdsa_p256_sign_prep(
    private_key: &[u8],
    rng: &mut (impl CryptoRng + RngCore),
) -> Result<(PrivateKey, [u8; 32]), Error> {
    let private_key = validate_scalar_slice(private_key).map_err(|_| Error::SigningError)?;

    let mut nonce = [0u8; 32];
    loop {
        rng.try_fill_bytes(&mut nonce)
            .map_err(|_| Error::SigningError)?;

        // Make sure it's a valid nonce.
        if validate_scalar_slice(&nonce).is_ok() {
            break;
        }
    }

    Ok((private_key, nonce))
}

/// Sign the `payload` with the `private_key`.
pub fn sign(
    payload: &[u8],
    private_key: &[u8],
    rng: &mut (impl CryptoRng + RngCore),
) -> Result<Signature, Error> {
    let (private_key, nonce) = ecdsa_p256_sign_prep(private_key, rng)?;

    let mut signature = [0u8; 64];
    let len = u32_len(payload)?;

    if !ecdsa_sign_p256_sha2(&mut signature, len, payload, private_key.as_ref(), &nonce) {
        return Err(Error::SigningError);
    }

    Ok(Signature {
        r: signature[..32]
            .try_into()
            .map_err(|_| Error::SigningError)?,
        s: signature[32..]
            .try_into()
            .map_err(|_| Error::SigningError)?,
    })
}

fn u32_len(bytes: &[u8]) -> Result<u32, Error> {
    if bytes.len() > u32::MAX as usize {
        return Err(Error::InvalidInput);
    } else {
        Ok(bytes.len() as u32)
    }
}

/// Prepare the public key for EcDSA
fn ecdsa_p256_verify_prep(public_key: &[u8]) -> Result<[u8; 64], Error> {
    if public_key.is_empty() {
        return Err(Error::SigningError);
    }

    // Parse the public key.
    let pk = if let Ok(pk) = uncompressed_to_coordinates(public_key) {
        pk
    } else {
        // Might be uncompressed
        if let Ok(pk) = compressed_to_coordinates(public_key) {
            pk
        } else {
            // Might be a simple concatenation
            public_key.try_into().map_err(|_| Error::InvalidSignature)?
        }
    };

    validate_point(PublicKey(pk)).map(|()| pk)
}

/// Verify the `payload` and `signature` with the `public_key`.
///
/// Return `()` or [`Error::InvalidSignature`].
pub fn verify(payload: &[u8], signature: &Signature, public_key: &PublicKey) -> Result<(), Error> {
    let pk = ecdsa_p256_verify_prep(public_key.as_ref())?;
    let len = u32_len(payload)?;

    if ecdsa_verif_p256_sha2(len, payload, &pk, &signature.r, &signature.s) {
        Ok(())
    } else {
        Err(Error::InvalidSignature)
    }
}
