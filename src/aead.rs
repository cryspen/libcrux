//! # AEAD
//!
//! Depending on the platform and available features the most efficient implementation
//! is chosen.
//!
//! ## ChaCha20Poly1305
//!
//! The HACL implementations are used on all platforms.
//! On x64 CPUs with AVX and AVX2 support the 256-bit SIMD implementation is used.
//! On CPUs with a 128-bit SIMD unit (arm64, or SSE3, SSE4.1, and AVX on x64), the
//! 128-bit SIMD implementation is used.
//! In any other case the portable implementation is used.

#[cfg(aes_ni)]
use crate::hacl::aesgcm;
use crate::hacl::chacha20_poly1305;

use libcrux_platform::{aes_ni_support, simd128_support, simd256_support};

/// The caller has provided an invalid argument.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum InvalidArgumentError {
    /// An provided algorithm is not supported.
    UnsupportedAlgorithm,

    /// The provided key is invalid.
    InvalidKey,

    /// The provided tag is invalid.
    InvalidTag,

    /// The provided IV is invalid.
    InvalidIv,

    /// An unknown argument is invalid.
    Unknown,
}

impl core::fmt::Display for InvalidArgumentError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            InvalidArgumentError::UnsupportedAlgorithm => write!(f, "algorithm not supported"),
            InvalidArgumentError::InvalidKey => write!(f, "key is invalid"),
            InvalidArgumentError::InvalidTag => write!(f, "tag is invalid"),
            InvalidArgumentError::InvalidIv => write!(f, "IV is invalid"),
            InvalidArgumentError::Unknown => write!(f, "an unknown argument is invalid"),
        }
    }
}

/// An error occurred during encryption.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum EncryptError {
    /// An error occurred because the provided arguments were not valid.
    /// The inner error can be one of the variants [`InvalidArgumentError::UnsupportedAlgorithm`] and [`InvalidArgumentError::Unknown`].
    /// The latter can be returned e.g. when the provided message is too long.
    InvalidArgument(InvalidArgumentError),

    /// An internal error occurred.
    InternalError,
}

impl core::fmt::Display for EncryptError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            EncryptError::InvalidArgument(e) => {
                debug_assert!(matches!(
                    e,
                    InvalidArgumentError::UnsupportedAlgorithm | InvalidArgumentError::Unknown
                ));
                write!(f, "invalid argument provided: {e}")
            }
            EncryptError::InternalError => write!(f, "internal error"),
        }
    }
}

/// An error occurred during decryption.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum DecryptError {
    /// An argument is invalid. Inner variant can only be [`InvalidArgumentError::UnsupportedAlgorithm`].
    InvalidArgument(InvalidArgumentError),

    /// The ciphertext could not be decrypted with the given key.
    DecryptionFailed,

    /// An internal error occurred.
    InternalError,
}

impl core::fmt::Display for DecryptError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            DecryptError::InvalidArgument(e) => {
                debug_assert!(matches!(e, InvalidArgumentError::UnsupportedAlgorithm));
                write!(f, "invalid argument provided: {e}")
            }
            DecryptError::DecryptionFailed => write!(f, "decryption failed"),
            DecryptError::InternalError => write!(f, "internal error"),
        }
    }
}

/// The AEAD Algorithm Identifier.
#[derive(Clone, Copy, PartialEq, Debug)]
#[repr(u32)]
pub enum Algorithm {
    /// AES GCM 128
    Aes128Gcm = 1,

    /// AES GCM 256
    Aes256Gcm = 2,

    /// ChaCha20 Poly1305
    Chacha20Poly1305 = 3,
}

impl From<u8> for Algorithm {
    fn from(v: u8) -> Algorithm {
        match v {
            0 => Algorithm::Aes128Gcm,
            1 => Algorithm::Aes256Gcm,
            2 => Algorithm::Chacha20Poly1305,
            _ => panic!("Unknown AEAD mode {}", v),
        }
    }
}

impl Algorithm {
    /// Get the key size of the `Algorithm` in bytes.
    #[inline]
    pub const fn key_size(self) -> usize {
        match self {
            Algorithm::Aes128Gcm => 16,
            Algorithm::Aes256Gcm => 32,
            Algorithm::Chacha20Poly1305 => 32,
        }
    }

    /// Get the tag size of the `Algorithm` in bytes.
    #[inline]
    pub const fn tag_size(self) -> usize {
        match self {
            Algorithm::Aes128Gcm => 16,
            Algorithm::Aes256Gcm => 16,
            Algorithm::Chacha20Poly1305 => 16,
        }
    }

    /// Get the nonce size of the `Algorithm` in bytes.
    #[inline]
    pub const fn nonce_size(self) -> usize {
        match self {
            Algorithm::Aes128Gcm => 12,
            Algorithm::Aes256Gcm => 12,
            Algorithm::Chacha20Poly1305 => 12,
        }
    }

    /// Make sure the algorithm is supported by the hardware.
    /// Returns `Ok(())` or `Err(InvalidArgumentError::UnsupportedAlgorithm)`.
    #[inline]
    fn supported(self) -> Result<(), InvalidArgumentError> {
        if matches!(self, Algorithm::Aes128Gcm | Algorithm::Aes256Gcm) && !aes_ni_support() {
            Err(InvalidArgumentError::UnsupportedAlgorithm)
        } else {
            Ok(())
        }
    }
}

#[derive(Default)]
pub struct Aes128Key(pub [u8; Algorithm::key_size(Algorithm::Aes128Gcm)]);

#[derive(Default)]
pub struct Aes256Key(pub [u8; Algorithm::key_size(Algorithm::Aes256Gcm)]);

#[derive(Default)]
pub struct Chacha20Key(pub [u8; Algorithm::key_size(Algorithm::Chacha20Poly1305)]);

mod keygen {
    use super::*;
    use rand::{CryptoRng, RngCore};

    macro_rules! impl_key_gen {
        ($name:ident) => {
            impl $name {
                pub fn generate(rng: &mut (impl RngCore + CryptoRng)) -> Self {
                    let mut k = Self::default();
                    rng.fill_bytes(&mut k.0);
                    k
                }
            }
        };
    }
    impl_key_gen!(Aes128Key);
    impl_key_gen!(Aes256Key);
    impl_key_gen!(Chacha20Key);

    impl Key {
        pub fn generate(alg: Algorithm, rng: &mut (impl RngCore + CryptoRng)) -> Self {
            match alg {
                Algorithm::Aes128Gcm => Self::Aes128(Aes128Key::generate(rng)),
                Algorithm::Aes256Gcm => Self::Aes256(Aes256Key::generate(rng)),
                Algorithm::Chacha20Poly1305 => Self::Chacha20Poly1305(Chacha20Key::generate(rng)),
            }
        }
    }

    impl Iv {
        /// Generate a new random Iv
        pub fn generate(rng: &mut (impl RngCore + CryptoRng)) -> Self {
            let mut n = Self::default();
            rng.fill_bytes(&mut n.0);
            n
        }

        pub fn new(iv: impl AsRef<[u8]>) -> Result<Self, InvalidArgumentError> {
            Ok(Self(
                iv.as_ref()
                    .try_into()
                    .map_err(|_| InvalidArgumentError::InvalidIv)?,
            ))
        }
    }
}

/// An AEAD key.
pub enum Key {
    Aes128(Aes128Key),
    Aes256(Aes256Key),
    Chacha20Poly1305(Chacha20Key),
}

impl Key {
    /// Generate a [`Key`] for the [`Algorithm`] from the raw `bytes`.
    pub fn from_bytes(alg: Algorithm, bytes: Vec<u8>) -> Result<Self, InvalidArgumentError> {
        alg.supported()?;

        fn to_array<const N: usize>(bytes: Vec<u8>) -> Result<[u8; N], InvalidArgumentError> {
            bytes
                .try_into()
                .map_err(|_| InvalidArgumentError::InvalidKey)
        }

        let key = match alg {
            Algorithm::Aes128Gcm => Self::Aes128(Aes128Key(to_array(bytes)?)),
            Algorithm::Aes256Gcm => Self::Aes256(Aes256Key(to_array(bytes)?)),
            Algorithm::Chacha20Poly1305 => Self::Chacha20Poly1305(Chacha20Key(to_array(bytes)?)),
        };

        Ok(key)
    }

    /// Generate a [`Key`] for the [`Algorithm`] from the raw `bytes` slice.
    pub fn from_slice(
        alg: Algorithm,
        bytes: impl AsRef<[u8]>,
    ) -> Result<Self, InvalidArgumentError> {
        alg.supported()?;

        fn to_array<const N: usize>(
            bytes: impl AsRef<[u8]>,
        ) -> Result<[u8; N], InvalidArgumentError> {
            bytes
                .as_ref()
                .try_into()
                .map_err(|_| InvalidArgumentError::InvalidKey)
        }

        let key = match alg {
            Algorithm::Aes128Gcm => Self::Aes128(Aes128Key(to_array(bytes)?)),
            Algorithm::Aes256Gcm => Self::Aes256(Aes256Key(to_array(bytes)?)),
            Algorithm::Chacha20Poly1305 => Self::Chacha20Poly1305(Chacha20Key(to_array(bytes)?)),
        };

        Ok(key)
    }
}

#[derive(Default, PartialEq, Eq, Debug)]
pub struct Tag([u8; 16]);

impl Tag {
    /// Convert slice into a [`Tag`]
    pub fn from_slice(t: impl AsRef<[u8]>) -> Result<Self, InvalidArgumentError> {
        Ok(Self(
            t.as_ref()
                .try_into()
                .map_err(|_| InvalidArgumentError::InvalidTag)?,
        ))
    }
}

impl From<[u8; 16]> for Tag {
    fn from(value: [u8; 16]) -> Self {
        Self(value)
    }
}

impl AsRef<[u8]> for Tag {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}

impl AsMut<[u8]> for Tag {
    fn as_mut(&mut self) -> &mut [u8] {
        &mut self.0
    }
}

#[derive(Default)]
pub struct Iv(pub [u8; 12]);

#[cfg(simd256)]
fn encrypt_256(key: &Chacha20Key, msg_ctxt: &mut [u8], iv: Iv, aad: &[u8]) -> Tag {
    chacha20_poly1305::simd256::encrypt(&key.0, msg_ctxt, iv.0, aad).into()
}

/// Fallback when simd256 is detected at runtime but it wasn't compiled.
/// We try to fall back to simd128 in this case.
#[cfg(not(simd256))]
fn encrypt_256(key: &Chacha20Key, msg_ctxt: &mut [u8], iv: Iv, aad: &[u8]) -> Tag {
    encrypt_128(key, msg_ctxt, iv, aad)
}

#[cfg(simd128)]
fn encrypt_128(key: &Chacha20Key, msg_ctxt: &mut [u8], iv: Iv, aad: &[u8]) -> Tag {
    chacha20_poly1305::simd128::encrypt(&key.0, msg_ctxt, iv.0, aad).into()
}

/// Fallback when simd128 is detected at runtime but it wasn't compiled.
/// We try to fall back to portable in this case.
#[cfg(not(simd128))]
fn encrypt_128(key: &Chacha20Key, msg_ctxt: &mut [u8], iv: Iv, aad: &[u8]) -> Tag {
    encrypt_32(key, msg_ctxt, iv, aad)
}

fn encrypt_32(key: &Chacha20Key, msg_ctxt: &mut [u8], iv: Iv, aad: &[u8]) -> Tag {
    chacha20_poly1305::encrypt(&key.0, msg_ctxt, iv.0, aad).into()
}

#[cfg(simd256)]
fn decrypt_256(
    key: &Chacha20Key,
    ctxt_msg: &mut [u8],
    iv: Iv,
    aad: &[u8],
    tag: &Tag,
) -> Result<(), DecryptError> {
    chacha20_poly1305::simd256::decrypt(&key.0, ctxt_msg, iv.0, aad, &tag.0)
        .map_err(|_| DecryptError::DecryptionFailed)
}

/// Fallback when simd256 is detected at runtime but it wasn't compiled.
/// We try to fall back to simd128 in this case.
#[cfg(not(simd256))]
fn decrypt_256(
    key: &Chacha20Key,
    ctxt_msg: &mut [u8],
    iv: Iv,
    aad: &[u8],
    tag: &Tag,
) -> Result<(), DecryptError> {
    decrypt_128(key, ctxt_msg, iv, aad, tag)
}

#[cfg(simd128)]
fn decrypt_128(
    key: &Chacha20Key,
    ctxt_msg: &mut [u8],
    iv: Iv,
    aad: &[u8],
    tag: &Tag,
) -> Result<(), DecryptError> {
    chacha20_poly1305::simd128::decrypt(&key.0, ctxt_msg, iv.0, aad, &tag.0)
        .map_err(|_| DecryptError::DecryptionFailed)
}

/// Fallback when simd128 is detected at runtime but it wasn't compiled.
/// We try to fall back to portable in this case.
#[cfg(not(simd128))]
fn decrypt_128(
    key: &Chacha20Key,
    ctxt_msg: &mut [u8],
    iv: Iv,
    aad: &[u8],
    tag: &Tag,
) -> Result<(), DecryptError> {
    decrypt_32(key, ctxt_msg, iv, aad, tag)
}

fn decrypt_32(
    key: &Chacha20Key,
    ctxt_msg: &mut [u8],
    iv: Iv,
    aad: &[u8],
    tag: &Tag,
) -> Result<(), DecryptError> {
    chacha20_poly1305::decrypt(&key.0, ctxt_msg, iv.0, aad, &tag.0)
        .map_err(|_| DecryptError::DecryptionFailed)
}

#[cfg(aes_ni)]
fn aes_encrypt_128(
    key: &Aes128Key,
    msg_ctxt: &mut [u8],
    iv: Iv,
    aad: &[u8],
) -> Result<Tag, EncryptError> {
    aesgcm::encrypt_128(&key.0, msg_ctxt, iv.0, aad)
        .map_err(|e| match e {
            aesgcm::Error::UnsupportedHardware => {
                EncryptError::InvalidArgument(InvalidArgumentError::UnsupportedAlgorithm)
            }
            aesgcm::Error::InvalidArgument => {
                EncryptError::InvalidArgument(InvalidArgumentError::Unknown)
            }
            aesgcm::Error::InvalidCiphertext => EncryptError::InternalError,
        })
        .map(|t| t.into())
}

#[cfg(not(aes_ni))]
fn aes_encrypt_128(_: &Aes128Key, _: &mut [u8], _v: Iv, _: &[u8]) -> Result<Tag, EncryptError> {
    Err(EncryptError::InvalidArgument(
        InvalidArgumentError::UnsupportedAlgorithm,
    ))
}

#[cfg(aes_ni)]
fn aes_encrypt_256(
    key: &Aes256Key,
    msg_ctxt: &mut [u8],
    iv: Iv,
    aad: &[u8],
) -> Result<Tag, EncryptError> {
    aesgcm::encrypt_256(&key.0, msg_ctxt, iv.0, aad)
        .map_err(|e| match e {
            aesgcm::Error::UnsupportedHardware => {
                EncryptError::InvalidArgument(InvalidArgumentError::UnsupportedAlgorithm)
            }
            aesgcm::Error::InvalidArgument => {
                EncryptError::InvalidArgument(InvalidArgumentError::Unknown)
            }
            aesgcm::Error::InvalidCiphertext => EncryptError::InternalError,
        })
        .map(|t| t.into())
}

#[cfg(not(aes_ni))]
fn aes_encrypt_256(_: &Aes256Key, _: &mut [u8], _: Iv, _: &[u8]) -> Result<Tag, EncryptError> {
    Err(EncryptError::InvalidArgument(
        InvalidArgumentError::UnsupportedAlgorithm,
    ))
}

#[cfg(aes_ni)]
fn aes_decrypt_128(
    key: &Aes128Key,
    ctxt_msg: &mut [u8],
    iv: Iv,
    aad: &[u8],
    tag: &Tag,
) -> Result<(), DecryptError> {
    aesgcm::decrypt_128(&key.0, ctxt_msg, iv.0, aad, &tag.0).map_err(|e| match e {
        aesgcm::Error::UnsupportedHardware => {
            DecryptError::InvalidArgument(InvalidArgumentError::UnsupportedAlgorithm)
        }
        aesgcm::Error::InvalidCiphertext => DecryptError::DecryptionFailed,
        aesgcm::Error::InvalidArgument => DecryptError::InternalError,
    })
}

#[cfg(not(aes_ni))]
fn aes_decrypt_128(
    _: &Aes128Key,
    _: &mut [u8],
    _: Iv,
    _: &[u8],
    _: &Tag,
) -> Result<(), DecryptError> {
    Err(DecryptError::InvalidArgument(
        InvalidArgumentError::UnsupportedAlgorithm,
    ))
}

#[cfg(aes_ni)]
fn aes_decrypt_256(
    key: &Aes256Key,
    ctxt_msg: &mut [u8],
    iv: Iv,
    aad: &[u8],
    tag: &Tag,
) -> Result<(), DecryptError> {
    aesgcm::decrypt_256(&key.0, ctxt_msg, iv.0, aad, &tag.0).map_err(|e| match e {
        aesgcm::Error::UnsupportedHardware => {
            DecryptError::InvalidArgument(InvalidArgumentError::UnsupportedAlgorithm)
        }
        aesgcm::Error::InvalidCiphertext => DecryptError::DecryptionFailed,
        aesgcm::Error::InvalidArgument => DecryptError::InternalError,
    })
}

#[cfg(not(aes_ni))]
fn aes_decrypt_256(
    _: &Aes256Key,
    _: &mut [u8],
    _: Iv,
    _: &[u8],
    _: &Tag,
) -> Result<(), DecryptError> {
    Err(DecryptError::InvalidArgument(
        InvalidArgumentError::UnsupportedAlgorithm,
    ))
}

/// AEAD encrypt the message in `msg_ctxt` with the `key`, `iv` and `aad`.
///
/// Returns the `Tag` and the ciphertext in `msg_ctxt`.
pub fn encrypt(key: &Key, msg_ctxt: &mut [u8], iv: Iv, aad: &[u8]) -> Result<Tag, EncryptError> {
    match key {
        Key::Aes128(key) => {
            if aes_ni_support() {
                aes_encrypt_128(key, msg_ctxt, iv, aad)
            } else {
                Err(EncryptError::InvalidArgument(
                    InvalidArgumentError::UnsupportedAlgorithm,
                ))
            }
        }
        Key::Aes256(key) => {
            if aes_ni_support() {
                aes_encrypt_256(key, msg_ctxt, iv, aad)
            } else {
                Err(EncryptError::InvalidArgument(
                    InvalidArgumentError::UnsupportedAlgorithm,
                ))
            }
        }
        Key::Chacha20Poly1305(key) => Ok(if simd256_support() {
            encrypt_256(key, msg_ctxt, iv, aad)
        } else if simd128_support() {
            encrypt_128(key, msg_ctxt, iv, aad)
        } else {
            encrypt_32(key, msg_ctxt, iv, aad)
        }),
    }
}

/// AEAD encrypt the message in `msg` with the `key`, `iv` and `aad`.
///
/// Returns the `Tag` and the ciphertext tuple.
pub fn encrypt_detached(
    key: &Key,
    msg: impl AsRef<[u8]>,
    iv: Iv,
    aad: impl AsRef<[u8]>,
) -> Result<(Tag, Vec<u8>), EncryptError> {
    let mut msg_ctxt = msg.as_ref().to_vec();
    let tag = encrypt(key, &mut msg_ctxt, iv, aad.as_ref())?;
    Ok((tag, msg_ctxt))
}

/// AEAD decrypt the ciphertext in `ctxt_msg` with the `key`, `iv`, `aad`, and
/// `tag`.
///
/// Returns the plaintext in `ctxt_msg` or an error if the decryption fails.
pub fn decrypt(
    key: &Key,
    ctxt_msg: &mut [u8],
    iv: Iv,
    aad: &[u8],
    tag: &Tag,
) -> Result<(), DecryptError> {
    match key {
        Key::Aes128(key) => {
            if aes_ni_support() {
                aes_decrypt_128(key, ctxt_msg, iv, aad, tag)
            } else {
                Err(DecryptError::InvalidArgument(
                    InvalidArgumentError::UnsupportedAlgorithm,
                ))
            }
        }
        Key::Aes256(key) => {
            if aes_ni_support() {
                aes_decrypt_256(key, ctxt_msg, iv, aad, tag)
            } else {
                Err(DecryptError::InvalidArgument(
                    InvalidArgumentError::UnsupportedAlgorithm,
                ))
            }
        }
        Key::Chacha20Poly1305(key) => {
            if simd256_support() {
                decrypt_256(key, ctxt_msg, iv, aad, tag)
            } else if simd128_support() {
                decrypt_128(key, ctxt_msg, iv, aad, tag)
            } else {
                decrypt_32(key, ctxt_msg, iv, aad, tag)
            }
        }
    }
}

/// AEAD decrypt the ciphertext in `ctxt` with the `key`, `iv`, `aad`, and
/// `tag`.
///
/// Returns the plaintext in `ctxt_msg` or an error if the decryption fails.
pub fn decrypt_detached(
    key: &Key,
    ctxt: impl AsRef<[u8]>,
    iv: Iv,
    aad: impl AsRef<[u8]>,
    tag: &Tag,
) -> Result<Vec<u8>, DecryptError> {
    let mut ctxt_msg = ctxt.as_ref().to_vec();
    decrypt(key, &mut ctxt_msg, iv, aad.as_ref(), tag)?;
    Ok(ctxt_msg)
}
