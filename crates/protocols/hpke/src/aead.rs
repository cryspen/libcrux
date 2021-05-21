#[cfg(feature = "serialization")]
pub(crate) use serde::{Deserialize, Serialize};

use crate::aead_impl::*;

use std::fmt::Debug;

/// AEAD modes.
#[derive(Clone, Copy, Debug, PartialEq)]
#[cfg_attr(feature = "serialization", derive(Serialize, Deserialize))]
#[repr(u16)]
pub enum Mode {
    /// AES GCM 128
    AesGcm128 = 0x0001,

    /// AES GCM 256
    AesGcm256 = 0x0002,

    /// ChaCha20 Poly1305
    ChaCha20Poly1305 = 0x0003,

    /// Export-only
    Export = 0xFFFF,
}

impl std::fmt::Display for Mode {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl std::convert::TryFrom<u16> for Mode {
    type Error = Error;
    fn try_from(x: u16) -> Result<Mode, Error> {
        match x {
            0x0001 => Ok(Mode::AesGcm128),
            0x0002 => Ok(Mode::AesGcm256),
            0x0003 => Ok(Mode::ChaCha20Poly1305),
            0xFFFF => Ok(Mode::Export),
            _ => Err(Error::UnknownMode),
        }
    }
}

/// AEAD Errors
#[derive(Debug)]
#[cfg_attr(feature = "serialization", derive(Serialize, Deserialize))]
pub enum Error {
    /// Error opening a ciphertext
    OpenError,

    /// Invalid configuration
    InvalidConfig,

    /// Invalid Nonce
    InvalidNonce,

    /// Invalid Ciphertext
    InvalidCiphertext,

    /// Unknown AEAD mode
    UnknownMode,

    /// Error from the crypto library
    CryptoLibError(String),
}

pub(crate) trait AeadTrait: Debug + Send + Sync {
    fn new() -> Self
    where
        Self: Sized;
    fn seal(
        &self,
        key: &[u8],
        nonce: &[u8],
        aad: &[u8],
        plain_txt: &[u8],
    ) -> Result<Vec<u8>, Error>;
    fn open(
        &self,
        key: &[u8],
        nonce: &[u8],
        aad: &[u8],
        cipher_txt: &[u8],
    ) -> Result<Vec<u8>, Error>;
    fn key_length(&self) -> usize;
    fn nonce_length(&self) -> usize;
    fn tag_length(&self) -> usize;
}

#[derive(Debug)]
pub struct Aead {
    mode: Mode,
    aead: Box<dyn AeadTrait>,
}

#[cfg(feature = "serialization")]
impl Serialize for Aead {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::ser::Serializer,
    {
        self.mode.serialize(serializer)
    }
}

#[cfg(feature = "serialization")]
impl<'de> Deserialize<'de> for Aead {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let mode = Mode::deserialize(deserializer)?;
        Ok(Self::new(mode))
    }
}

fn aead_object(mode: Mode) -> Box<dyn AeadTrait> {
    match mode {
        Mode::AesGcm128 => Box::new(AesGcm128::new()),
        Mode::AesGcm256 => Box::new(AesGcm256::new()),
        Mode::ChaCha20Poly1305 => Box::new(ChaCha20Poly1305::new()),
        Mode::Export => panic!("Exporter only interface is not implemented yet."),
    }
}

impl Aead {
    /// Create a new Aead with the given `mode`.
    pub fn new(mode: Mode) -> Self {
        Self {
            mode,
            aead: aead_object(mode),
        }
    }

    /// Get the key length of the used scheme.
    pub fn nk(&self) -> usize {
        self.aead.key_length()
    }

    /// Get the nonce length of the used scheme.
    pub fn nn(&self) -> usize {
        self.aead.nonce_length()
    }

    /// Encrypt the given `plain_txt` with the `aad`, `key`, and `nonce`. All
    /// values are passed in as byte slices.
    ///
    /// The function returns a `Result`.
    /// A byte vector with the cipher text and tag concatenated if successful.
    /// Or an `Error` if any of the parameters are invalid.
    pub fn seal(
        &self,
        key: &[u8],
        nonce: &[u8],
        aad: &[u8],
        plain_txt: &[u8],
    ) -> Result<Vec<u8>, Error> {
        self.aead.seal(key, nonce, aad, plain_txt)
    }

    /// Decrypt a given `cipher_txt` with the `aad`, `key`, and `nonce`. All
    /// values are passed in as byte slices.
    ///
    /// The function returns a `Result`.
    /// A byte vector with the plaintext.
    /// Or an `Error` if any of the parameters are invalid or the opening fails.
    pub fn open(
        &self,
        key: &[u8],
        nonce: &[u8],
        aad: &[u8],
        cipher_txt: &[u8],
    ) -> Result<Vec<u8>, Error> {
        self.aead.open(key, nonce, aad, cipher_txt)
    }

    /// Get the message limit for this AEAD.
    /// If the message limit is reached, the key must be rotated.
    pub fn message_limit(&self) -> u32 {
        (1 << self.nn()) - 1
    }
}
