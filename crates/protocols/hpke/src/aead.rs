use crate::aead_impl::*;

use std::fmt::Debug;

/// AEAD modes.
#[derive(Clone, Copy, Debug, PartialEq)]
#[repr(u16)]
pub enum Mode {
    /// AES GCM 128
    AesGcm128 = 0x0001,

    /// AES GCM 256
    AesGcm256 = 0x0002,

    /// ChaCha20 Poly1305
    ChaCha20Poly1305 = 0x0003,
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
            _ => Err(Error::UnknownMode),
        }
    }
}

/// AEAD Errors
#[derive(Debug)]
pub enum Error {
    /// Error opening a ciphertext
    OpenError,

    /// Invalid configuration
    InvalidConfig,

    /// Invalid Nonce
    InvalidNonce,

    /// Unknown AEAD mode
    UnknownMode,
}

pub(crate) trait AeadTrait: Debug {
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
    fn get_key_length(&self) -> usize;
    fn get_nonce_length(&self) -> usize;
}

#[derive(Debug)]
pub struct Aead {
    aead: Box<dyn AeadTrait>,
}

fn get_aead_object(mode: Mode) -> Box<dyn AeadTrait> {
    match mode {
        Mode::AesGcm128 => Box::new(AesGcm128::new()),
        Mode::AesGcm256 => Box::new(AesGcm256::new()),
        Mode::ChaCha20Poly1305 => Box::new(ChaCha20Poly1305::new()),
    }
}

impl Aead {
    pub fn new(mode: Mode) -> Self {
        Self {
            aead: get_aead_object(mode),
        }
    }
    pub fn get_nk(&self) -> usize {
        self.aead.get_key_length()
    }
    pub fn get_nn(&self) -> usize {
        self.aead.get_nonce_length()
    }
    pub fn seal(
        &self,
        key: &[u8],
        nonce: &[u8],
        aad: &[u8],
        plain_txt: &[u8],
    ) -> Result<Vec<u8>, Error> {
        println!("seal key: {:?}", key);
        self.aead.seal(key, nonce, aad, plain_txt)
    }
    pub fn open(
        &self,
        key: &[u8],
        nonce: &[u8],
        aad: &[u8],
        cipher_txt: &[u8],
    ) -> Result<Vec<u8>, Error> {
        println!("open key: {:?}", key);
        self.aead.open(key, nonce, aad, cipher_txt)
    }
}
