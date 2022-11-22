use crate::hacl;

pub mod chacha20poly1305;
use chacha20poly1305::*;

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
}

pub type Aes128Key = [u8; Algorithm::key_size(Algorithm::Aes128Gcm)];
pub type Aes256Key = [u8; Algorithm::key_size(Algorithm::Aes256Gcm)];
pub type Chacha20Key = [u8; Algorithm::key_size(Algorithm::Chacha20Poly1305)];

pub enum Key {
    Aes128(Aes128Key),
    Aes256(Aes256Key),
    Chacha20Poly1305(Chacha20Key),
}

pub type Tag = [u8; 16];
pub type Iv = [u8; 12];

pub fn encrypt(
    algorithm: Algorithm,
    key: &Key,
    msg_ctxt: &mut [u8],
    iv: &Iv,
    aad: &[u8],
) -> Result<Tag, &'static str> {
    match algorithm {
        Algorithm::Aes128Gcm => unimplemented!(),
        Algorithm::Aes256Gcm => unimplemented!(),
        Algorithm::Chacha20Poly1305 => {
            let key = match key {
                Key::Aes128(_) | Key::Aes256(_) => return Err("Invalid key"),
                Key::Chacha20Poly1305(k) => k,
            };
            Ok(hacl::chacha20poly1305::encrypt(key, msg_ctxt, iv, aad))
        }
    }
}

pub fn decrypt(
    algorithm: Algorithm,
    key: &Key,
    ctxt_msg: &mut [u8],
    iv: &Iv,
    aad: &[u8],
    tag: &Tag,
) -> Result<(), &'static str> {
    match algorithm {
        Algorithm::Aes128Gcm => unimplemented!(),
        Algorithm::Aes256Gcm => unimplemented!(),
        Algorithm::Chacha20Poly1305 => {
            let key = match key {
                Key::Aes128(_) | Key::Aes256(_) => return Err("Invalid key"),
                Key::Chacha20Poly1305(k) => k,
            };
            hacl::chacha20poly1305::decrypt(key, ctxt_msg, iv, aad, tag)
        }
    }
}
