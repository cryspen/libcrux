#[cfg(feature = "serialization")]
pub(crate) use serde::{Deserialize, Serialize};

use crate::dh_kem;
use crate::kdf;
use crate::util;

/// KEM Modes
#[derive(PartialEq, Copy, Clone, Debug)]
#[cfg_attr(feature = "serialization", derive(Serialize, Deserialize))]
#[repr(u16)]
pub enum Mode {
    /// DH KEM on P256
    DhKemP256 = 0x0010,

    /// DH KEM on P384
    DhKemP384 = 0x0011,

    /// DH KEM on P521
    DhKemP521 = 0x0012,

    /// DH KEM on x25519
    DhKem25519 = 0x0020,

    /// DH KEM on x448
    DhKem448 = 0x0021,
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
            0x0010 => Ok(Mode::DhKemP256),
            0x0011 => Ok(Mode::DhKemP384),
            0x0012 => Ok(Mode::DhKemP521),
            0x0020 => Ok(Mode::DhKem25519),
            0x0021 => Ok(Mode::DhKem448),
            _ => Err(Error::UnknownMode),
        }
    }
}

/// KEM Errors
#[derive(Debug)]
pub enum Error {
    /// The KEM mode is unknown.
    UnknownMode,

    /// A cryptographic operation failed.
    CryptoError,

    /// Key generation error.
    KeyGenerationError,
}

// Map KEM to KDF according to spec.
fn kdf(mode: Mode) -> kdf::Mode {
    match mode {
        Mode::DhKemP256 => kdf::Mode::HkdfSha256,
        Mode::DhKemP384 => kdf::Mode::HkdfSha384,
        Mode::DhKemP521 => kdf::Mode::HkdfSha512,
        Mode::DhKem25519 => kdf::Mode::HkdfSha256,
        Mode::DhKem448 => kdf::Mode::HkdfSha512,
    }
}

pub(crate) type PrivateKey = Vec<u8>;
pub(crate) type PublicKey = Vec<u8>;

pub(crate) trait KemTrait: std::fmt::Debug + Send + Sync {
    fn new(kdf_id: kdf::Mode) -> Self
    where
        Self: Sized;

    fn key_gen(&self) -> Result<(Vec<u8>, Vec<u8>), Error>;
    fn derive_key_pair(
        &self,
        suite_id: &[u8],
        ikm: &[u8],
    ) -> Result<(PublicKey, PrivateKey), Error>;

    fn encaps(&self, pk_r: &[u8], suite_id: &[u8]) -> Result<(Vec<u8>, Vec<u8>), Error>;
    fn decaps(&self, enc: &[u8], sk_r: &[u8], suite_id: &[u8]) -> Result<Vec<u8>, Error>;
    fn auth_encaps(
        &self,
        pk_r: &[u8],
        sk_s: &[u8],
        suite_id: &[u8],
    ) -> Result<(Vec<u8>, Vec<u8>), Error>;
    fn auth_decaps(
        &self,
        enc: &[u8],
        sk_r: &[u8],
        pk_s: &[u8],
        suite_id: &[u8],
    ) -> Result<Vec<u8>, Error>;

    fn secret_len(&self) -> usize;
    fn encoded_pk_len(&self) -> usize;

    #[cfg(feature = "deterministic")]
    fn set_random(&mut self, r: &[u8]);
}

#[derive(Debug)]
pub struct Kem {
    mode: Mode,
    kem: Box<dyn KemTrait>,
}

#[cfg(feature = "serialization")]
impl Serialize for Kem {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::ser::Serializer,
    {
        self.mode.serialize(serializer)
    }
}

#[cfg(feature = "serialization")]
impl<'de> Deserialize<'de> for Kem {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let mode = Mode::deserialize(deserializer)?;
        Ok(Self::new(mode))
    }
}

impl std::fmt::Display for Kem {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", self.mode)
    }
}

fn kem_object(mode: Mode, kdf_id: kdf::Mode) -> Box<dyn KemTrait> {
    match mode {
        Mode::DhKem25519 => Box::new(dh_kem::DhKem::init(kdf_id, evercrypt::ecdh::Mode::X25519)),
        Mode::DhKemP256 => Box::new(dh_kem::DhKem::init(kdf_id, evercrypt::ecdh::Mode::P256)),
        _ => panic!("KEM {:?} is not implemented", mode),
    }
}

impl Kem {
    pub(crate) fn new(mode: Mode) -> Self {
        Self {
            mode,
            kem: kem_object(mode, kdf(mode)),
        }
    }

    #[inline]
    fn ciphersuite(&self) -> Vec<u8> {
        util::concat(&[b"KEM", &(self.mode as u16).to_be_bytes()])
    }

    pub(crate) fn encaps(&self, pk_r: &[u8]) -> Result<(Vec<u8>, Vec<u8>), Error> {
        self.kem.encaps(pk_r, &self.ciphersuite())
    }
    pub(crate) fn decaps(&self, enc: &[u8], sk_r: &[u8]) -> Result<Vec<u8>, Error> {
        self.kem.decaps(enc, sk_r, &self.ciphersuite())
    }
    pub(crate) fn auth_encaps(
        &self,
        pk_r: &[u8],
        sk_s: &[u8],
    ) -> Result<(Vec<u8>, Vec<u8>), Error> {
        self.kem.auth_encaps(pk_r, sk_s, &self.ciphersuite())
    }
    pub(crate) fn auth_decaps(
        &self,
        enc: &[u8],
        sk_r: &[u8],
        pk_s: &[u8],
    ) -> Result<Vec<u8>, Error> {
        self.kem.auth_decaps(enc, sk_r, pk_s, &self.ciphersuite())
    }
    pub(crate) fn key_gen(&self) -> Result<(Vec<u8>, Vec<u8>), Error> {
        self.kem.key_gen()
    }

    /// Derive key pair from the input key material `ikm`.
    ///
    /// Returns (PublicKey, PrivateKey).
    pub(crate) fn derive_key_pair(&self, ikm: &[u8]) -> Result<(PublicKey, PrivateKey), Error> {
        self.kem.derive_key_pair(&self.ciphersuite(), ikm)
    }

    #[cfg(feature = "deterministic")]
    pub(crate) fn set_random(&mut self, r: &[u8]) {
        self.kem.set_random(r);
    }
}
