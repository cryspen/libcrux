use crate::dh_kem;
use crate::kdf;
use crate::util;

#[derive(PartialEq, Copy, Clone, Debug)]
#[repr(u16)]
pub enum Mode {
    DhKemP256 = 0x0010,
    DhKemP384 = 0x0011,
    DhKemP521 = 0x0012,
    DhKem25519 = 0x0020,
    DhKem448 = 0x0021,
}

impl From<u16> for Mode {
    fn from(x: u16) -> Mode {
        match x {
            0x0010 => Mode::DhKemP256,
            0x0011 => Mode::DhKemP384,
            0x0012 => Mode::DhKemP521,
            0x0020 => Mode::DhKem25519,
            0x0021 => Mode::DhKem448,
            _ => panic!("Unknown KEM Mode {}", x),
        }
    }
}

// Map KEM to KDF according to spec.
fn get_kdf(mode: Mode) -> kdf::Mode {
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

pub(crate) trait KemTrait: std::fmt::Debug {
    fn new(kdf_id: kdf::Mode) -> Self
    where
        Self: Sized;

    fn key_gen(&self) -> (Vec<u8>, Vec<u8>);
    fn derive_key_pair(&self, suite_id: &[u8], ikm: &[u8]) -> (PublicKey, PrivateKey);

    fn encaps(&self, pk_r: &[u8], suite_id: &[u8]) -> (Vec<u8>, Vec<u8>);
    fn decaps(&self, enc: &[u8], sk_r: &[u8], suite_id: &[u8]) -> Vec<u8>;
    fn auth_encaps(&self, pk_r: &[u8], sk_s: &[u8], suite_id: &[u8]) -> (Vec<u8>, Vec<u8>);
    fn auth_decaps(&self, enc: &[u8], sk_r: &[u8], pk_s: &[u8], suite_id: &[u8]) -> Vec<u8>;

    fn get_secret_len(&self) -> usize;
    fn get_encoded_pk_len(&self) -> usize;
}

#[derive(Debug)]
pub struct Kem {
    mode: Mode,
    kem: Box<dyn KemTrait>,
}

fn get_kem_object(mode: Mode, kdf_id: kdf::Mode) -> Box<dyn KemTrait> {
    match mode {
        Mode::DhKem25519 => Box::new(dh_kem::DhKem::init(kdf_id, evercrypt::ecdh::Mode::X25519)),
        Mode::DhKemP256 => Box::new(dh_kem::DhKem::init(kdf_id, evercrypt::ecdh::Mode::P256)),
        _ => panic!("KEM {:?} is note implemented", mode),
    }
}

impl Kem {
    pub(crate) fn new(mode: Mode) -> Self {
        Self {
            mode,
            kem: get_kem_object(mode, get_kdf(mode)),
        }
    }

    #[inline]
    fn get_ciphersuite(&self) -> Vec<u8> {
        util::concat(&[b"KEM", &(self.mode as u16).to_be_bytes()])
    }

    pub(crate) fn encaps(&self, pk_r: &[u8]) -> (Vec<u8>, Vec<u8>) {
        self.kem.encaps(pk_r, &self.get_ciphersuite())
    }
    pub(crate) fn decaps(&self, enc: &[u8], sk_r: &[u8]) -> Vec<u8> {
        self.kem.decaps(enc, sk_r, &self.get_ciphersuite())
    }
    pub(crate) fn auth_encaps(&self, pk_r: &[u8], sk_s: &[u8]) -> (Vec<u8>, Vec<u8>) {
        self.kem.auth_encaps(pk_r, sk_s, &self.get_ciphersuite())
    }
    pub(crate) fn auth_decaps(&self, enc: &[u8], sk_r: &[u8], pk_s: &[u8]) -> Vec<u8> {
        self.kem
            .auth_decaps(enc, sk_r, pk_s, &self.get_ciphersuite())
    }
    pub(crate) fn key_gen(&self) -> (Vec<u8>, Vec<u8>) {
        self.kem.key_gen()
    }

    /// Derive key pair from the input key material `ikm`.
    ///
    /// Returns (PublicKey, PrivateKey).
    pub(crate) fn derive_key_pair(&self, ikm: &[u8]) -> (PublicKey, PrivateKey) {
        self.kem.derive_key_pair(&self.get_ciphersuite(), ikm)
    }
}
