use crate::dh_kem;
use crate::kdf;

#[derive(PartialEq, Copy, Clone, Debug)]
pub enum Mode {
    DhKemP256 = 0x0010,
    DhKemP384 = 0x0011,
    DhKemP521 = 0x0012,
    DhKem25519 = 0x0020,
    DhKem448 = 0x0021,
}

fn get_kdf(mode: Mode) -> kdf::Mode {
    match mode {
        Mode::DhKemP256 => kdf::Mode::HkdfSha256,
        Mode::DhKemP384 => kdf::Mode::HkdfSha384,
        Mode::DhKemP521 => kdf::Mode::HkdfSha512,
        Mode::DhKem25519 => kdf::Mode::HkdfSha256,
        Mode::DhKem448 => kdf::Mode::HkdfSha512,
    }
}

pub(crate) trait KemTrait {
    fn new() -> Self
    where
        Self: Sized;

    fn encaps(&self, pk_r: &[u8]) -> (Vec<u8>, Vec<u8>);
    fn decaps(&self, enc: &[u8], sk_r: &[u8]) -> Vec<u8>;
    fn auth_encaps(&self, pk_r: &[u8], sk_s: &[u8]) -> (Vec<u8>, Vec<u8>);
    fn auth_decaps(&self, enc: &[u8], sk_r: &[u8], pk_s: &[u8]) -> Vec<u8>;

    fn get_secret_len(&self) -> usize;
    fn get_seed_len(&self) -> usize;
    fn get_encoded_pk_len(&self) -> usize;
}

pub struct Kem {
    mode: Mode,
    kem: Box<dyn KemTrait>,
}

fn get_kem_object(mode: Mode) -> Box<dyn KemTrait> {
    match mode {
        Mode::DhKem25519 => Box::new(dh_kem::X25519Kem::new()),
        _ => panic!("KEM {:?} is note implemented", mode),
    }
}

impl Kem {
    pub fn new(mode: Mode) -> Self {
        Self {
            mode: mode,
            kem: get_kem_object(mode),
        }
    }

    pub fn encaps(&self, pk_r: &[u8]) -> (Vec<u8>, Vec<u8>) {
        self.kem.encaps(pk_r)
    }
    pub fn decaps(&self, enc: &[u8], sk_r: &[u8]) -> Vec<u8> {
        self.kem.decaps(enc, sk_r)
    }
    pub fn auth_encaps(&self, pk_r: &[u8], sk_s: &[u8]) -> (Vec<u8>, Vec<u8>) {
        self.kem.auth_encaps(pk_r, sk_s)
    }
    pub fn auth_decaps(&self, enc: &[u8], sk_r: &[u8], pk_s: &[u8]) -> Vec<u8> {
        self.kem.auth_decaps(enc, sk_r, pk_s)
    }
}
