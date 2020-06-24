use crate::dh_kem;

#[derive(PartialEq, Copy, Clone, Debug)]
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
