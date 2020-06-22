use crate::aes_gcm;

#[derive(Clone, Copy, Debug)]
pub enum Mode {
    AesGcm128 = 0x0001,
    AesGcm256 = 0x0002,
    ChaCha20Polz1305 = 0x0003,
}

#[derive(Debug)]
pub enum Error {
    OpenError,
}

pub(crate) trait AeadTrait {
    fn new() -> Self
    where
        Self: Sized;
    fn seal(&self, key: &[u8], nonce: &[u8], aad: &[u8], plain_txt: &[u8]) -> Vec<u8>;
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

pub struct Aead {
    mode: Mode,
    aead: Box<dyn AeadTrait>,
}

fn get_aead_object(mode: Mode) -> Box<dyn AeadTrait> {
    match mode {
        Mode::AesGcm128 => Box::new(aes_gcm::AesGcm128::new()),
        _ => panic!("AEAD {:?} is note implemented", mode),
    }
}

impl Aead {
    pub fn new(mode: Mode) -> Self {
        Self {
            mode: mode,
            aead: get_aead_object(mode),
        }
    }
    pub fn get_nk(&self) -> usize {
        self.aead.get_key_length()
    }
    pub fn get_nn(&self) -> usize {
        self.aead.get_nonce_length()
    }
    pub fn seal(&self, key: &[u8], nonce: &[u8], aad: &[u8], plain_txt: &[u8]) -> Vec<u8> {
        self.aead.seal(key, nonce, aad, plain_txt)
    }
    pub fn open(
        &self,
        key: &[u8],
        nonce: &[u8],
        aad: &[u8],
        cipher_txt: &[u8],
    ) -> Result<Vec<u8>, Error> {
        self.aead.open(key, nonce, aad, cipher_txt)
    }
}
