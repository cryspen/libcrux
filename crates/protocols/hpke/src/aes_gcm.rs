use aead::{Aead, NewAead, Payload};
use aes_gcm::Aes128Gcm;

use crate::aead::{AeadTrait, Error};

pub(crate) struct AesGcm128 {}

impl AeadTrait for AesGcm128 {
    fn new() -> Self {
        Self {}
    }
    fn seal(&self, key: &[u8], nonce: &[u8], aad: &[u8], plain_txt: &[u8]) -> Vec<u8> {
        // TODO: Only works with 12 byte nonce!
        Aes128Gcm::new(key.into())
            .encrypt(
                nonce.into(),
                Payload {
                    msg: plain_txt,
                    aad: aad,
                },
            )
            .unwrap()
    }
    fn open(
        &self,
        key: &[u8],
        nonce: &[u8],
        aad: &[u8],
        cipher_txt: &[u8],
    ) -> Result<Vec<u8>, Error> {
        match Aes128Gcm::new(key.into()).decrypt(
            nonce.into(),
            Payload {
                msg: cipher_txt,
                aad: aad,
            },
        ) {
            Ok(p) => Ok(p),
            Err(_) => Err(Error::OpenError),
        }
    }
    fn get_key_length(&self) -> usize {
        16
    }
    fn get_nonce_length(&self) -> usize {
        12
    }
}
