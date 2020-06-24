use aead::{Aead, NewAead, Payload};
use chacha20poly1305::ChaCha20Poly1305 as chacha;

use crate::aead::{AeadTrait, Error};

pub(crate) struct ChaCha20Poly1305 {}

impl AeadTrait for ChaCha20Poly1305 {
    fn new() -> Self {
        Self {}
    }
    fn seal(&self, key: &[u8], nonce: &[u8], aad: &[u8], plain_txt: &[u8]) -> Vec<u8> {
        chacha::new(key.into())
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
        match chacha::new(key.into()).decrypt(
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
        32
    }
    fn get_nonce_length(&self) -> usize {
        12
    }
}
