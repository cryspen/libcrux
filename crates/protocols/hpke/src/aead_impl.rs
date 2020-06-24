use aead::{Aead, NewAead, Payload};
use aes_gcm::{Aes128Gcm, Aes256Gcm};
use chacha20poly1305::ChaCha20Poly1305 as chacha;

use crate::aead::{AeadTrait, Error};

macro_rules! implement_aead {
    ($name:ident, $base:ident, $key_length:literal) => {
        pub(crate) struct $name {}

        impl AeadTrait for $name {
            fn new() -> Self {
                Self {}
            }
            fn seal(&self, key: &[u8], nonce: &[u8], aad: &[u8], plain_txt: &[u8]) -> Vec<u8> {
                // XXX: Only works with 12 byte nonce!
                $base::new(key.into())
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
                match $base::new(key.into()).decrypt(
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
                $key_length
            }
            fn get_nonce_length(&self) -> usize {
                12
            }
        }
    };
}

implement_aead!(AesGcm128, Aes128Gcm, 16);
implement_aead!(AesGcm256, Aes256Gcm, 32);
implement_aead!(ChaCha20Poly1305, chacha, 32);
