use aead::{Aead, NewAead, Payload};
use aes_gcm::{Aes128Gcm, Aes256Gcm};

use crate::aead::{AeadTrait, Error};

macro_rules! implement_aes {
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

implement_aes!(AesGcm128, Aes128Gcm, 16);
implement_aes!(AesGcm256, Aes256Gcm, 32);
