use evercrypt::aead::{Aead, Mode as EvercryptMode};

use crate::aead::{AeadTrait, Error};

macro_rules! implement_aead {
    ($name:ident, $algorithm:expr, $key_length:literal) => {
        pub(crate) struct $name {}

        impl AeadTrait for $name {
            fn new() -> Self {
                Self {}
            }
            fn seal(&self, key: &[u8], nonce: &[u8], aad: &[u8], plain_txt: &[u8]) -> Vec<u8> {
                // XXX: Only works with 12 byte nonce!
                // TODO: fix unwrap
                let cipher = Aead::new($algorithm, &key).unwrap();
                let (mut ctxt, tag) = cipher.encrypt(&plain_txt, &nonce, &aad).unwrap();
                ctxt.extend(tag);
                ctxt
            }
            fn open(
                &self,
                key: &[u8],
                nonce: &[u8],
                aad: &[u8],
                cipher_txt: &[u8],
            ) -> Result<Vec<u8>, Error> {
                let cipher = match Aead::new($algorithm, &key) {
                    Ok(c) => c,
                    Err(_) => return Err(Error::InvalidConfig),
                };
                match cipher.decrypt(
                    &cipher_txt[..cipher_txt.len() - 16],
                    &cipher_txt[cipher_txt.len() - 16..],
                    &nonce,
                    &aad,
                ) {
                    Ok(m) => Ok(m),
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

implement_aead!(AesGcm128, EvercryptMode::Aes128Gcm, 16);
implement_aead!(AesGcm256, EvercryptMode::Aes256Gcm, 32);
implement_aead!(ChaCha20Poly1305, EvercryptMode::Chacha20Poly1305, 32);
