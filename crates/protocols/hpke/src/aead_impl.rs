use evercrypt::prelude::*;

use crate::aead::{AeadTrait, Error};

impl From<evercrypt::aead::Error> for Error {
    fn from(e: evercrypt::aead::Error) -> Self {
        Self::CryptoLibError(format!("Evercrypt error {:?}", e))
    }
}

macro_rules! implement_aead {
    ($name:ident, $algorithm:expr) => {
        #[derive(Debug)]
        pub(crate) struct $name {}

        impl AeadTrait for $name {
            fn new() -> Self {
                Self {}
            }
            fn seal(
                &self,
                key: &[u8],
                nonce: &[u8],
                aad: &[u8],
                plain_txt: &[u8],
            ) -> Result<Vec<u8>, Error> {
                if nonce.len() != 12 {
                    return Err(Error::InvalidNonce);
                }

                let cipher = match Aead::new($algorithm, &key) {
                    Ok(c) => c,
                    Err(_) => return Err(Error::InvalidConfig),
                };

                let (mut ctxt, tag) = cipher.encrypt(&plain_txt, &nonce, &aad)?;
                ctxt.extend(tag.to_vec());
                Ok(ctxt)
            }
            fn open(
                &self,
                key: &[u8],
                nonce: &[u8],
                aad: &[u8],
                cipher_txt: &[u8],
            ) -> Result<Vec<u8>, Error> {
                let nonce_length = self.nonce_length();
                if nonce.len() != nonce_length {
                    return Err(Error::InvalidNonce);
                }
                let tag_length = self.tag_length();
                if cipher_txt.len() <= tag_length {
                    return Err(Error::InvalidCiphertext);
                }

                let cipher = match Aead::new($algorithm, &key) {
                    Ok(c) => c,
                    Err(_) => return Err(Error::InvalidConfig),
                };

                match cipher.decrypt(
                    &cipher_txt[..cipher_txt.len() - tag_length],
                    &cipher_txt[cipher_txt.len() - tag_length..],
                    &nonce,
                    &aad,
                ) {
                    Ok(m) => Ok(m),
                    Err(_) => Err(Error::OpenError),
                }
            }
            fn key_length(&self) -> usize {
                aead_key_size($algorithm)
            }
            fn nonce_length(&self) -> usize {
                aead_nonce_size($algorithm)
            }
            fn tag_length(&self) -> usize {
                aead_tag_size($algorithm)
            }
        }
    };
}

implement_aead!(AesGcm128, AeadMode::Aes128Gcm);
implement_aead!(AesGcm256, AeadMode::Aes256Gcm);
implement_aead!(ChaCha20Poly1305, AeadMode::Chacha20Poly1305);
