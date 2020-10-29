use evercrypt::prelude::*;

use crate::aead::{AeadTrait, Error};

macro_rules! implement_aead {
    ($name:ident, $algorithm:expr, $key_length:literal) => {
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

                let mut nonce_array = [0u8; 12];
                nonce_array.clone_from_slice(nonce);

                let (mut ctxt, tag) = cipher.encrypt(&plain_txt, &nonce_array, &aad).unwrap();
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
                if nonce.len() != 12 {
                    return Err(Error::InvalidNonce);
                }

                let cipher = match Aead::new($algorithm, &key) {
                    Ok(c) => c,
                    Err(_) => return Err(Error::InvalidConfig),
                };

                let mut nonce_array = [0u8; 12];
                nonce_array.clone_from_slice(nonce);

                match cipher.decrypt(
                    &cipher_txt[..cipher_txt.len() - 16],
                    &cipher_txt[cipher_txt.len() - 16..],
                    &nonce_array,
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

implement_aead!(AesGcm128, AeadMode::Aes128Gcm, 16);
implement_aead!(AesGcm256, AeadMode::Aes256Gcm, 32);
implement_aead!(ChaCha20Poly1305, AeadMode::Chacha20Poly1305, 32);
