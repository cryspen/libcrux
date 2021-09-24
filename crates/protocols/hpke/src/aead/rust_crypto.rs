use crate::aead::{AeadTrait, Error};
use aes_gcm::{Aes128Gcm as RC_Aes128Gcm, Aes256Gcm as RC_Aes256Gcm};
use chacha20poly1305::{
    aead::{Aead, Error as AeadError, NewAead, Payload},
    ChaCha20Poly1305 as RC_ChaCha20Poly1305,
};

impl From<AeadError> for Error {
    fn from(e: AeadError) -> Self {
        Self::CryptoLibError(format!("AEAD error {:?}", e))
    }
}

macro_rules! implement_aead {
    ($name:ident, $algorithm:ident, $key_len:expr) => {
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
                msg: &[u8],
            ) -> Result<Vec<u8>, Error> {
                if nonce.len() != 12 {
                    return Err(Error::InvalidNonce);
                }

                let cipher = $algorithm::new(key.into());
                cipher
                    .encrypt(nonce.into(), Payload { msg, aad })
                    .map_err(|e| e.into())
            }
            fn open(
                &self,
                key: &[u8],
                nonce: &[u8],
                aad: &[u8],
                msg: &[u8],
            ) -> Result<Vec<u8>, Error> {
                let nonce_length = self.nonce_length();
                if nonce.len() != nonce_length {
                    return Err(Error::InvalidNonce);
                }
                let tag_length = self.tag_length();
                if msg.len() <= tag_length {
                    return Err(Error::InvalidCiphertext);
                }

                let cipher = $algorithm::new(key.into());

                cipher
                    .decrypt(nonce.into(), Payload { msg, aad })
                    .map_err(|_| Error::OpenError)
            }
            fn key_length(&self) -> usize {
                $key_len
            }
            fn nonce_length(&self) -> usize {
                12
            }
            fn tag_length(&self) -> usize {
                16
            }
        }
    };
}

implement_aead!(AesGcm128, RC_Aes128Gcm, 16);
implement_aead!(AesGcm256, RC_Aes256Gcm, 32);
implement_aead!(ChaCha20Poly1305, RC_ChaCha20Poly1305, 32);
