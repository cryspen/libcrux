//! Libcrux AEAD trait

#[cfg(feature = "rand")]
use rand::CryptoRng;

/// AEAD Error
#[derive(Debug, PartialEq, Eq)]
pub enum Error {
    KeyGen,
    Encrypt,
    Decrypt,
}

pub trait Aead {
    type Key;
    type Tag;
    type Nonce;

    #[cfg(feature = "rand")]
    fn key_gen(key: &mut Self::Key, rng: &mut impl CryptoRng) -> Result<(), Error>;

    fn encrypt(
        ciphertext: &mut [u8],
        tag: &mut Self::Tag,
        key: &Self::Key,
        nonce: &Self::Nonce,
        aad: &[u8],
        plaintext: &[u8],
    ) -> Result<(), Error>;

    fn decrypt(
        plaintext: &mut [u8],
        key: &Self::Key,
        nonce: &Self::Nonce,
        aad: &[u8],
        ciphertext: &[u8],
        tag: &Self::Tag,
    ) -> Result<(), Error>;
}
