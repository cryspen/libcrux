#[cfg(any(feature = "chacha20poly1305", feature = "xchacha20poly1305"))]
use libcrux_traits::{
    aead,
    aead::typed_refs::{DecryptError, EncryptError, Multiplexes},
    libcrux_secrets::U8,
};

/// A multiplexed AEAD, allowing algorithm selection at run time.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Aead {
    /// The ChaCha20Poly1305 AEAD algorithm.
    #[cfg(feature = "chacha20poly1305")]
    ChaCha20Poly1305,

    /// The XChaCha20Poly1305 AEAD algorithm.
    #[cfg(feature = "xchacha20poly1305")]
    XChaCha20Poly1305,
}

/// A reference to a multiplexed AEAD key.
#[cfg(any(feature = "chacha20poly1305", feature = "xchacha20poly1305"))]
pub type KeyRef<'a> = aead::typed_refs::KeyRef<'a, Aead>;
/// A reference to a multiplexed AEAD tag.
#[cfg(any(feature = "chacha20poly1305", feature = "xchacha20poly1305"))]
pub type TagRef<'a> = aead::typed_refs::TagRef<'a, Aead>;
/// A mutable reference to a multiplexed AEAD tag.
#[cfg(any(feature = "chacha20poly1305", feature = "xchacha20poly1305"))]
pub type TagMut<'a> = aead::typed_refs::TagMut<'a, Aead>;
/// A reference to a multiplexed AEAD nonce.
#[cfg(any(feature = "chacha20poly1305", feature = "xchacha20poly1305"))]
pub type NonceRef<'a> = aead::typed_refs::NonceRef<'a, Aead>;

#[cfg(feature = "chacha20poly1305")]
impl Multiplexes<crate::chacha20poly1305::ChaCha20Poly1305> for Aead {
    fn mux_algo(&self) -> Option<crate::chacha20poly1305::ChaCha20Poly1305> {
        matches!(self, Self::ChaCha20Poly1305).then_some(crate::chacha20poly1305::ChaCha20Poly1305)
    }
    fn wrap_algo(_algo: crate::chacha20poly1305::ChaCha20Poly1305) -> Self {
        Self::ChaCha20Poly1305
    }
}

#[cfg(feature = "xchacha20poly1305")]
impl Multiplexes<crate::xchacha20poly1305::XChaCha20Poly1305> for Aead {
    fn mux_algo(&self) -> Option<crate::xchacha20poly1305::XChaCha20Poly1305> {
        matches!(self, Self::XChaCha20Poly1305)
            .then_some(crate::xchacha20poly1305::XChaCha20Poly1305)
    }
    fn wrap_algo(_algo: crate::xchacha20poly1305::XChaCha20Poly1305) -> Self {
        Self::XChaCha20Poly1305
    }
}

#[cfg(any(feature = "chacha20poly1305", feature = "xchacha20poly1305"))]
impl aead::typed_refs::Aead for Aead {
    fn key_len(&self) -> usize {
        32
    }

    fn tag_len(&self) -> usize {
        16
    }

    fn nonce_len(&self) -> usize {
        match *self {
            #[cfg(feature = "chacha20poly1305")]
            Aead::ChaCha20Poly1305 => 12,
            #[cfg(feature = "xchacha20poly1305")]
            Aead::XChaCha20Poly1305 => 24,
        }
    }

    fn encrypt<'a>(
        &self,
        ciphertext: &mut [u8],
        tag: TagMut<'a>,
        key: KeyRef<'a>,
        nonce: NonceRef<'a>,
        aad: &[u8],
        plaintext: &[U8],
    ) -> Result<(), aead::typed_refs::EncryptError> {
        match *self {
            #[cfg(feature = "chacha20poly1305")]
            Aead::ChaCha20Poly1305 => {
                use crate::chacha20poly1305::ChaCha20Poly1305;

                let key = Self::mux_key(key).ok_or(EncryptError::WrongKey)?;
                let tag = Self::mux_tag_mut(tag).ok_or(EncryptError::WrongTag)?;
                let nonce = Self::mux_nonce(nonce).ok_or(EncryptError::WrongNonce)?;
                ChaCha20Poly1305.encrypt(ciphertext, tag, key, nonce, aad, plaintext)
            }
            #[cfg(feature = "xchacha20poly1305")]
            Aead::XChaCha20Poly1305 => {
                use crate::xchacha20poly1305::XChaCha20Poly1305;

                let key = Self::mux_key(key).ok_or(EncryptError::WrongKey)?;
                let tag = Self::mux_tag_mut(tag).ok_or(EncryptError::WrongTag)?;
                let nonce = Self::mux_nonce(nonce).ok_or(EncryptError::WrongNonce)?;
                XChaCha20Poly1305.encrypt(ciphertext, tag, key, nonce, aad, plaintext)
            }
        }
    }

    fn decrypt<'a>(
        &self,
        plaintext: &mut [U8],
        key: KeyRef<'a>,
        nonce: NonceRef<'a>,
        aad: &[u8],
        ciphertext: &[u8],
        tag: TagRef<'a>,
    ) -> Result<(), aead::typed_refs::DecryptError> {
        match *self {
            #[cfg(feature = "chacha20poly1305")]
            Aead::ChaCha20Poly1305 => {
                use crate::chacha20poly1305::ChaCha20Poly1305;

                let key = Self::mux_key(key).ok_or(DecryptError::WrongKey)?;
                let tag = Self::mux_tag(tag).ok_or(DecryptError::WrongTag)?;
                let nonce = Self::mux_nonce(nonce).ok_or(DecryptError::WrongNonce)?;
                ChaCha20Poly1305.decrypt(plaintext, key, nonce, aad, ciphertext, tag)
            }
            #[cfg(feature = "xchacha20poly1305")]
            Aead::XChaCha20Poly1305 => {
                use crate::xchacha20poly1305::XChaCha20Poly1305;

                let key = Self::mux_key(key).ok_or(DecryptError::WrongKey)?;
                let tag = Self::mux_tag(tag).ok_or(DecryptError::WrongTag)?;
                let nonce = Self::mux_nonce(nonce).ok_or(DecryptError::WrongNonce)?;
                XChaCha20Poly1305.decrypt(plaintext, key, nonce, aad, ciphertext, tag)
            }
        }
    }
}

#[cfg(any(feature = "chacha20poly1305", feature = "xchacha20poly1305"))]
#[cfg(test)]
mod tests {
    use libcrux_traits::aead::typed_refs;
    use typed_refs::Aead as _;

    use super::Aead;

    #[test]
    #[cfg(feature = "chacha20poly1305")]
    fn test_key_centric_multiplexed_chachapoly() {
        let algo = Aead::ChaCha20Poly1305;

        algo.new_key(&[0; 33]).expect_err("length should mismatch");

        let mut tag_bytes = [0; 16];

        let key = algo.new_key(&[0; 32]).expect("length should match");
        let nonce = algo.new_nonce(&[0; 12]).expect("length should match");
        let tag = algo
            .new_tag_mut(&mut tag_bytes)
            .expect("length should match");

        let pt = b"the quick brown fox jumps over the lazy dog";
        let mut ct = [0; 43];
        let mut pt_out = [0; 43];

        key.encrypt(&mut ct, tag, nonce, b"", pt).unwrap();
        let tag = algo.new_tag(&tag_bytes).unwrap();
        key.decrypt(&mut pt_out, nonce, b"", &ct, tag).unwrap();
        assert_eq!(pt, &pt_out);
    }

    #[test]
    #[cfg(feature = "xchacha20poly1305")]
    fn test_key_centric_multiplexed_xchachapoly() {
        let algo = Aead::XChaCha20Poly1305;

        algo.new_key(&[0; 33]).expect_err("length should mismatch");

        let mut tag_bytes = [0; 16];

        let key = algo.new_key(&[0; 32]).expect("length should match");
        let nonce = algo.new_nonce(&[0; 24]).expect("length should match");
        let tag = algo
            .new_tag_mut(&mut tag_bytes)
            .expect("length should match");

        let pt = b"the quick brown fox jumps over the lazy dog";
        let mut ct = [0; 43];
        let mut pt_out = [0; 43];

        key.encrypt(&mut ct, tag, nonce, b"", pt).unwrap();
        let tag = algo.new_tag(&tag_bytes).unwrap();
        key.decrypt(&mut pt_out, nonce, b"", &ct, tag).unwrap();
        assert_eq!(pt, &pt_out);
    }
}
