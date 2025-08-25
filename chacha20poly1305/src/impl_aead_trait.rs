use libcrux_traits::aead::arrayref::{Aead, DecryptError, EncryptError};

use crate::{KEY_LEN, NONCE_LEN, TAG_LEN};

/// The ChaCha20Poly1305 AEAD algorithm.
///
/// Note: Plaintext, ciphertext and aad need to be at most [`u32::MAX`] long, due to limitations of
/// the implementation.
pub struct ChaCha20Poly1305;

/// The extended ChaCha20Poly1305 AEAD algorithm, which uses longer nonces than ChaCha20Poly1305.
///
/// Note: Plaintext, ciphertext and aad need to be at most [`u32::MAX`] long, due to limitations of
/// the implementation.
pub struct XChaCha20Poly1305;

mod impl_chachapoly {
    use super::*;

    impl Aead<KEY_LEN, TAG_LEN, NONCE_LEN> for ChaCha20Poly1305 {
        fn encrypt(
            ciphertext: &mut [u8],
            tag: &mut [u8; TAG_LEN],
            key: &[u8; KEY_LEN],
            nonce: &[u8; NONCE_LEN],
            aad: &[u8],
            plaintext: &[u8],
        ) -> Result<(), EncryptError> {
            if plaintext.len() != ciphertext.len() {
                return Err(EncryptError::WrongCiphertextLength);
            }

            let ptxt_len: u32 = plaintext
                .len()
                .try_into()
                .map_err(|_| EncryptError::PlaintextTooLong)?;
            let aad_len: u32 = aad.len().try_into().map_err(|_| EncryptError::AadTooLong)?;

            crate::hacl::aead_chacha20poly1305::encrypt(
                ciphertext, tag, plaintext, ptxt_len, aad, aad_len, key, nonce,
            );

            Ok(())
        }

        fn decrypt(
            plaintext: &mut [u8],
            key: &[u8; KEY_LEN],
            nonce: &[u8; NONCE_LEN],
            aad: &[u8],
            ciphertext: &[u8],
            tag: &[u8; TAG_LEN],
        ) -> Result<(), DecryptError> {
            if plaintext.len() != ciphertext.len() {
                return Err(DecryptError::WrongPlaintextLength);
            }

            let aad_len: u32 = aad.len().try_into().map_err(|_| DecryptError::AadTooLong)?;
            let ctxt_len: u32 = ciphertext
                .len()
                .try_into()
                .map_err(|_| DecryptError::PlaintextTooLong)?;

            // this call should only ever produce 0 or 1, where 0 is success and 1 is error
            match crate::hacl::aead_chacha20poly1305::decrypt(
                plaintext, ciphertext, ctxt_len, aad, aad_len, key, nonce, tag,
            ) {
                0 => Ok(()),
                _ => Err(DecryptError::InvalidTag),
            }
        }
    }

    libcrux_traits::aead::slice::impl_aead_slice_trait!(ChaCha20Poly1305 => KEY_LEN, TAG_LEN, NONCE_LEN);
    libcrux_traits::aead::typed_owned::impl_aead_typed_owned!(
        ChaCha20Poly1305,
        KEY_LEN,
        TAG_LEN,
        NONCE_LEN
    );
}

mod impl_xchachapoly {
    use crate::xchacha20_poly1305::NONCE_LEN as XNONCE_LEN;

    use super::*;

    impl Aead<KEY_LEN, TAG_LEN, XNONCE_LEN> for XChaCha20Poly1305 {
        fn encrypt(
            ciphertext: &mut [u8],
            tag: &mut [u8; TAG_LEN],
            key: &[u8; KEY_LEN],
            nonce: &[u8; XNONCE_LEN],
            aad: &[u8],
            plaintext: &[u8],
        ) -> Result<(), EncryptError> {
            let mut subkey = [0u8; KEY_LEN];
            let mut new_nonce = [0u8; super::NONCE_LEN];

            crate::xchacha20_poly1305::derive(key, nonce, &mut subkey, &mut new_nonce);
            ChaCha20Poly1305::encrypt(ciphertext, tag, &subkey, &new_nonce, aad, plaintext)
        }

        fn decrypt(
            plaintext: &mut [u8],
            key: &[u8; KEY_LEN],
            nonce: &[u8; XNONCE_LEN],
            aad: &[u8],
            ciphertext: &[u8],
            tag: &[u8; TAG_LEN],
        ) -> Result<(), DecryptError> {
            let mut subkey = [0u8; KEY_LEN];
            let mut new_nonce = [0u8; super::NONCE_LEN];

            crate::xchacha20_poly1305::derive(key, nonce, &mut subkey, &mut new_nonce);
            ChaCha20Poly1305::decrypt(plaintext, &subkey, &new_nonce, &aad, ciphertext, tag)
        }
    }

    libcrux_traits::aead::slice::impl_aead_slice_trait!(XChaCha20Poly1305 => KEY_LEN, TAG_LEN, XNONCE_LEN);
    libcrux_traits::aead::typed_owned::impl_aead_typed_owned!(
        XChaCha20Poly1305,
        KEY_LEN,
        TAG_LEN,
        XNONCE_LEN
    );
}

#[cfg(test)]
mod tests {
    use libcrux_traits::aead::typed_owned;
    type Key = typed_owned::Key<super::ChaCha20Poly1305>;
    type Nonce = typed_owned::Nonce<super::ChaCha20Poly1305>;
    type Tag = typed_owned::Tag<super::ChaCha20Poly1305>;

    #[test]
    fn test_key_centric_owned() {
        let k: Key = [0; 32].into();
        let nonce: Nonce = [0; 12].into();
        let mut tag: Tag = [0; 16].into();

        let pt = b"the quick brown fox jumps over the lazy dog";
        let mut ct = [0; 43];
        let mut pt_out = [0; 43];

        k.encrypt(&mut ct, &mut tag, &nonce, b"", pt).unwrap();
        k.decrypt(&mut pt_out, &nonce, b"", &ct, &tag).unwrap();
        assert_eq!(pt, &pt_out);
    }
}
