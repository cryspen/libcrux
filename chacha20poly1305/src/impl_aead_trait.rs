use libcrux_traits::aead::arrayref::{Aead, DecryptError, EncryptError};

use crate::{KEY_LEN, NONCE_LEN, TAG_LEN};

/// The ChaCha20Poly1305 AEAD algorithm
pub struct ChaCha20Poly1305;

/// The extended ChaCha20Poly1305 AEAD algorithm, which uses longer nonces.
pub struct XChaCha20Poly1305;

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

use crate::xchacha20_poly1305::NONCE_LEN as XNONCE_LEN;

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

libcrux_traits::aead::slice::impl_aead_slice_trait!(ChaCha20Poly1305 => KEY_LEN, TAG_LEN, NONCE_LEN);
libcrux_traits::aead::slice::impl_aead_slice_trait!(XChaCha20Poly1305 => KEY_LEN, TAG_LEN, XNONCE_LEN);
