//! This module contains the trait and related errors for an Authenticated
//! Encryption with Associated Data (AEAD) scheme that takes array references
//! as arguments and returns outputs as arrays or vectors.

use super::arrayref::{DecryptError, EncryptError};

/// An Authenticated Encryption with Associated Data (AEAD) scheme
///
/// Some implementors of this trait may impose stronger restrictions on the inputs than described
/// here. Check the documentation of the types implementing this trait to make sure which inputs
/// are valid.
pub trait Aead<const KEY_LEN: usize, const TAG_LEN: usize, const NONCE_LEN: usize> {
    /// Encrypt a plaintext message, producing a ciphertext and an authentication tag.
    fn encrypt<const MSG_LEN: usize>(
        key: &[u8; KEY_LEN],
        nonce: &[u8; NONCE_LEN],
        aad: &[u8],
        plaintext: &[u8; MSG_LEN],
    ) -> Result<([u8; MSG_LEN], [u8; TAG_LEN]), EncryptError>;

    /// Encrypt a plaintext message, producing a ciphertext and an authentication tag.
    fn encrypt_to_vec(
        key: &[u8; KEY_LEN],
        nonce: &[u8; NONCE_LEN],
        aad: &[u8],
        plaintext: &[u8],
    ) -> Result<(alloc::vec::Vec<u8>, [u8; TAG_LEN]), EncryptError>;

    /// Decrypt a ciphertext, verifying its authenticity.
    fn decrypt<const MSG_LEN: usize>(
        key: &[u8; KEY_LEN],
        nonce: &[u8; NONCE_LEN],
        aad: &[u8],
        ciphertext: &[u8; MSG_LEN],
        tag: &[u8; TAG_LEN],
    ) -> Result<[u8; MSG_LEN], DecryptError>;

    /// Decrypt a ciphertext, verifying its authenticity.
    fn decrypt_to_vec(
        key: &[u8; KEY_LEN],
        nonce: &[u8; NONCE_LEN],
        aad: &[u8],
        ciphertext: &[u8],
        tag: &[u8; TAG_LEN],
    ) -> Result<alloc::vec::Vec<u8>, DecryptError>;
}

impl<
        const KEY_LEN: usize,
        const TAG_LEN: usize,
        const NONCE_LEN: usize,
        T: super::arrayref::Aead<KEY_LEN, TAG_LEN, NONCE_LEN>,
    > Aead<KEY_LEN, TAG_LEN, NONCE_LEN> for T
{
    fn encrypt<const MSG_LEN: usize>(
        key: &[u8; KEY_LEN],
        nonce: &[u8; NONCE_LEN],
        aad: &[u8],
        plaintext: &[u8; MSG_LEN],
    ) -> Result<([u8; MSG_LEN], [u8; TAG_LEN]), EncryptError> {
        let mut ciphertext = [0u8; MSG_LEN];
        let mut tag = [0u8; TAG_LEN];

        Self::encrypt(&mut ciphertext, &mut tag, key, nonce, aad, plaintext)
            .map(|()| (ciphertext, tag))
    }

    fn encrypt_to_vec(
        key: &[u8; KEY_LEN],
        nonce: &[u8; NONCE_LEN],
        aad: &[u8],
        plaintext: &[u8],
    ) -> Result<(alloc::vec::Vec<u8>, [u8; TAG_LEN]), EncryptError> {
        let mut ciphertext = alloc::vec![0u8; plaintext.len()];
        let mut tag = [0u8; TAG_LEN];

        Self::encrypt(&mut ciphertext, &mut tag, key, nonce, aad, plaintext)
            .map(|()| (ciphertext, tag))
    }

    fn decrypt<const MSG_LEN: usize>(
        key: &[u8; KEY_LEN],
        nonce: &[u8; NONCE_LEN],
        aad: &[u8],
        ciphertext: &[u8; MSG_LEN],
        tag: &[u8; TAG_LEN],
    ) -> Result<[u8; MSG_LEN], DecryptError> {
        let mut plaintext = [0u8; MSG_LEN];

        Self::decrypt(&mut plaintext, key, nonce, aad, ciphertext, tag).map(|()| plaintext)
    }

    fn decrypt_to_vec(
        key: &[u8; KEY_LEN],
        nonce: &[u8; NONCE_LEN],
        aad: &[u8],
        ciphertext: &[u8],
        tag: &[u8; TAG_LEN],
    ) -> Result<alloc::vec::Vec<u8>, DecryptError> {
        let mut plaintext = alloc::vec![0u8; ciphertext.len()];

        Self::decrypt(&mut plaintext, key, nonce, aad, ciphertext, tag).map(|()| plaintext)
    }
}
