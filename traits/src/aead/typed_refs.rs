//! This module contains the trait and related errors for an Authenticated
//! Encryption with Associated Data (AEAD) scheme that takes array references
//! as arguments and writes outputs to mutable array references.

use super::slice::*;
use libcrux_secrets::U8;

// These are the types for the arguments to AEAD. I wonder if it makes sense to do stuff like
// implementing a random constructor for Nonce for all LEN in 24..64 or so
//
// There also is the question whether we want these to be byte-oriented or whether we want to just
// make these associated types. That would mean that we'd have to define them separately for all
// implementations.

pub struct Key<'a, Algo>(Algo, &'a [U8]);
pub struct Tag<'a, Algo>(Algo, &'a [u8]);
pub struct TagMut<'a, Algo>(Algo, &'a mut [u8]);
pub struct Nonce<'a, Algo>(Algo, &'a [u8]);

/// An Authenticated Encryption with Associated Data (AEAD) scheme. This trait
/// is low-level and is mostly used for implementing other, more usable APIs.
///
/// Some implementors of this trait may impose stronger restrictions on the inputs than described
/// here. Check the documentation of the types implementing this trait to make sure which inputs
/// are valid.
pub trait Aead: Sized {
    fn key_len(&self) -> usize;
    fn tag_len(&self) -> usize;
    fn nonce_len(&self) -> usize;

    /// Encrypt a plaintext message, producing a ciphertext and an authentication tag.
    /// The arguments `plaintext` and `ciphertext` must have the same length.
    fn encrypt<'a>(
        &self,
        ciphertext: &mut [u8],
        tag: TagMut<'a, Self>,
        key: Key<'a, Self>,
        nonce: Nonce<'a, Self>,
        aad: &[u8],
        plaintext: &[U8],
    ) -> Result<(), EncryptError>;

    /// Decrypt a ciphertext, verifying its authenticity.
    /// The arguments `plaintext` and `ciphertext` must have the same length.
    fn decrypt<'a>(
        &self,
        plaintext: &mut [U8],
        key: Key<'a, Self>,
        nonce: Nonce<'a, Self>,
        aad: &[u8],
        ciphertext: &[u8],
        tag: Tag<'a, Self>,
    ) -> Result<(), DecryptError>;
}

impl<
        const KEY_LEN: usize,
        const TAG_LEN: usize,
        const NONCE_LEN: usize,
        Algo: super::typed_owned::Aead<Key = [U8; KEY_LEN], Tag = [u8; TAG_LEN], Nonce = [u8; NONCE_LEN]>,
    > Aead for Algo
{
    fn key_len(&self) -> usize {
        KEY_LEN
    }

    fn tag_len(&self) -> usize {
        TAG_LEN
    }

    fn nonce_len(&self) -> usize {
        NONCE_LEN
    }

    fn encrypt<'a>(
        &self,
        ciphertext: &mut [u8],
        mut tag: TagMut<'a, Self>,
        key: Key<'a, Self>,
        nonce: Nonce<'a, Self>,
        aad: &[u8],
        plaintext: &[U8],
    ) -> Result<(), EncryptError> {
        let key: &[U8; KEY_LEN] = key
            .as_ref()
            .try_into()
            .map_err(|_| EncryptError::WrongKeyLength)?;

        let tag: &mut [u8; TAG_LEN] = tag
            .as_mut()
            .try_into()
            .map_err(|_| EncryptError::WrongTagLength)?;

        let nonce: &[u8; NONCE_LEN] = nonce
            .as_ref()
            .try_into()
            .map_err(|_| EncryptError::WrongNonceLength)?;

        <Self as super::typed_owned::Aead>::encrypt(
            ciphertext,
            tag.into(),
            key.into(),
            nonce.into(),
            aad,
            plaintext,
        )
        .map_err(EncryptError::from)
    }

    fn decrypt<'a>(
        &self,
        plaintext: &mut [U8],
        key: Key<'a, Self>,
        nonce: Nonce<'a, Self>,
        aad: &[u8],
        ciphertext: &[u8],
        tag: Tag<'a, Self>,
    ) -> Result<(), DecryptError> {
        let key: &[U8; KEY_LEN] = key
            .as_ref()
            .try_into()
            .map_err(|_| DecryptError::WrongKeyLength)?;

        let tag: &[u8; TAG_LEN] = tag
            .as_ref()
            .try_into()
            .map_err(|_| DecryptError::WrongTagLength)?;

        let nonce: &[u8; NONCE_LEN] = nonce
            .as_ref()
            .try_into()
            .map_err(|_| DecryptError::WrongNonceLength)?;

        <Self as super::typed_owned::Aead>::decrypt(
            plaintext,
            key.into(),
            nonce.into(),
            aad,
            ciphertext,
            tag.into(),
        )
        .map_err(DecryptError::from)
    }
}

impl<'a, Algo: Aead> AsRef<[U8]> for Key<'a, Algo> {
    fn as_ref(&self) -> &[U8] {
        self.1
    }
}

impl<'a, Algo> Key<'a, Algo> {
    pub fn algo(&self) -> &Algo {
        &self.0
    }
}

pub trait Multiplexes<Algo>: Aead {
    fn mux_algo(&self) -> Option<Algo>;

    fn mux_key<'a>(key: Key<'a, Self>) -> Option<Key<'a, Algo>> {
        let Key(algo, bytes) = key;
        algo.mux_algo().map(|algo| Key(algo, bytes))
    }

    fn mux_tag<'a>(tag: Tag<'a, Self>) -> Option<Tag<'a, Algo>> {
        let Tag(algo, bytes) = tag;
        algo.mux_algo().map(|algo| Tag(algo, bytes))
    }

    fn mux_tag_mut<'a>(tag: TagMut<'a, Self>) -> Option<TagMut<'a, Algo>> {
        let TagMut(algo, bytes) = tag;
        algo.mux_algo().map(|algo| TagMut(algo, bytes))
    }

    fn mux_nonce<'a>(nonce: Nonce<'a, Self>) -> Option<Nonce<'a, Algo>> {
        let Nonce(algo, bytes) = nonce;
        algo.mux_algo().map(|algo| Nonce(algo, bytes))
    }
}

impl<'a, Algo: Aead> AsRef<[u8]> for Tag<'a, Algo> {
    fn as_ref(&self) -> &[U8] {
        self.1
    }
}

impl<'a, Algo> Tag<'a, Algo> {
    pub fn algo(&self) -> &Algo {
        &self.0
    }
}

impl<'a, Algo> TagMut<'a, Algo> {
    pub fn algo(&self) -> &Algo {
        &self.0
    }
}

impl<'a, Algo> Nonce<'a, Algo> {
    pub fn algo(&self) -> &Algo {
        &self.0
    }
}

impl<'a, Algo: Aead> AsRef<[u8]> for Nonce<'a, Algo> {
    fn as_ref(&self) -> &[U8] {
        self.1
    }
}

impl<'a, Algo: Aead> AsMut<[u8]> for TagMut<'a, Algo> {
    fn as_mut(&mut self) -> &mut [U8] {
        self.1
    }
}
