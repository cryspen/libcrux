//! This module contains the trait and related errors for an Authenticated
//! Encryption with Associated Data (AEAD) scheme that takes array references
//! as arguments and writes outputs to mutable array references.

use super::arrayref::*;
use libcrux_secrets::U8;

// These are the types for the arguments to AEAD. I wonder if it makes sense to do stuff like
// implementing a random constructor for Nonce for all LEN in 24..64 or so
//
// There also is the question whether we want these to be byte-oriented or whether we want to just
// make these associated types. That would mean that we'd have to define them separately for all
// implementations.

pub struct Key<Algo: Aead>(Algo, Algo::Key);
pub struct Tag<Algo: Aead>(Algo, Algo::Tag);
pub struct Nonce<Algo: Aead>(Algo, Algo::Nonce);

/// An Authenticated Encryption with Associated Data (AEAD) scheme. This trait
/// is low-level and is mostly used for implementing other, more usable APIs.
///
/// Some implementors of this trait may impose stronger restrictions on the inputs than described
/// here. Check the documentation of the types implementing this trait to make sure which inputs
/// are valid.
pub trait Aead: Sized {
    type Key;
    type Tag;
    type Nonce;

    /// Encrypt a plaintext message, producing a ciphertext and an authentication tag.
    /// The arguments `plaintext` and `ciphertext` must have the same length.
    fn encrypt(
        ciphertext: &mut [u8],
        tag: &mut Tag<Self>,
        key: &Key<Self>,
        nonce: &Nonce<Self>,
        aad: &[u8],
        plaintext: &[U8],
    ) -> Result<(), EncryptError>;

    /// Decrypt a ciphertext, verifying its authenticity.
    /// The arguments `plaintext` and `ciphertext` must have the same length.
    fn decrypt(
        plaintext: &mut [U8],
        key: &Key<Self>,
        nonce: &Nonce<Self>,
        aad: &[u8],
        ciphertext: &[u8],
        tag: &Tag<Self>,
    ) -> Result<(), DecryptError>;
}

impl<Algo: Aead> Key<Algo> {
    pub fn encrypt(
        &self,
        ciphertext: &mut [u8],
        tag: &mut Tag<Algo>,
        nonce: &Nonce<Algo>,
        aad: &[u8],
        plaintext: &[U8],
    ) -> Result<(), EncryptError> {
        Algo::encrypt(ciphertext, tag, self, nonce, aad, plaintext)
    }
}

impl<
        const KEY_LEN: usize,
        const TAG_LEN: usize,
        const NONCE_LEN: usize,
        Algo: super::arrayref::Aead<KEY_LEN, TAG_LEN, NONCE_LEN>,
    > Aead for Algo
{
    type Key = [U8; KEY_LEN];

    type Tag = [u8; TAG_LEN];

    type Nonce = [u8; NONCE_LEN];

    fn encrypt(
        ciphertext: &mut [u8],
        tag: &mut Tag<Self>,
        key: &Key<Self>,
        nonce: &Nonce<Self>,
        aad: &[u8],
        plaintext: &[U8],
    ) -> Result<(), EncryptError> {
        <Algo as super::arrayref::Aead<KEY_LEN, TAG_LEN, NONCE_LEN>>::encrypt(
            ciphertext, &mut tag.1, &key.1, &nonce.1, aad, plaintext,
        )
    }

    fn decrypt(
        plaintext: &mut [U8],
        key: &Key<Self>,
        nonce: &Nonce<Self>,
        aad: &[u8],
        ciphertext: &[u8],
        tag: &Tag<Self>,
    ) -> Result<(), DecryptError> {
        <Algo as super::arrayref::Aead<KEY_LEN, TAG_LEN, NONCE_LEN>>::decrypt(
            plaintext, &key.1, &nonce.1, aad, ciphertext, &tag.1,
        )
    }
}
