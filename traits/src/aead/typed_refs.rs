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
