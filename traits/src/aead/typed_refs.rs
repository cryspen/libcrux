//! This module contains the trait and related errors for an Authenticated
//! Encryption with Associated Data (AEAD) scheme that takes array references
//! as arguments and writes outputs to mutable array references.

use libcrux_secrets::U8;

/// Error that can occur during encryption.
#[derive(Debug, PartialEq, Eq)]
pub enum EncryptError {
    /// The ciphertext buffer has the wrong length.
    WrongCiphertextLength,

    /// The plaintext is too long for this algorithm or implementation.
    PlaintextTooLong,

    /// The AAD is too long for this algorithm or implementation.
    AadTooLong,

    /// The key has the wrong length.
    WrongKey,

    /// The tag has the wrong length.
    WrongTag,

    /// The nonce has the wrong length.
    WrongNonce,

    /// An unknown error occurred during encryption.
    Unknown,
}

/// Error that can occur during decryption.
#[derive(Debug, PartialEq, Eq)]
pub enum DecryptError {
    /// The authentication tag is invalid; the ciphertext has been tampered with
    /// or the key/nonce/aad is incorrect.
    InvalidTag,

    /// The plaintext buffer has the wrong length.
    WrongPlaintextLength,

    /// The plaintext is too long for this algorithm or implementation.
    PlaintextTooLong,

    /// The AAD is too long for this algorithm or implementation.
    AadTooLong,

    /// The key has the wrong length.
    WrongKey,

    /// The tag has the wrong length.
    WrongTag,

    /// The nonce has the wrong length.
    WrongNonce,

    /// An unknown error occurred during decryption.
    Unknown,
}

impl From<super::arrayref::EncryptError> for EncryptError {
    fn from(value: super::arrayref::EncryptError) -> Self {
        match value {
            super::arrayref::EncryptError::WrongCiphertextLength => {
                EncryptError::WrongCiphertextLength
            }
            super::arrayref::EncryptError::PlaintextTooLong => EncryptError::PlaintextTooLong,
            super::arrayref::EncryptError::AadTooLong => EncryptError::AadTooLong,
            super::arrayref::EncryptError::Unknown => EncryptError::Unknown,
        }
    }
}

impl From<super::arrayref::DecryptError> for DecryptError {
    fn from(value: super::arrayref::DecryptError) -> Self {
        match value {
            super::arrayref::DecryptError::InvalidTag => DecryptError::InvalidTag,
            super::arrayref::DecryptError::WrongPlaintextLength => {
                DecryptError::WrongPlaintextLength
            }
            super::arrayref::DecryptError::PlaintextTooLong => DecryptError::PlaintextTooLong,
            super::arrayref::DecryptError::AadTooLong => DecryptError::AadTooLong,
            super::arrayref::DecryptError::Unknown => DecryptError::Unknown,
        }
    }
}

impl core::fmt::Display for EncryptError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let text = match self {
            EncryptError::WrongCiphertextLength => "ciphertext buffer has wrong length",
            EncryptError::PlaintextTooLong => {
                "plaintext is too long for algorithm or implementation"
            }
            EncryptError::AadTooLong => "aad is too long for algorithm or implementation",
            EncryptError::Unknown => "an unknown error occurred",
            EncryptError::WrongKey => "key is for wrong algorithm",
            EncryptError::WrongTag => "tag is for wrong algorithm",
            EncryptError::WrongNonce => "nonce is for wrong algorithm",
        };

        f.write_str(text)
    }
}

impl core::fmt::Display for DecryptError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let text = match self {
            DecryptError::InvalidTag => "invalid authentication tag",
            DecryptError::WrongPlaintextLength => "plaintext buffer has wrong length",
            DecryptError::PlaintextTooLong => {
                "plaintext is too long for algorithm or implementation"
            }
            DecryptError::AadTooLong => "aad is too long for algorithm or implementation",
            DecryptError::Unknown => "an unknown error occurred",
            DecryptError::WrongKey => "key is for wrong algorithm",
            DecryptError::WrongTag => "tag is for wrong algorithm",
            DecryptError::WrongNonce => "nonce is for wrong algorithm",
        };

        f.write_str(text)
    }
}

// These are the types for the arguments to AEAD. I wonder if it makes sense to do stuff like
// implementing a random constructor for Nonce for all LEN in 24..64 or so
//
// There also is the question whether we want these to be byte-oriented or whether we want to just
// make these associated types. That would mean that we'd have to define them separately for all
// implementations.

#[derive(Clone, Copy)]
pub struct Key<'a, Algo>(Algo, &'a [U8]);
#[derive(Clone, Copy)]
pub struct Tag<'a, Algo>(Algo, &'a [u8]);
pub struct TagMut<'a, Algo>(Algo, &'a mut [u8]);
#[derive(Clone, Copy)]
pub struct Nonce<'a, Algo>(Algo, &'a [u8]);

impl<'a, Algo: Aead + core::fmt::Debug> core::fmt::Debug for Key<'a, Algo> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_tuple("Key").field(&self.0).field(&"***").finish()
    }
}

/// An Authenticated Encryption with Associated Data (AEAD) scheme. This trait
/// is low-level and is mostly used for implementing other, more usable APIs.
///
/// Some implementors of this trait may impose stronger restrictions on the inputs than described
/// here. Check the documentation of the types implementing this trait to make sure which inputs
/// are valid.
pub trait Aead: Copy + PartialEq {
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
    ) -> Result<Tag<'a, Self>, EncryptError>;

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

pub trait AeadExt: Aead {
    fn new_key(self, key: &[U8]) -> Result<Key<Self>, WrongLengthError>;
    fn new_tag(self, tag: &[u8]) -> Result<Tag<Self>, WrongLengthError>;
    fn new_tag_mut(self, tag_mut: &mut [u8]) -> Result<TagMut<Self>, WrongLengthError>;
    fn new_nonce(self, nonce: &[u8]) -> Result<Nonce<Self>, WrongLengthError>;
}

impl<Algo: Aead> AeadExt for Algo {
    fn new_key(self, key: &[U8]) -> Result<Key<Self>, WrongLengthError> {
        Key::new_for_algo(self, key)
    }
    fn new_tag(self, tag: &[u8]) -> Result<Tag<Self>, WrongLengthError> {
        Tag::new_for_algo(self, tag)
    }
    fn new_tag_mut(self, tag_mut: &mut [u8]) -> Result<TagMut<Self>, WrongLengthError> {
        TagMut::new_for_algo(self, tag_mut)
    }
    fn new_nonce(self, nonce: &[u8]) -> Result<Nonce<Self>, WrongLengthError> {
        Nonce::new_for_algo(self, nonce)
    }
}

impl<
        const KEY_LEN: usize,
        const TAG_LEN: usize,
        const NONCE_LEN: usize,
        Algo: super::typed_owned::Aead<
                Key = [U8; KEY_LEN],
                Tag = [u8; TAG_LEN],
                Nonce = [u8; NONCE_LEN],
            > + Copy
            + PartialEq,
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
    ) -> Result<Tag<'a, Self>, EncryptError> {
        if key.algo() != self {
            return Err(EncryptError::WrongKey);
        }
        if tag.algo() != self {
            return Err(EncryptError::WrongTag);
        }
        if nonce.algo() != self {
            return Err(EncryptError::WrongNonce);
        }

        // now we expect the lengths to be correct, so later mismatches are unknown errors
        let key: &[U8; KEY_LEN] = key.as_ref().try_into().map_err(|_| EncryptError::Unknown)?;

        let tag_raw: &mut [u8; TAG_LEN] =
            tag.as_mut().try_into().map_err(|_| EncryptError::Unknown)?;

        let nonce: &[u8; NONCE_LEN] = nonce
            .as_ref()
            .try_into()
            .map_err(|_| EncryptError::Unknown)?;

        <Self as super::typed_owned::Aead>::encrypt(
            ciphertext,
            tag_raw.into(),
            key.into(),
            nonce.into(),
            aad,
            plaintext,
        )
        .map_err(EncryptError::from)
        .map(|_| Tag::from(tag))
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
        if key.algo() != self {
            return Err(DecryptError::WrongKey);
        }
        if tag.algo() != self {
            return Err(DecryptError::WrongTag);
        }
        if nonce.algo() != self {
            return Err(DecryptError::WrongNonce);
        }

        // now we expect the lengths to be correct, so later mismatches are unknown errors
        let key: &[U8; KEY_LEN] = key.as_ref().try_into().map_err(|_| DecryptError::Unknown)?;

        let tag: &[u8; TAG_LEN] = tag.as_ref().try_into().map_err(|_| DecryptError::Unknown)?;

        let nonce: &[u8; NONCE_LEN] = nonce
            .as_ref()
            .try_into()
            .map_err(|_| DecryptError::Unknown)?;

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

#[derive(Debug, Clone, Copy)]
pub struct WrongLengthError;

impl<'a, Algo: Aead> Key<'a, Algo> {
    pub fn new_for_algo(algo: Algo, key: &'a [U8]) -> Result<Self, WrongLengthError> {
        (key.len() == algo.key_len())
            .then_some(Key(algo, key))
            .ok_or(WrongLengthError)
    }

    pub fn encrypt(
        &self,
        ciphertext: &mut [u8],
        tag: TagMut<'a, Algo>,
        nonce: Nonce<'a, Algo>,
        aad: &[u8],
        plaintext: &[U8],
    ) -> Result<Tag<'a, Algo>, EncryptError> {
        self.0
            .encrypt(ciphertext, tag, *self, nonce, aad, plaintext)
    }

    pub fn decrypt(
        &self,
        plaintext: &mut [U8],
        nonce: Nonce<'a, Algo>,
        aad: &[u8],
        ciphertext: &[u8],
        tag: Tag<'a, Algo>,
    ) -> Result<(), DecryptError> {
        self.0
            .decrypt(plaintext, *self, nonce, aad, ciphertext, tag)
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

impl<'a, Algo: Aead> Tag<'a, Algo> {
    pub fn new_for_algo(algo: Algo, tag: &'a [u8]) -> Result<Self, WrongLengthError> {
        (tag.len() == algo.tag_len())
            .then_some(Tag(algo, tag))
            .ok_or(WrongLengthError)
    }
}

impl<'a, Algo: Aead> AsRef<[u8]> for Tag<'a, Algo> {
    fn as_ref(&self) -> &[u8] {
        self.1
    }
}

impl<'a, Algo> Tag<'a, Algo> {
    pub fn algo(&self) -> &Algo {
        &self.0
    }
}

impl<'a, Algo: Aead> TagMut<'a, Algo> {
    pub fn new_for_algo(algo: Algo, tag: &'a mut [u8]) -> Result<Self, WrongLengthError> {
        (tag.len() == algo.tag_len())
            .then_some(TagMut(algo, tag))
            .ok_or(WrongLengthError)
    }
}

impl<'a, Algo: Aead> From<TagMut<'a, Algo>> for Tag<'a, Algo> {
    fn from(tag: TagMut<'a, Algo>) -> Self {
        Tag(tag.0, tag.1)
    }
}

impl<'a, Algo> TagMut<'a, Algo> {
    pub fn algo(&self) -> &Algo {
        &self.0
    }
}

impl<'a, Algo: Aead> Nonce<'a, Algo> {
    pub fn new_for_algo(algo: Algo, nonce: &'a [u8]) -> Result<Self, WrongLengthError> {
        (nonce.len() == algo.nonce_len())
            .then_some(Nonce(algo, nonce))
            .ok_or(WrongLengthError)
    }
}

impl<'a, Algo> Nonce<'a, Algo> {
    pub fn algo(&self) -> &Algo {
        &self.0
    }
}

impl<'a, Algo: Aead> AsRef<[u8]> for Nonce<'a, Algo> {
    fn as_ref(&self) -> &[u8] {
        self.1
    }
}

impl<'a, Algo: Aead> AsMut<[u8]> for TagMut<'a, Algo> {
    fn as_mut(&mut self) -> &mut [u8] {
        self.1
    }
}

pub trait Multiplexes<Algo>: Aead + Sized {
    fn mux_algo(&self) -> Option<Algo>;
    fn wrap_algo(algo: Algo) -> Self;

    fn mux_key<'a>(key: Key<'a, Self>) -> Option<Key<'a, Algo>> {
        let Key(algo, bytes) = key;
        algo.mux_algo().map(|algo| Key(algo, bytes))
    }

    fn wrap_key<'a>(k: Key<'a, Algo>) -> Key<'a, Self> {
        Key(Self::wrap_algo(k.0), k.1)
    }

    fn mux_tag<'a>(tag: Tag<'a, Self>) -> Option<Tag<'a, Algo>> {
        let Tag(algo, bytes) = tag;
        algo.mux_algo().map(|algo| Tag(algo, bytes))
    }

    fn wrap_tag<'a>(tag: Tag<'a, Algo>) -> Tag<'a, Self> {
        Tag(Self::wrap_algo(tag.0), tag.1)
    }

    fn mux_tag_mut<'a>(tag: TagMut<'a, Self>) -> Option<TagMut<'a, Algo>> {
        let TagMut(algo, bytes) = tag;
        algo.mux_algo().map(|algo| TagMut(algo, bytes))
    }

    fn wrap_tag_mut<'a>(tag: TagMut<'a, Algo>) -> TagMut<'a, Self> {
        TagMut(Self::wrap_algo(tag.0), tag.1)
    }

    fn mux_nonce<'a>(nonce: Nonce<'a, Self>) -> Option<Nonce<'a, Algo>> {
        let Nonce(algo, bytes) = nonce;
        algo.mux_algo().map(|algo| Nonce(algo, bytes))
    }

    fn wrap_nonce<'a>(nonce: Nonce<'a, Algo>) -> Nonce<'a, Self> {
        Nonce(Self::wrap_algo(nonce.0), nonce.1)
    }
}
