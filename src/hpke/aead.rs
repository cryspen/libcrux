//! # Authenticated Encryption (AEAD)
//!
//! > 💡 This is a hacspec representation of the [HPKE RFC].
//! > The text is mostly verbatim from the RFC with changes where required.
//! > It demonstrates the possibilities of hacspec for specifications.
//!
//! - [`Seal(key, nonce, aad, pt)`](`AeadSeal`): Encrypt and authenticate plaintext
//! `pt` with associated data `aad` using symmetric key `key` and nonce
//! `nonce`, yielding ciphertext and tag `ct`. This function
//!  can raise a [`MessageLimitReachedError`](`HpkeError::MessageLimitReachedError`) upon failure.
//! - [`Open(key, nonce, aad, ct)`](`AeadOpen`): Decrypt ciphertext and tag `ct` using
//! associated data `aad` with symmetric key `key` and nonce `nonce`,
//! returning plaintext message `pt`. This function can raise an
//! [`OpenError`](`HpkeError::OpenError`) or [`MessageLimitReachedError`](`HpkeError::MessageLimitReachedError`) upon failure.
//! - [`Nk`]: The length in bytes of a key for this algorithm.
//! - [`Nn`]: The length in bytes of a nonce for this algorithm.
//! - [`Nt`]: The length in bytes of the authentication tag for this algorithm.
//!
//! ## Security Requirements on an AEAD
//!
//! All AEADs MUST be IND-CCA2-secure, as is currently true for all AEADs
//! listed in [`AEAD`].
//!
//! [hpke rfc]: https://datatracker.ietf.org/doc/draft-irtf-cfrg-hpke/
//! [publication queue]: https://www.rfc-editor.org/current_queue.php
#![allow(
    non_camel_case_types,
    non_snake_case,
    unused_imports,
    non_upper_case_globals
)]

use crate::{
    aead::{self, *},
    hmac::tag_size,
};

use super::errors::*;

type AeadAlgResult = Result<Algorithm, HpkeError>;

/// ## Authenticated Encryption with Associated Data (AEAD) Functions
///
/// The `0xFFFF` AEAD ID is reserved for applications which only use the Export
/// interface; see HPKE for more details.
///
/// | Value  | AEAD             | Nk  | Nn  | Nt  | Reference |
/// | :----- | :--------------- | :-- | :-- | :-- | :-------- |
/// | 0x0000 | (reserved)       | N/A | N/A | N/A | N/A       |
/// | 0x0001 | AES-128-GCM      | 16  | 12  | 16  | [GCM]     |
/// | 0x0002 | AES-256-GCM      | 32  | 12  | 16  | [GCM]     |
/// | 0x0003 | ChaCha20Poly1305 | 32  | 12  | 16  | [RFC8439] |
/// | 0xFFFF | Export-only      | N/A | N/A | N/A | RFCXXXX   |
///
/// The "HPKE AEAD Identifiers" registry lists identifiers for authenticated
/// encryption with associated data (AEAD) algorithms defined for use with HPKE.
/// These identifiers are two-byte values, so the maximum possible value is
/// 0xFFFF = 65535.
///
/// Template:
///
/// * Value: The two-byte identifier for the algorithm
/// * AEAD: The name of the algorithm
/// * Nk: The length in bytes of a key for this algorithm
/// * Nn: The length in bytes of a nonce for this algorithm
/// * Nt: The length in bytes of an authentication tag for this algorithm
/// * Reference: Where this algorithm is defined
///
/// [GCM]: https://doi.org/10.6028/nist.sp.800-38d
/// [RFC8439]: https://www.rfc-editor.org/info/rfc8439
#[derive(Clone, Copy, PartialEq, Debug)]
pub enum AEAD {
    /// 0x0001
    AES_128_GCM,
    /// 0x0002
    AES_256_GCM,
    /// 0x0003
    ChaCha20Poly1305,
    /// 0xFFFF
    Export_only,
}

/// The length in bytes of a key for this algorithm.
///
/// See [`AEAD`] for details.
pub fn Nk(aead_id: AEAD) -> usize {
    match aead_id {
        AEAD::AES_128_GCM => 16,
        AEAD::AES_256_GCM => 32,
        AEAD::ChaCha20Poly1305 => 32,
        AEAD::Export_only => 0,
    }
}

/// The length in bytes of the authentication tag for this algorithm.
///
/// See [`AEAD`] for details.
pub fn Nt(aead_id: AEAD) -> usize {
    match aead_id {
        AEAD::AES_128_GCM => 16,
        AEAD::AES_256_GCM => 16,
        AEAD::ChaCha20Poly1305 => 16,
        AEAD::Export_only => 0,
    }
}

/// The length in bytes of a nonce for this algorithm.
///
/// See [`AEAD`] for details.
pub fn Nn(aead_id: AEAD) -> usize {
    match aead_id {
        AEAD::AES_128_GCM => 12,
        AEAD::AES_256_GCM => 12,
        AEAD::ChaCha20Poly1305 => 12,
        AEAD::Export_only => 0,
    }
}

/// An AEAD key is a sequence of bytes.
pub type Key = Vec<u8>;

/// An AEAD nonce is a sequence of bytes.
pub type Nonce = Vec<u8>;

fn alg_for_aead(aead_id: AEAD) -> AeadAlgResult {
    match aead_id {
        AEAD::AES_128_GCM => AeadAlgResult::Ok(Algorithm::Aes128Gcm),
        AEAD::AES_256_GCM => AeadAlgResult::Ok(Algorithm::Aes256Gcm),
        AEAD::ChaCha20Poly1305 => AeadAlgResult::Ok(Algorithm::Chacha20Poly1305),
        AEAD::Export_only => AeadAlgResult::Err(HpkeError::UnsupportedAlgorithm),
    }
}

/// Encrypt and authenticate plaintext `pt` with associated data `aad` using
/// symmetric key `key` and nonce `nonce`, yielding ciphertext and tag `ct`.
/// This function can raise a [`MessageLimitReachedError`](`HpkeError::MessageLimitReachedError`) upon failure.
pub fn AeadSeal(aead_id: AEAD, key: &Key, nonce: &Nonce, aad: &[u8], pt: &[u8]) -> HpkeBytesResult {
    let algorithm = alg_for_aead(aead_id)?;
    let key = aead::Key::from_slice(algorithm, key)?;
    match encrypt_detached(&key, pt, Iv::new(nonce)?, aad) {
        Ok((tag, mut ct)) => {
            ct.extend_from_slice(tag.as_ref());
            HpkeBytesResult::Ok(ct)
        }
        Err(_) => HpkeBytesResult::Err(HpkeError::CryptoError),
    }
}

/// Decrypt ciphertext and tag `ct` using
/// associated data `aad` with symmetric key `key` and nonce `nonce`,
/// returning plaintext message `pt`. This function can raise an
/// [`OpenError`](`HpkeError::OpenError`) or [`MessageLimitReachedError`](`HpkeError::MessageLimitReachedError`) upon failure.
pub fn AeadOpen(aead_id: AEAD, key: &Key, nonce: &Nonce, aad: &[u8], ct: &[u8]) -> HpkeBytesResult {
    let algorithm = alg_for_aead(aead_id)?;
    let key = aead::Key::from_slice(algorithm, key)?;
    let mut ct = ct.to_vec();
    let tag = ct.split_off(ct.len() - Nt(aead_id));
    match decrypt_detached(&key, ct, Iv::new(nonce)?, aad, &Tag::from_slice(tag)?) {
        Ok(pt) => HpkeBytesResult::Ok(pt.into()),
        Err(_) => HpkeBytesResult::Err(HpkeError::CryptoError),
    }
}
