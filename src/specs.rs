#![allow(dead_code)]
//! # hacspecs
//!
//! This module holds specifications for all implementations in libcrux.
//! They are the basis for all proofs and can used to generate test vectors or
//! when using libcrux in other hacspecs.

mod bls12_381;
mod chacha20;
mod chacha20poly1305;
mod curve25519;
mod poly1305;
mod sha256;

pub mod aead {
    use hacspec_lib::seq::Bytes;

    pub use crate::aead::{self, Algorithm, Error, Iv, Key};

    /// AEAD encrypt the message in `msg` with the `key`, `iv` and `aad` using
    /// the `algorithm`.
    ///
    /// Returns the `(ciphertext, tag)` tuple, or an error string if the
    /// key was invalid.
    pub fn encrypt(
        algorithm: Algorithm,
        key: &Bytes,
        msg: &Bytes,
        iv: Bytes,
        aad: &Bytes,
    ) -> Result<(Bytes, Bytes), Error> {
        let mut msg_ctxt = msg.to_native();
        let tag = aead::encrypt(
            &Key::from_bytes(algorithm, key.to_native())?,
            &mut msg_ctxt,
            Iv(iv.into_native().try_into().map_err(|_| Error::InvalidIv)?),
            &aad.to_native(),
        )?;

        Ok((Bytes::from_native(msg_ctxt), Bytes::from_native(tag.into())))
    }

    /// AEAD decrypt the ciphertext in `ctxt` with the `key`, `iv`, `aad`, and
    /// `tag` using the `algorithm`.
    ///
    /// Returns the plaintext or an error if the decryption fails.
    pub fn decrypt(
        algorithm: Algorithm,
        key: &Bytes,
        ctxt: &Bytes,
        iv: Bytes,
        aad: &Bytes,
        tag: &Bytes,
    ) -> Result<Bytes, Error> {
        let mut ctxt_msg = ctxt.to_native();
        aead::decrypt(
            &Key::from_bytes(algorithm, key.to_native())?,
            &mut ctxt_msg,
            Iv(iv.into_native().try_into().map_err(|_| Error::InvalidIv)?),
            &aad.to_native(),
            &tag.to_native()
                .try_into()
                .map_err(|_| Error::DecryptionFailed)?,
        )?;

        Ok(Bytes::from_native(ctxt_msg))
    }
}

pub mod hkdf {
    use hacspec_lib::seq::Bytes;

    use crate::hkdf::{self, Algorithm, Error};

    /// HKDF extract using hash function `mode`, `salt`, and the input key material `ikm`.
    /// Returns the pre-key material in a vector of tag length.
    pub fn extract(alg: Algorithm, salt: &Bytes, ikm: &Bytes) -> Bytes {
        Bytes::from_native(hkdf::extract(alg, &salt.to_native(), &ikm.to_native()))
    }

    /// HKDF expand using hash function `mode`, pre-key material `prk`, `info`, and output length `okm_len`.
    /// Returns the key material in a vector of length `okm_len` or [`Error::OkmLengthTooLarge`]
    /// if the requested output length is too large.
    pub fn expand(
        alg: Algorithm,
        prk: &Bytes,
        info: &Bytes,
        okm_len: usize,
    ) -> Result<Bytes, Error> {
        hkdf::expand(alg, &prk.to_native(), &info.to_native(), okm_len)
            .map(|r| Bytes::from_native(r))
    }

    /// HKDF using hash function `mode`, `salt`, input key material `ikm`, `info`, and output length `okm_len`.
    /// Calls `extract` and `expand` with the given input.
    /// Returns the key material in a vector of length `okm_len` or [`Error::OkmLengthTooLarge`]
    /// if the requested output length is too large.
    pub fn hkdf(
        mode: Algorithm,
        salt: &Bytes,
        ikm: &Bytes,
        info: &Bytes,
        okm_len: usize,
    ) -> Result<Bytes, Error> {
        let prk = extract(mode, salt, ikm);
        expand(mode, &prk, info, okm_len)
    }
}

pub mod ecdh {
    use hacspec_lib::seq::Bytes;

    use crate::ecdh::{self, Algorithm, Error};

    /// Derive the ECDH shared secret.
    /// Returns `Ok(point * scalar)` on the provided curve [`Algorithm`] or an error.
    pub fn derive(alg: Algorithm, point: &Bytes, scalar: &Bytes) -> Result<Bytes, Error> {
        ecdh::derive(alg, &point.to_native(), &scalar.to_native()).map(|r| Bytes::from_native(r))
    }

    /// Derive the public key for the provided secret key `scalar`.
    pub fn secret_to_public(alg: Algorithm, scalar: &Bytes) -> Result<Bytes, Error> {
        ecdh::secret_to_public(alg, &scalar.to_native()).map(|r| Bytes::from_native(r))
    }

    /// Validate a secret key.
    pub fn validate_scalar(alg: Algorithm, s: &Bytes) -> Result<(), Error> {
        ecdh::validate_scalar(alg, &s.as_slice())
    }
}

pub mod kem {
    use hacspec_lib::prelude::*;
    use rand::{CryptoRng, Rng};

    use crate::kem::{self, Algorithm, Error};

    /// Compute the public key for a private key of the given [`Algorithm`].
    pub fn secret_to_public(alg: Algorithm, sk: &Bytes) -> Result<Bytes, Error> {
        kem::secret_to_public(alg, &sk.to_native()).map(|p| Bytes::from_public_slice(&p))
    }

    /// Generate a key pair for the [`Algorithm`] based on the provided [`Entropy`].
    ///
    /// The function returns a fresh key or a [`Error::KeyGen`] error if
    /// * not enough entropy was available
    /// * it was not possible to generate a valid key within a reasonable amount of iterations.
    pub fn key_gen(
        alg: Algorithm,
        rng: &mut (impl CryptoRng + Rng),
    ) -> Result<(Bytes, Bytes), Error> {
        kem::key_gen(alg, rng)
            .map(|(s, p)| (Bytes::from_public_slice(&s), Bytes::from_public_slice(&p)))
    }

    /// Encapsulate a shared secret to the provided `pk` and return the `(Key, Enc)` tuple.
    pub fn encapsulate(
        alg: Algorithm,
        pk: &Bytes,
        rng: &mut (impl CryptoRng + Rng),
    ) -> Result<(Bytes, Bytes), Error> {
        kem::encapsulate(alg, &pk.to_native(), rng)
            .map(|(s, p)| (Bytes::from_public_slice(&s), Bytes::from_public_slice(&p)))
    }

    /// Decapsulate the shared secret in `ct` using the private key `sk`.
    pub fn decapsulate(alg: Algorithm, ct: &Bytes, sk: &Bytes) -> Result<Bytes, Error> {
        kem::decapsulate(alg, &ct.to_native(), &sk.to_native())
            .map(|s| Bytes::from_public_slice(&s))
    }
}

mod utils;
// mod lib;
