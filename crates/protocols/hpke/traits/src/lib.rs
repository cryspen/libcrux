#![doc = include_str!("../Readme.md")]
#![no_std]

extern crate alloc;
#[cfg(feature = "std")]
extern crate std;

use alloc::string::String;
use alloc::vec::Vec;

use error::Error;
use types::{AeadAlgorithm, KemAlgorithm};

pub mod error;
pub mod types;

// re-export trait
pub use rand_core::{CryptoRng, RngCore};

/// The [`HpkeCrypto`] trait defines the necessary cryptographic functions used
/// in the HPKE implementation.
pub trait HpkeCrypto: core::fmt::Debug + Send + Sync {
    /// The PRNG implementation returned in [`HpkeCrypto::prng()`].
    type HpkePrng: RngCore + CryptoRng + HpkeTestRng;

    /// The name of the implementation.
    fn name() -> String;

    /// Returns an error if the KDF algorithm is not supported by this crypto provider.
    fn supports_kdf(alg: types::KdfAlgorithm) -> Result<(), Error>;

    /// Returns an error if the KEM algorithm is not supported by this crypto provider.
    fn supports_kem(alg: types::KemAlgorithm) -> Result<(), Error>;

    /// Returns an error if the AEAD algorithm is not supported by this crypto provider.
    fn supports_aead(alg: types::AeadAlgorithm) -> Result<(), Error>;

    /// Get a stateful PRNG.
    /// Note that this will create a new PRNG state.
    fn prng() -> Self::HpkePrng;

    /// Get the length of the output digest.
    #[inline(always)]
    fn kdf_digest_length(alg: types::KdfAlgorithm) -> usize {
        match alg {
            types::KdfAlgorithm::HkdfSha256 => 32,
            types::KdfAlgorithm::HkdfSha384 => 48,
            types::KdfAlgorithm::HkdfSha512 => 64,
        }
    }

    /// KDF Extract
    fn kdf_extract(alg: types::KdfAlgorithm, salt: &[u8], ikm: &[u8]) -> Vec<u8>;

    /// KDF Expand
    fn kdf_expand(
        alg: types::KdfAlgorithm,
        prk: &[u8],
        info: &[u8],
        output_size: usize,
    ) -> Result<Vec<u8>, Error>;

    /// Diffie-Hellman
    fn dh(alg: KemAlgorithm, pk: &[u8], sk: &[u8]) -> Result<Vec<u8>, Error>;

    /// Diffie-Hellman with the base (generate public key for secret key `sk`).
    fn secret_to_public(alg: KemAlgorithm, sk: &[u8]) -> Result<Vec<u8>, Error>;

    /// KEM key pair generation (encapsulation key, decapsulation key).
    fn kem_key_gen(
        alg: KemAlgorithm,
        prng: &mut Self::HpkePrng,
    ) -> Result<(Vec<u8>, Vec<u8>), Error>;

    /// KEM key pair generation (encapsulation key, decapsulation key) based
    /// on the `seed`.
    fn kem_key_gen_derand(alg: KemAlgorithm, seed: &[u8]) -> Result<(Vec<u8>, Vec<u8>), Error>;

    /// KEM encapsulation to `pk_r` (shared secret, ciphertext).
    fn kem_encaps(
        alg: KemAlgorithm,
        pk_r: &[u8],
        prng: &mut Self::HpkePrng,
    ) -> Result<(Vec<u8>, Vec<u8>), Error>;

    /// KEM decapsulation with `sk_r`.
    /// Returns the shared secret.
    fn kem_decaps(alg: KemAlgorithm, ct: &[u8], sk_r: &[u8]) -> Result<Vec<u8>, Error>;

    /// Validate a secret key for its correctness.
    fn dh_validate_sk(alg: KemAlgorithm, sk: &[u8]) -> Result<Vec<u8>, Error>;

    /// AEAD encrypt.
    fn aead_seal(
        alg: AeadAlgorithm,
        key: &[u8],
        nonce: &[u8],
        aad: &[u8],
        msg: &[u8],
    ) -> Result<Vec<u8>, Error>;

    /// AEAD decrypt.
    fn aead_open(
        alg: AeadAlgorithm,
        key: &[u8],
        nonce: &[u8],
        aad: &[u8],
        msg: &[u8],
    ) -> Result<Vec<u8>, Error>;

    /// Get key length for AEAD.
    ///
    /// Note that this function returns `0` for export only keys of unknown size.
    fn aead_key_length(alg: AeadAlgorithm) -> usize {
        match alg {
            AeadAlgorithm::Aes128Gcm => 16,
            AeadAlgorithm::Aes256Gcm => 32,
            AeadAlgorithm::ChaCha20Poly1305 => 32,
            AeadAlgorithm::HpkeExport => 0,
        }
    }

    /// Get key length for AEAD.
    ///
    /// Note that this function returns `0` for export only nonces of unknown size.
    fn aead_nonce_length(alg: AeadAlgorithm) -> usize {
        match alg {
            AeadAlgorithm::Aes128Gcm => 12,
            AeadAlgorithm::Aes256Gcm => 12,
            AeadAlgorithm::ChaCha20Poly1305 => 12,
            AeadAlgorithm::HpkeExport => 0,
        }
    }

    /// Get key length for AEAD.
    ///
    /// Note that this function returns `0` for export only tags of unknown size.
    fn aead_tag_length(alg: AeadAlgorithm) -> usize {
        match alg {
            AeadAlgorithm::Aes128Gcm => 16,
            AeadAlgorithm::Aes256Gcm => 16,
            AeadAlgorithm::ChaCha20Poly1305 => 16,
            AeadAlgorithm::HpkeExport => 0,
        }
    }
}

/// PRNG extension for testing that is supposed to return pre-configured bytes.
pub trait HpkeTestRng {
    // Error type to replace rand::Error (which is no longer available as of version 0.9)
    type Error: core::fmt::Debug + core::fmt::Display;
    /// Like [`TryRngCore::try_fill_bytes`] but the result is expected to be known.
    fn try_fill_test_bytes(&mut self, dest: &mut [u8]) -> Result<(), Self::Error>;

    /// Set the randomness state of this test PRNG.
    fn seed(&mut self, seed: &[u8]);
}
