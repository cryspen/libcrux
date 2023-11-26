#![doc = include_str!("../Readme.md")]

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

    /// KEM Derive
    fn kem_derive(alg: KemAlgorithm, pk: &[u8], sk: &[u8]) -> Result<Vec<u8>, Error>;

    /// KEM Derive with base
    fn kem_derive_base(alg: KemAlgorithm, sk: &[u8]) -> Result<Vec<u8>, Error>;

    /// KEM Key generation
    fn kem_key_gen(alg: KemAlgorithm, prng: &mut Self::HpkePrng) -> Result<Vec<u8>, Error>;

    /// Validate a secret key for its correctness.
    fn kem_validate_sk(alg: KemAlgorithm, sk: &[u8]) -> Result<Vec<u8>, Error>;

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
    /// Like [`RngCore::try_fill_bytes`] but the result is expected to be known.
    fn try_fill_test_bytes(&mut self, dest: &mut [u8]) -> Result<(), rand_core::Error>;

    /// Set the randomness state of this test PRNG.
    fn seed(&mut self, seed: &[u8]);
}
