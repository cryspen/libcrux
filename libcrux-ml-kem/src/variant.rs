//! This module defines the `Variant` trait, which captures
//! differences between the NIST standard FIPS 203 (ML-KEM) and the
//! Round 3 CRYSTALS-Kyber submissions in the NIST PQ competition.

use crate::{constants::CPA_PKE_KEY_GENERATION_SEED_SIZE, hash_functions::Hash, MlKemCiphertext};

/// This trait collects differences in specification between ML-KEM
/// (FIPS 203) and the Round 3 CRYSTALS-Kyber submission in the
/// NIST PQ competition.
///
/// cf. FIPS 203, Appendix C
pub(crate) trait Variant {
    fn kdf<const K: usize, const CIPHERTEXT_SIZE: usize, Hasher: Hash<K>>(
        shared_secret: &[u8],
        ciphertext: &MlKemCiphertext<CIPHERTEXT_SIZE>,
    ) -> [u8; 32];
    fn entropy_preprocess<const K: usize, Hasher: Hash<K>>(randomness: &[u8]) -> [u8; 32];
    fn cpa_keygen_seed<const K: usize, Hasher: Hash<K>>(seed: &[u8]) -> [u8; 64];
}

/// Implements [`Variant`], to perform the Kyber-specific actions
/// during encapsulation and decapsulation.
/// Specifically,
/// * during key generation, the seed hash is not domain separated
/// * during encapsulation, the initial randomness is hashed before being used,
/// * the derivation of the shared secret includes a hash of the Kyber ciphertext.
#[cfg(feature = "kyber")]
pub(crate) struct Kyber {}

#[cfg(feature = "kyber")]
impl Variant for Kyber {
    #[inline(always)]
    fn kdf<const K: usize, const CIPHERTEXT_SIZE: usize, Hasher: Hash<K>>(
        shared_secret: &[u8],
        ciphertext: &MlKemCiphertext<CIPHERTEXT_SIZE>,
    ) -> [u8; 32] {
        use crate::{constants::H_DIGEST_SIZE, utils::into_padded_array};

        let mut kdf_input: [u8; 2 * H_DIGEST_SIZE] = into_padded_array(&shared_secret);
        kdf_input[H_DIGEST_SIZE..].copy_from_slice(&Hasher::H(ciphertext.as_slice()));
        Hasher::PRF::<32>(&kdf_input)
    }

    #[inline(always)]
    fn entropy_preprocess<const K: usize, Hasher: Hash<K>>(randomness: &[u8]) -> [u8; 32] {
        Hasher::H(&randomness)
    }

    #[inline(always)]
    fn cpa_keygen_seed<const K: usize, Hasher: Hash<K>>(key_generation_seed: &[u8]) -> [u8; 64] {
        Hasher::G(key_generation_seed)
    }
}

/// Implements [`Variant`], to perform the ML-KEM-specific actions
/// during encapsulation and decapsulation.
/// Specifically,
/// * during key generation, the seed hash is domain separated (this is a difference from the FIPS 203 IPD and Kyber)
/// * during encapsulation, the initial randomness is used without prior hashing,
/// * the derivation of the shared secret does not include a hash of the ML-KEM ciphertext.
pub(crate) struct MlKem {}

impl Variant for MlKem {
    #[inline(always)]
    fn kdf<const K: usize, const CIPHERTEXT_SIZE: usize, Hasher: Hash<K>>(
        shared_secret: &[u8],
        _: &MlKemCiphertext<CIPHERTEXT_SIZE>,
    ) -> [u8; 32] {
        let mut out = [0u8; 32];
        out.copy_from_slice(shared_secret);
        out
    }

    #[inline(always)]
    fn entropy_preprocess<const K: usize, Hasher: Hash<K>>(randomness: &[u8]) -> [u8; 32] {
        let mut out = [0u8; 32];
        out.copy_from_slice(randomness);
        out
    }

    #[inline(always)]
    fn cpa_keygen_seed<const K: usize, Hasher: Hash<K>>(key_generation_seed: &[u8]) -> [u8; 64] {
        let mut seed = [0u8; CPA_PKE_KEY_GENERATION_SEED_SIZE + 1];
        seed[0..CPA_PKE_KEY_GENERATION_SEED_SIZE].copy_from_slice(key_generation_seed);
        seed[CPA_PKE_KEY_GENERATION_SEED_SIZE] = K as u8;
        Hasher::G(&seed)
    }
}
