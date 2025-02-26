//! This module defines the `Variant` trait, which captures
//! differences between the NIST standard FIPS 203 (ML-KEM) and the
//! Round 3 CRYSTALS-Kyber submissions in the NIST PQ competition.

use crate::{constants::CPA_PKE_KEY_GENERATION_SEED_SIZE, hash_functions::Hash, MlKemCiphertext};

/// This trait collects differences in specification between ML-KEM
/// (FIPS 203) and the Round 3 CRYSTALS-Kyber submission in the
/// NIST PQ competition.
///
/// cf. FIPS 203, Appendix C
#[hax_lib::attributes]
pub(crate) trait Variant {
    #[requires(shared_secret.len() == 32)]
    #[ensures(|res| fstar!(r#"$res == $shared_secret"#))] // We only have post-conditions for ML-KEM, not Kyber
    fn kdf<const K: usize, const CIPHERTEXT_SIZE: usize, Hasher: Hash>(
        shared_secret: &[u8],
        ciphertext: &MlKemCiphertext<CIPHERTEXT_SIZE>,
        out: &mut [u8],
    );
    #[requires(randomness.len() == 32)]
    #[ensures(|res| fstar!(r#"$res == $randomness"#))] // We only have post-conditions for ML-KEM, not Kyber
    fn entropy_preprocess<const K: usize, Hasher: Hash>(randomness: &[u8], out: &mut [u8]);
    #[requires(seed.len() == 32)]
    #[ensures(|res| fstar!(r#"Seq.length $seed == 32 ==> $res == Spec.Utils.v_G
        (Seq.append $seed (Seq.create 1 (cast $K <: u8)))"#)
    )]
    fn cpa_keygen_seed<const K: usize, Hasher: Hash>(seed: &[u8], out: &mut [u8]);
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
    fn kdf<const K: usize, const CIPHERTEXT_SIZE: usize, Hasher: Hash>(
        shared_secret: &[u8],
        ciphertext: &MlKemCiphertext<CIPHERTEXT_SIZE>,
        out: &mut [u8],
    ) {
        use crate::{constants::H_DIGEST_SIZE, utils::into_padded_array};

        let mut kdf_input: [u8; 2 * H_DIGEST_SIZE] = into_padded_array(&shared_secret);
        Hasher::H(ciphertext.as_slice(), &mut kdf_input[H_DIGEST_SIZE..]);
        Hasher::PRF::<32>(&kdf_input, out)
    }

    #[inline(always)]
    fn entropy_preprocess<const K: usize, Hasher: Hash>(randomness: &mut [u8], out: &mut [u8]) {
        Hasher::H(&randomness, out)
    }

    #[inline(always)]
    fn cpa_keygen_seed<const K: usize, Hasher: Hash>(
        key_generation_seed: &[u8],
        out: &mut [u8],
    ) -> [u8; 64] {
        Hasher::G(key_generation_seed, out)
    }
}

/// Implements [`Variant`], to perform the ML-KEM-specific actions
/// during encapsulation and decapsulation.
/// Specifically,
/// * during key generation, the seed hash is domain separated (this is a difference from the FIPS 203 IPD and Kyber)
/// * during encapsulation, the initial randomness is used without prior hashing,
/// * the derivation of the shared secret does not include a hash of the ML-KEM ciphertext.
pub(crate) struct MlKem {}

#[hax_lib::attributes]
impl Variant for MlKem {
    #[inline(always)]
    #[requires(shared_secret.len() == 32)]
    #[ensures(|res| fstar!(r#"$res == $shared_secret"#))]
    fn kdf<const K: usize, const CIPHERTEXT_SIZE: usize, Hasher: Hash>(
        shared_secret: &[u8],
        _: &MlKemCiphertext<CIPHERTEXT_SIZE>,
        out: &mut [u8],
    ) {
        out.copy_from_slice(shared_secret);
    }

    #[inline(always)]
    #[requires(randomness.len() == 32)]
    #[ensures(|res| fstar!(r#"$res == $randomness"#))]
    fn entropy_preprocess<const K: usize, Hasher: Hash>(randomness: &[u8], out: &mut [u8]) {
        out.copy_from_slice(randomness);
    }

    #[inline(always)]
    #[requires(key_generation_seed.len() == 32)]
    #[ensures(|res| fstar!(r#"Seq.length $key_generation_seed == 32 ==> $res == Spec.Utils.v_G
        (Seq.append $key_generation_seed (Seq.create 1 (cast $K <: u8)))"#)
    )]
    fn cpa_keygen_seed<const K: usize, Hasher: Hash>(key_generation_seed: &[u8], out: &mut [u8]) {
        let mut seed = [0u8; CPA_PKE_KEY_GENERATION_SEED_SIZE + 1];
        seed[0..CPA_PKE_KEY_GENERATION_SEED_SIZE].copy_from_slice(key_generation_seed);
        seed[CPA_PKE_KEY_GENERATION_SEED_SIZE] = K as u8;
        hax_lib::fstar!(
            "Lib.Sequence.eq_intro #u8 #33 $seed
            (Seq.append $key_generation_seed (Seq.create 1 (cast $K <: u8)))"
        );
        Hasher::G(&seed, out);
    }
}
