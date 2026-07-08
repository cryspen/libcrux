//! Post-quantum KEM implementations using RustCrypto crates.
//!
//! Provides X-Wing (hybrid X25519 + ML-KEM-768) and standalone
//! ML-KEM-768 / ML-KEM-1024 support.

use alloc::vec::Vec;

use hpke_rs_crypto::{error::Error, types::KemAlgorithm};
use ml_kem::{
    Decapsulate, Encapsulate, Generate, KeyExport, TryKeyInit,
    kem::Decapsulator,
};

use crate::HpkeRustCryptoPrng;

/// Generate a KEM key pair. Returns `(encapsulation_key, decapsulation_key)`.
pub(crate) fn kem_key_gen(
    alg: KemAlgorithm,
    prng: &mut HpkeRustCryptoPrng,
) -> Result<(Vec<u8>, Vec<u8>), Error> {
    match alg {
        #[allow(deprecated)]
        KemAlgorithm::XWingDraft06
        | KemAlgorithm::XWingDraft06Obsolete => {
            let dk =
                x_wing::DecapsulationKey::generate_from_rng(prng);
            let ek = dk.encapsulation_key();
            Ok((
                ek.to_bytes().as_slice().to_vec(),
                dk.as_bytes().to_vec(),
            ))
        }
        KemAlgorithm::MlKem768 => {
            let dk =
                ml_kem::DecapsulationKey768::generate_from_rng(prng);
            let ek_bytes = dk.encapsulation_key().to_bytes();
            let sk_bytes = dk
                .to_seed()
                .ok_or(Error::KemInvalidSecretKey)?;
            Ok((ek_bytes.as_slice().to_vec(), sk_bytes.to_vec()))
        }
        KemAlgorithm::MlKem1024 => {
            let dk =
                ml_kem::DecapsulationKey1024::generate_from_rng(prng);
            let ek_bytes = dk.encapsulation_key().to_bytes();
            let sk_bytes = dk
                .to_seed()
                .ok_or(Error::KemInvalidSecretKey)?;
            Ok((ek_bytes.as_slice().to_vec(), sk_bytes.to_vec()))
        }
        _ => Err(Error::UnsupportedKemOperation),
    }
}

/// Deterministic key generation from a seed.
/// Returns `(encapsulation_key, decapsulation_key)`.
pub(crate) fn kem_key_gen_derand(
    alg: KemAlgorithm,
    seed: &[u8],
) -> Result<(Vec<u8>, Vec<u8>), Error> {
    match alg {
        #[allow(deprecated)]
        KemAlgorithm::XWingDraft06
        | KemAlgorithm::XWingDraft06Obsolete => {
            let seed: [u8; 32] = seed
                .try_into()
                .map_err(|_| Error::KemInvalidSecretKey)?;
            let dk = x_wing::DecapsulationKey::from(seed);
            let ek = dk.encapsulation_key();
            Ok((
                ek.to_bytes().as_slice().to_vec(),
                dk.as_bytes().to_vec(),
            ))
        }
        KemAlgorithm::MlKem768 => {
            let seed = ml_kem::Seed::try_from(seed)
                .map_err(|_| Error::KemInvalidSecretKey)?;
            let dk = ml_kem::DecapsulationKey768::from_seed(seed);
            let ek_bytes = dk.encapsulation_key().to_bytes();
            let sk_bytes = dk
                .to_seed()
                .ok_or(Error::KemInvalidSecretKey)?;
            Ok((ek_bytes.as_slice().to_vec(), sk_bytes.to_vec()))
        }
        KemAlgorithm::MlKem1024 => {
            let seed = ml_kem::Seed::try_from(seed)
                .map_err(|_| Error::KemInvalidSecretKey)?;
            let dk = ml_kem::DecapsulationKey1024::from_seed(seed);
            let ek_bytes = dk.encapsulation_key().to_bytes();
            let sk_bytes = dk
                .to_seed()
                .ok_or(Error::KemInvalidSecretKey)?;
            Ok((ek_bytes.as_slice().to_vec(), sk_bytes.to_vec()))
        }
        _ => Err(Error::UnsupportedKemOperation),
    }
}

/// KEM encapsulation. Returns `(shared_secret, ciphertext)`.
pub(crate) fn kem_encaps(
    alg: KemAlgorithm,
    pk_r: &[u8],
    prng: &mut HpkeRustCryptoPrng,
) -> Result<(Vec<u8>, Vec<u8>), Error> {
    match alg {
        #[allow(deprecated)]
        KemAlgorithm::XWingDraft06
        | KemAlgorithm::XWingDraft06Obsolete => {
            let ek = x_wing::EncapsulationKey::new_from_slice(pk_r)
                .map_err(|_| Error::KemInvalidPublicKey)?;
            let (ct, ss) = ek.encapsulate_with_rng(prng);
            Ok((ss.as_slice().to_vec(), ct.as_slice().to_vec()))
        }
        KemAlgorithm::MlKem768 => {
            let ek_arr = ml_kem::array::Array::try_from(pk_r)
                .map_err(|_| Error::KemInvalidPublicKey)?;
            let ek = ml_kem::EncapsulationKey768::new(&ek_arr)
                .map_err(|_| Error::KemInvalidPublicKey)?;
            let (ct, ss) = ek.encapsulate_with_rng(prng);
            Ok((ss.as_slice().to_vec(), ct.as_slice().to_vec()))
        }
        KemAlgorithm::MlKem1024 => {
            let ek_arr = ml_kem::array::Array::try_from(pk_r)
                .map_err(|_| Error::KemInvalidPublicKey)?;
            let ek = ml_kem::EncapsulationKey1024::new(&ek_arr)
                .map_err(|_| Error::KemInvalidPublicKey)?;
            let (ct, ss) = ek.encapsulate_with_rng(prng);
            Ok((ss.as_slice().to_vec(), ct.as_slice().to_vec()))
        }
        _ => Err(Error::UnsupportedKemOperation),
    }
}

/// KEM decapsulation. Returns the shared secret.
pub(crate) fn kem_decaps(
    alg: KemAlgorithm,
    ct: &[u8],
    sk_r: &[u8],
) -> Result<Vec<u8>, Error> {
    match alg {
        #[allow(deprecated)]
        KemAlgorithm::XWingDraft06
        | KemAlgorithm::XWingDraft06Obsolete => {
            let seed: [u8; 32] = sk_r
                .try_into()
                .map_err(|_| Error::KemInvalidSecretKey)?;
            let dk = x_wing::DecapsulationKey::from(seed);
            let ct = x_wing::Ciphertext::try_from(ct)
                .map_err(|_| Error::KemInvalidCiphertext)?;
            let ss = dk.decapsulate(&ct);
            Ok(ss.as_slice().to_vec())
        }
        KemAlgorithm::MlKem768 => {
            let seed = ml_kem::Seed::try_from(sk_r)
                .map_err(|_| Error::KemInvalidSecretKey)?;
            let dk = ml_kem::DecapsulationKey768::from_seed(seed);
            let ct = ml_kem::ml_kem_768::Ciphertext::try_from(ct)
                .map_err(|_| Error::KemInvalidCiphertext)?;
            let ss = dk.decapsulate(&ct);
            Ok(ss.as_slice().to_vec())
        }
        KemAlgorithm::MlKem1024 => {
            let seed = ml_kem::Seed::try_from(sk_r)
                .map_err(|_| Error::KemInvalidSecretKey)?;
            let dk = ml_kem::DecapsulationKey1024::from_seed(seed);
            let ct = ml_kem::ml_kem_1024::Ciphertext::try_from(ct)
                .map_err(|_| Error::KemInvalidCiphertext)?;
            let ss = dk.decapsulate(&ct);
            Ok(ss.as_slice().to_vec())
        }
        _ => Err(Error::UnsupportedKemOperation),
    }
}
