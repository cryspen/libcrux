#![doc = include_str!("../Readme.md")]

use std::sync::RwLock;

use evercrypt::prelude::*;
use hpke_rs_crypto::{
    error::Error,
    types::{AeadAlgorithm, KdfAlgorithm, KemAlgorithm},
    HpkeCrypto, HpkeTestRng,
};
use rand::{CryptoRng, RngCore, SeedableRng};

/// The Evercrypt HPKE Provider
#[derive(Debug)]
pub struct HpkeEvercrypt {}

/// The PRNG for the Evercrypt Provider.
pub struct HpkeEvercryptPrng {
    #[cfg(feature = "deterministic-prng")]
    fake_rng: Vec<u8>,
    rng: RwLock<rand_chacha::ChaCha20Rng>,
}

impl HpkeCrypto for HpkeEvercrypt {
    fn kdf_extract(alg: KdfAlgorithm, salt: &[u8], ikm: &[u8]) -> Vec<u8> {
        match alg {
            KdfAlgorithm::HkdfSha256 => hkdf_extract(HmacMode::Sha256, salt, ikm),
            KdfAlgorithm::HkdfSha384 => hkdf_extract(HmacMode::Sha384, salt, ikm),
            KdfAlgorithm::HkdfSha512 => hkdf_extract(HmacMode::Sha512, salt, ikm),
        }
    }

    fn kdf_expand(
        alg: KdfAlgorithm,
        prk: &[u8],
        info: &[u8],
        output_size: usize,
    ) -> Result<Vec<u8>, Error> {
        Ok(match alg {
            KdfAlgorithm::HkdfSha256 => hkdf_expand(HmacMode::Sha256, prk, info, output_size),
            KdfAlgorithm::HkdfSha384 => hkdf_expand(HmacMode::Sha384, prk, info, output_size),
            KdfAlgorithm::HkdfSha512 => hkdf_expand(HmacMode::Sha512, prk, info, output_size),
        })
    }

    fn kem_derive(alg: KemAlgorithm, pk: &[u8], sk: &[u8]) -> Result<Vec<u8>, Error> {
        let evercrypt_mode = kem_key_type_to_mode(alg)?;
        ecdh_derive(evercrypt_mode, pk, sk)
            .map_err(|e| Error::CryptoLibraryError(format!("ECDH derive error: {:?}", e)))
            .map(|mut p| {
                if evercrypt_mode == EcdhMode::P256 {
                    // We only want the x-coordinate here but evercrypt gives us the entire point
                    p.truncate(32);
                    p
                } else {
                    p
                }
            })
    }

    fn kem_derive_base(alg: KemAlgorithm, sk: &[u8]) -> Result<Vec<u8>, Error> {
        let evercrypt_mode = kem_key_type_to_mode(alg)?;
        ecdh_derive_base(evercrypt_mode, sk)
            .map_err(|e| Error::CryptoLibraryError(format!("ECDH derive base error: {:?}", e)))
            .map(|p| {
                if evercrypt_mode == EcdhMode::P256 {
                    nist_format_uncompressed(p)
                } else {
                    p
                }
            })
    }

    fn kem_key_gen(alg: KemAlgorithm, _: &mut Self::HpkePrng) -> Result<Vec<u8>, Error> {
        // XXX: Evercypt doesn't support bring your own randomness yet.
        //      https://github.com/franziskuskiefer/evercrypt-rust/issues/35
        let evercrypt_mode = kem_key_type_to_mode(alg)?;
        ecdh::key_gen(evercrypt_mode)
            .map_err(|e| Error::CryptoLibraryError(format!("ECDH key gen error: {:?}", e)))
    }

    fn kem_validate_sk(alg: KemAlgorithm, sk: &[u8]) -> Result<Vec<u8>, Error> {
        match alg {
            KemAlgorithm::DhKemP256 => p256_validate_sk(&sk)
                .map_err(|e| Error::CryptoLibraryError(format!("ECDH invalid sk error: {:?}", e)))
                .map(|sk| sk.to_vec()),
            _ => Err(Error::UnknownKemAlgorithm),
        }
    }

    fn aead_seal(
        alg: AeadAlgorithm,
        key: &[u8],
        nonce: &[u8],
        aad: &[u8],
        msg: &[u8],
    ) -> Result<Vec<u8>, Error> {
        let mode = aead_type_to_mode(alg)?;
        if nonce.len() != 12 {
            return Err(Error::AeadInvalidNonce);
        }

        let cipher = match Aead::new(mode, key) {
            Ok(c) => c,
            Err(_) => return Err(Error::CryptoLibraryError(format!("Invalid configuration"))),
        };

        cipher
            .encrypt_combined(&msg, &nonce, &aad)
            .map_err(|e| Error::CryptoLibraryError(format!("AEAD encrypt error: {:?}", e)))
    }

    fn aead_open(
        alg: AeadAlgorithm,
        key: &[u8],
        nonce: &[u8],
        aad: &[u8],
        cipher_txt: &[u8],
    ) -> Result<Vec<u8>, Error> {
        let mode = aead_type_to_mode(alg)?;
        let cipher = match Aead::new(mode, key) {
            Ok(c) => c,
            Err(_) => {
                return Err(Error::CryptoLibraryError(format!(
                    "Invalid configuration or unsupported algorithm {:?}",
                    mode
                )))
            }
        };

        cipher
            .decrypt_combined(&cipher_txt, &nonce, &aad)
            .map_err(|e| Error::CryptoLibraryError(format!("AEAD decryption error: {:?}", e)))
    }

    type HpkePrng = HpkeEvercryptPrng;

    fn prng() -> Self::HpkePrng {
        #[cfg(feature = "deterministic-prng")]
        {
            let mut fake_rng = vec![0u8; 256];
            rand_chacha::ChaCha20Rng::from_entropy().fill_bytes(&mut fake_rng);
            HpkeEvercryptPrng {
                fake_rng,
                rng: RwLock::new(rand_chacha::ChaCha20Rng::from_entropy()),
            }
        }
        #[cfg(not(feature = "deterministic-prng"))]
        HpkeEvercryptPrng {
            rng: RwLock::new(rand_chacha::ChaCha20Rng::from_entropy()),
        }
    }

    /// Returns an error if the KDF algorithm is not supported by this crypto provider.
    fn supports_kdf(_: KdfAlgorithm) -> Result<(), Error> {
        Ok(())
    }

    /// Returns an error if the KEM algorithm is not supported by this crypto provider.
    fn supports_kem(alg: KemAlgorithm) -> Result<(), Error> {
        match alg {
            KemAlgorithm::DhKem25519 | KemAlgorithm::DhKemP256 => Ok(()),
            _ => Err(Error::UnknownKemAlgorithm),
        }
    }

    /// Returns an error if the AEAD algorithm is not supported by this crypto provider.
    fn supports_aead(alg: AeadAlgorithm) -> Result<(), Error> {
        match alg {
            AeadAlgorithm::Aes128Gcm | AeadAlgorithm::Aes256Gcm => aes_support(),
            AeadAlgorithm::ChaCha20Poly1305 => Ok(()),
            AeadAlgorithm::HpkeExport => Err(Error::UnknownAeadAlgorithm),
        }
    }
}

#[cfg(all(target_arch = "x86_64", not(target_os = "macos")))]
fn aes_support() -> Result<(), Error> {
    Ok(())
}

#[cfg(any(not(target_arch = "x86_64"), target_os = "macos"))]
fn aes_support() -> Result<(), Error> {
    Err(Error::UnknownAeadAlgorithm)
}

/// Prepend 0x04 for uncompressed NIST curve points.
#[inline(always)]
fn nist_format_uncompressed(mut pk: Vec<u8>) -> Vec<u8> {
    let mut tmp = Vec::with_capacity(pk.len() + 1);
    tmp.push(0x04);
    tmp.append(&mut pk);
    tmp
}

#[inline(always)]
fn kem_key_type_to_mode(alg: KemAlgorithm) -> Result<EcdhMode, Error> {
    match alg {
        KemAlgorithm::DhKem25519 => Ok(EcdhMode::X25519),
        KemAlgorithm::DhKemP256 => Ok(EcdhMode::P256),
        _ => Err(Error::UnknownKemAlgorithm),
    }
}

#[inline(always)]
fn aead_type_to_mode(alg: AeadAlgorithm) -> Result<AeadMode, Error> {
    match alg {
        AeadAlgorithm::Aes128Gcm => Ok(AeadMode::Aes128Gcm),
        AeadAlgorithm::Aes256Gcm => Ok(AeadMode::Aes256Gcm),
        AeadAlgorithm::ChaCha20Poly1305 => Ok(AeadMode::Chacha20Poly1305),
        _ => Err(Error::UnknownKemAlgorithm),
    }
}

impl RngCore for HpkeEvercryptPrng {
    fn next_u32(&mut self) -> u32 {
        let mut rng = self.rng.write().unwrap();
        rng.next_u32()
    }

    fn next_u64(&mut self) -> u64 {
        let mut rng = self.rng.write().unwrap();
        rng.next_u64()
    }

    fn fill_bytes(&mut self, dest: &mut [u8]) {
        let mut rng = self.rng.write().unwrap();
        rng.fill_bytes(dest)
    }

    fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), rand::Error> {
        let mut rng = self.rng.write().unwrap();
        rng.try_fill_bytes(dest)
    }
}
impl CryptoRng for HpkeEvercryptPrng {}

impl HpkeTestRng for HpkeEvercryptPrng {
    #[cfg(feature = "deterministic-prng")]
    fn try_fill_test_bytes(&mut self, dest: &mut [u8]) -> Result<(), rand::Error> {
        // Here we fake our randomness for testing.
        if dest.len() > self.fake_rng.len() {
            return Err(rand::Error::new(Error::InsufficientRandomness));
        }
        dest.clone_from_slice(&self.fake_rng.split_off(self.fake_rng.len() - dest.len()));
        Ok(())
    }
    #[cfg(not(feature = "deterministic-prng"))]
    fn try_fill_test_bytes(&mut self, dest: &mut [u8]) -> Result<(), rand::Error> {
        self.rng.write().unwrap().try_fill_bytes(dest)
    }

    #[cfg(feature = "deterministic-prng")]
    fn seed(&mut self, seed: &[u8]) {
        self.fake_rng = seed.to_vec();
    }
    #[cfg(not(feature = "deterministic-prng"))]
    fn seed(&mut self, _: &[u8]) {}
}
