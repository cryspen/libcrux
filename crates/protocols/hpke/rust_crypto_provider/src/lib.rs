#![doc = include_str!("../Readme.md")]

use std::sync::RwLock;

use hpke_rs_crypto::{
    error::Error,
    types::{AeadAlgorithm, KdfAlgorithm, KemAlgorithm},
    CryptoRng, HpkeCrypto, HpkeTestRng, RngCore,
};
use p256::{elliptic_curve::ecdh::diffie_hellman, EncodedPoint, PublicKey, SecretKey};
use rand::SeedableRng;
use x25519_dalek_ng::{PublicKey as X25519PublicKey, StaticSecret as X25519StaticSecret};

mod aead;
mod hkdf;
use crate::aead::*;
use crate::hkdf::*;

/// The Rust Crypto HPKE Provider
#[derive(Debug)]
pub struct HpkeRustCrypto {}

/// The PRNG for the Rust Crypto Provider.
pub struct HpkeRustCryptoPrng {
    rng: RwLock<rand_chacha::ChaCha20Rng>,
    #[cfg(feature = "deterministic-prng")]
    fake_rng: Vec<u8>,
}

impl HpkeCrypto for HpkeRustCrypto {
    fn kdf_extract(alg: KdfAlgorithm, salt: &[u8], ikm: &[u8]) -> Vec<u8> {
        match alg {
            KdfAlgorithm::HkdfSha256 => sha256_extract(salt, ikm),
            KdfAlgorithm::HkdfSha384 => sha384_extract(salt, ikm),
            KdfAlgorithm::HkdfSha512 => sha512_extract(salt, ikm),
        }
    }

    fn kdf_expand(
        alg: KdfAlgorithm,
        prk: &[u8],
        info: &[u8],
        output_size: usize,
    ) -> Result<Vec<u8>, Error> {
        match alg {
            KdfAlgorithm::HkdfSha256 => sha256_expand(prk, info, output_size),
            KdfAlgorithm::HkdfSha384 => sha384_expand(prk, info, output_size),
            KdfAlgorithm::HkdfSha512 => sha512_expand(prk, info, output_size),
        }
    }

    fn kem_derive(alg: KemAlgorithm, pk: &[u8], sk: &[u8]) -> Result<Vec<u8>, Error> {
        match alg {
            KemAlgorithm::DhKem25519 => {
                if sk.len() != 32 {
                    return Err(Error::KemInvalidSecretKey);
                }
                if pk.len() != 32 {
                    return Err(Error::KemInvalidPublicKey);
                }
                let mut sk_array = [0u8; 32];
                sk_array.clone_from_slice(sk);
                let mut pk_array = [0u8; 32];
                pk_array.clone_from_slice(pk);
                let sk = X25519StaticSecret::from(sk_array);
                Ok(sk
                    .diffie_hellman(&X25519PublicKey::from(pk_array))
                    .as_bytes()
                    .to_vec())
            }
            KemAlgorithm::DhKemP256 => {
                let sk = SecretKey::from_bytes(sk).map_err(|_| Error::KemInvalidSecretKey)?;
                let pk = PublicKey::from_sec1_bytes(pk).map_err(|_| Error::KemInvalidPublicKey)?;
                Ok(diffie_hellman(sk.to_secret_scalar(), pk.as_affine())
                    .as_bytes()
                    .as_slice()
                    .into())
            }
            _ => Err(Error::UnknownKemAlgorithm),
        }
    }

    fn kem_derive_base(alg: KemAlgorithm, sk: &[u8]) -> Result<Vec<u8>, Error> {
        match alg {
            KemAlgorithm::DhKem25519 => {
                if sk.len() != 32 {
                    return Err(Error::KemInvalidSecretKey);
                }
                let mut sk_array = [0u8; 32];
                sk_array.clone_from_slice(sk);
                let sk = X25519StaticSecret::from(sk_array);
                Ok(X25519PublicKey::from(&sk).as_bytes().to_vec())
            }
            KemAlgorithm::DhKemP256 => {
                let sk = SecretKey::from_bytes(sk).map_err(|_| Error::KemInvalidSecretKey)?;
                Ok(EncodedPoint::encode(
                    PublicKey::from_secret_scalar(&sk.to_secret_scalar()),
                    false,
                )
                .as_bytes()
                .into())
            }
            _ => Err(Error::UnknownKemAlgorithm),
        }
    }

    fn kem_key_gen(alg: KemAlgorithm, prng: &mut Self::HpkePrng) -> Result<Vec<u8>, Error> {
        let mut rng = prng.rng.write().unwrap();
        match alg {
            KemAlgorithm::DhKem25519 => Ok(X25519StaticSecret::new(&mut *rng).to_bytes().to_vec()),
            KemAlgorithm::DhKemP256 => {
                Ok(SecretKey::random(&mut *rng).to_bytes().as_slice().into())
            }
            _ => Err(Error::UnknownKemAlgorithm),
        }
    }

    fn kem_validate_sk(alg: KemAlgorithm, sk: &[u8]) -> Result<Vec<u8>, Error> {
        match alg {
            KemAlgorithm::DhKemP256 => SecretKey::from_bytes(sk)
                .map_err(|_| Error::KemInvalidSecretKey)
                .map(|_| sk.into()),
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
        match alg {
            AeadAlgorithm::Aes128Gcm => aes128_seal(key, nonce, aad, msg),
            AeadAlgorithm::Aes256Gcm => aes256_seal(key, nonce, aad, msg),
            AeadAlgorithm::ChaCha20Poly1305 => chacha_seal(key, nonce, aad, msg),
            AeadAlgorithm::HpkeExport => Err(Error::UnknownAeadAlgorithm),
        }
    }

    fn aead_open(
        alg: AeadAlgorithm,
        key: &[u8],
        nonce: &[u8],
        aad: &[u8],
        msg: &[u8],
    ) -> Result<Vec<u8>, Error> {
        match alg {
            AeadAlgorithm::Aes128Gcm => aes128_open(alg, key, nonce, aad, msg),
            AeadAlgorithm::Aes256Gcm => aes256_open(alg, key, nonce, aad, msg),
            AeadAlgorithm::ChaCha20Poly1305 => chacha_open(alg, key, nonce, aad, msg),
            AeadAlgorithm::HpkeExport => Err(Error::UnknownAeadAlgorithm),
        }
    }

    type HpkePrng = HpkeRustCryptoPrng;

    fn prng() -> Self::HpkePrng {
        #[cfg(feature = "deterministic-prng")]
        {
            let mut fake_rng = vec![0u8; 256];
            rand_chacha::ChaCha20Rng::from_entropy().fill_bytes(&mut fake_rng);
            HpkeRustCryptoPrng {
                fake_rng,
                rng: RwLock::new(rand_chacha::ChaCha20Rng::from_entropy()),
            }
        }
        #[cfg(not(feature = "deterministic-prng"))]
        HpkeRustCryptoPrng {
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
            AeadAlgorithm::Aes128Gcm
            | AeadAlgorithm::Aes256Gcm
            | AeadAlgorithm::ChaCha20Poly1305 => Ok(()),
            AeadAlgorithm::HpkeExport => Err(Error::UnknownAeadAlgorithm),
        }
    }
}

impl RngCore for HpkeRustCryptoPrng {
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

impl CryptoRng for HpkeRustCryptoPrng {}

impl HpkeTestRng for HpkeRustCryptoPrng {
    #[cfg(feature = "deterministic-prng")]
    fn try_fill_test_bytes(&mut self, dest: &mut [u8]) -> Result<(), rand::Error> {
        // Here we fake our randomness for testing.
        if dest.len() > self.fake_rng.len() {
            return Err(rand::Error::new(Error::InsufficientRandomness));
        }
        dest.clone_from_slice(&self.fake_rng.split_off(self.fake_rng.len() - dest.len()));
        Ok(())
    }

    #[cfg(feature = "deterministic-prng")]
    fn seed(&mut self, seed: &[u8]) {
        self.fake_rng = seed.to_vec();
    }
    #[cfg(not(feature = "deterministic-prng"))]
    fn try_fill_test_bytes(&mut self, dest: &mut [u8]) -> Result<(), rand::Error> {
        self.rng.write().unwrap().try_fill_bytes(dest)
    }

    #[cfg(not(feature = "deterministic-prng"))]
    fn seed(&mut self, _: &[u8]) {}
}
