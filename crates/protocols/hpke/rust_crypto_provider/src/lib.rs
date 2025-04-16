#![doc = include_str!("../Readme.md")]
#![cfg_attr(not(test), no_std)]

extern crate alloc;

use alloc::{string::String, vec::Vec};
use core::fmt::Display;

use hpke_rs_crypto::{
    error::Error,
    types::{AeadAlgorithm, KdfAlgorithm, KemAlgorithm},
    CryptoRng, HpkeCrypto, HpkeTestRng, RngCore,
};
use p256::{
    elliptic_curve::ecdh::diffie_hellman as p256diffie_hellman, PublicKey as p256PublicKey,
    SecretKey as p256SecretKey,
};

use k256::{
    elliptic_curve::{ecdh::diffie_hellman as k256diffie_hellman, sec1::ToEncodedPoint},
    PublicKey as k256PublicKey, SecretKey as k256SecretKey,
};

use rand_core::SeedableRng;
use x25519_dalek::{PublicKey as X25519PublicKey, StaticSecret as X25519StaticSecret};

mod aead;
mod hkdf;
use crate::aead::*;
use crate::hkdf::*;

/// The Rust Crypto HPKE Provider
#[derive(Debug)]
pub struct HpkeRustCrypto {}

/// The PRNG for the Rust Crypto Provider.
pub struct HpkeRustCryptoPrng {
    rng: rand_chacha::ChaCha20Rng,
    #[cfg(feature = "deterministic-prng")]
    fake_rng: Vec<u8>,
}

impl HpkeCrypto for HpkeRustCrypto {
    fn name() -> String {
        "RustCrypto".into()
    }

    fn kdf_extract(alg: KdfAlgorithm, salt: &[u8], ikm: &[u8]) -> Result<Vec<u8>, Error> {
        Ok(match alg {
            KdfAlgorithm::HkdfSha256 => sha256_extract(salt, ikm),
            KdfAlgorithm::HkdfSha384 => sha384_extract(salt, ikm),
            KdfAlgorithm::HkdfSha512 => sha512_extract(salt, ikm),
        })
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

    fn dh(alg: KemAlgorithm, pk: &[u8], sk: &[u8]) -> Result<Vec<u8>, Error> {
        match alg {
            KemAlgorithm::DhKem25519 => {
                if sk.len() != 32 {
                    return Err(Error::KemInvalidSecretKey);
                }
                if pk.len() != 32 {
                    return Err(Error::KemInvalidPublicKey);
                }
                assert!(pk.len() == 32);
                assert!(sk.len() == 32);
                let sk_array: [u8; 32] = sk.try_into().map_err(|_| Error::KemInvalidSecretKey)?;
                let pk_array: [u8; 32] = pk.try_into().map_err(|_| Error::KemInvalidPublicKey)?;
                let sk = X25519StaticSecret::from(sk_array);
                Ok(sk
                    .diffie_hellman(&X25519PublicKey::from(pk_array))
                    .as_bytes()
                    .to_vec())
            }
            KemAlgorithm::DhKemP256 => {
                let sk = p256SecretKey::from_slice(sk).map_err(|_| Error::KemInvalidSecretKey)?;
                let pk =
                    p256PublicKey::from_sec1_bytes(pk).map_err(|_| Error::KemInvalidPublicKey)?;
                Ok(p256diffie_hellman(sk.to_nonzero_scalar(), pk.as_affine())
                    .raw_secret_bytes()
                    .as_slice()
                    .into())
            }
            KemAlgorithm::DhKemK256 => {
                let sk = k256SecretKey::from_slice(sk).map_err(|_| Error::KemInvalidSecretKey)?;
                let pk =
                    k256PublicKey::from_sec1_bytes(pk).map_err(|_| Error::KemInvalidPublicKey)?;
                Ok(k256diffie_hellman(sk.to_nonzero_scalar(), pk.as_affine())
                    .raw_secret_bytes()
                    .as_slice()
                    .into())
            }
            _ => Err(Error::UnknownKemAlgorithm),
        }
    }

    fn kem_key_gen_derand(_alg: KemAlgorithm, _seed: &[u8]) -> Result<(Vec<u8>, Vec<u8>), Error> {
        // No ciphersuite uses this.
        return Err(Error::UnsupportedKemOperation);
    }

    fn kem_encaps(
        _alg: KemAlgorithm,
        _pk_r: &[u8],
        _prng: &mut Self::HpkePrng,
    ) -> Result<(Vec<u8>, Vec<u8>), Error> {
        // No ciphersuite uses this.
        return Err(Error::UnsupportedKemOperation);
    }

    fn kem_decaps(_alg: KemAlgorithm, _ct: &[u8], _sk_r: &[u8]) -> Result<Vec<u8>, Error> {
        // No ciphersuite uses this.
        return Err(Error::UnsupportedKemOperation);
    }

    fn secret_to_public(alg: KemAlgorithm, sk: &[u8]) -> Result<Vec<u8>, Error> {
        match alg {
            KemAlgorithm::DhKem25519 => {
                if sk.len() != 32 {
                    return Err(Error::KemInvalidSecretKey);
                }
                assert!(sk.len() == 32);
                let sk_array: [u8; 32] = sk.try_into().map_err(|_| Error::KemInvalidSecretKey)?;
                let sk = X25519StaticSecret::from(sk_array);
                Ok(X25519PublicKey::from(&sk).as_bytes().to_vec())
            }
            KemAlgorithm::DhKemP256 => {
                let sk = p256SecretKey::from_slice(sk).map_err(|_| Error::KemInvalidSecretKey)?;
                Ok(sk.public_key().to_encoded_point(false).as_bytes().into())
            }
            KemAlgorithm::DhKemK256 => {
                let sk = k256SecretKey::from_slice(sk).map_err(|_| Error::KemInvalidSecretKey)?;
                Ok(sk.public_key().to_encoded_point(false).as_bytes().into())
            }
            _ => Err(Error::UnsupportedKemOperation),
        }
    }

    fn kem_key_gen(
        alg: KemAlgorithm,
        prng: &mut Self::HpkePrng,
    ) -> Result<(Vec<u8>, Vec<u8>), Error> {
        let rng = &mut prng.rng;
        match alg {
            KemAlgorithm::DhKem25519 => {
                let sk = X25519StaticSecret::random_from_rng(&mut *rng);
                let pk = X25519PublicKey::from(&sk).as_bytes().to_vec();
                let sk = sk.to_bytes().to_vec();
                Ok((pk, sk))
            }
            KemAlgorithm::DhKemP256 => {
                let sk = p256SecretKey::random(&mut *rng);
                let pk = sk.public_key().to_encoded_point(false).as_bytes().into();
                let sk = sk.to_bytes().as_slice().into();
                Ok((pk, sk))
            }
            KemAlgorithm::DhKemK256 => {
                let sk = k256SecretKey::random(&mut *rng);
                let pk = sk.public_key().to_encoded_point(false).as_bytes().into();
                let sk = sk.to_bytes().as_slice().into();
                Ok((pk, sk))
            }
            _ => Err(Error::UnknownKemAlgorithm),
        }
    }

    fn dh_validate_sk(alg: KemAlgorithm, sk: &[u8]) -> Result<Vec<u8>, Error> {
        match alg {
            KemAlgorithm::DhKemP256 => p256SecretKey::from_slice(sk)
                .map_err(|_| Error::KemInvalidSecretKey)
                .map(|_| sk.into()),
            KemAlgorithm::DhKemK256 => k256SecretKey::from_slice(sk)
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
            let mut fake_rng = alloc::vec![0u8; 256];
            rand_chacha::ChaCha20Rng::from_entropy().fill_bytes(&mut fake_rng);
            HpkeRustCryptoPrng {
                fake_rng,
                rng: rand_chacha::ChaCha20Rng::from_entropy(),
            }
        }
        #[cfg(not(feature = "deterministic-prng"))]
        HpkeRustCryptoPrng {
            rng: rand_chacha::ChaCha20Rng::from_entropy(),
        }
    }

    /// Returns an error if the KDF algorithm is not supported by this crypto provider.
    fn supports_kdf(_: KdfAlgorithm) -> Result<(), Error> {
        Ok(())
    }

    /// Returns an error if the KEM algorithm is not supported by this crypto provider.
    fn supports_kem(alg: KemAlgorithm) -> Result<(), Error> {
        match alg {
            KemAlgorithm::DhKem25519 | KemAlgorithm::DhKemP256 | KemAlgorithm::DhKemK256 => Ok(()),
            _ => Err(Error::UnknownKemAlgorithm),
        }
    }

    /// Returns an error if the AEAD algorithm is not supported by this crypto provider.
    fn supports_aead(alg: AeadAlgorithm) -> Result<(), Error> {
        match alg {
            AeadAlgorithm::Aes128Gcm
            | AeadAlgorithm::Aes256Gcm
            | AeadAlgorithm::ChaCha20Poly1305
            | AeadAlgorithm::HpkeExport => Ok(()),
        }
    }
}

// We need to implement the old and new traits here because the crytpo uses the
// old one.

impl rand_old::RngCore for HpkeRustCryptoPrng {
    fn next_u32(&mut self) -> u32 {
        self.rng.next_u32()
    }

    fn next_u64(&mut self) -> u64 {
        self.rng.next_u64()
    }

    fn fill_bytes(&mut self, dest: &mut [u8]) {
        self.rng.fill_bytes(dest);
    }

    fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), rand_core::Error> {
        self.rng.try_fill_bytes(dest)
    }
}

impl rand_old::CryptoRng for HpkeRustCryptoPrng {}

use rand_old::RngCore as _;

impl RngCore for HpkeRustCryptoPrng {
    fn next_u32(&mut self) -> u32 {
        self.rng.next_u32()
    }

    fn next_u64(&mut self) -> u64 {
        self.rng.next_u64()
    }

    fn fill_bytes(&mut self, dest: &mut [u8]) {
        self.rng.fill_bytes(dest);
    }
}

impl CryptoRng for HpkeRustCryptoPrng {}

impl HpkeTestRng for HpkeRustCryptoPrng {
    #[cfg(feature = "deterministic-prng")]
    fn try_fill_test_bytes(&mut self, dest: &mut [u8]) -> Result<(), rand_old::Error> {
        // Here we fake our randomness for testing.
        if dest.len() > self.fake_rng.len() {
            return Err(rand_core::Error::new(Error::InsufficientRandomness));
        }
        dest.clone_from_slice(&self.fake_rng.split_off(self.fake_rng.len() - dest.len()));
        Ok(())
    }

    #[cfg(feature = "deterministic-prng")]
    fn seed(&mut self, seed: &[u8]) {
        self.fake_rng = seed.to_vec();
    }
    #[cfg(not(feature = "deterministic-prng"))]
    fn try_fill_test_bytes(&mut self, dest: &mut [u8]) -> Result<(), rand_old::Error> {
        self.rng.try_fill_bytes(dest)
    }

    #[cfg(not(feature = "deterministic-prng"))]
    fn seed(&mut self, _: &[u8]) {}

    type Error = rand_old::Error;
}

impl Display for HpkeRustCrypto {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}", Self::name())
    }
}
