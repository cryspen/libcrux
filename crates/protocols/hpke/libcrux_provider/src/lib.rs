#![doc = include_str!("../Readme.md")]

use std::{fmt::Display, sync::RwLock};

use hpke_rs_crypto::{
    error::Error,
    types::{AeadAlgorithm, KdfAlgorithm, KemAlgorithm},
    CryptoRng, HpkeCrypto, HpkeTestRng,
};

use rand::SeedableRng;

/// The Libcrux HPKE Provider
#[derive(Debug)]
pub struct HpkeLibcrux {}

/// The PRNG for the Libcrux Provider.
pub struct HpkeLibcruxPrng {
    #[cfg(feature = "deterministic-prng")]
    fake_rng: Vec<u8>,
    rng: RwLock<rand_chacha::ChaCha20Rng>,
}

impl HpkeCrypto for HpkeLibcrux {
    fn name() -> String {
        "Libcrux".into()
    }

    fn kdf_extract(alg: KdfAlgorithm, salt: &[u8], ikm: &[u8]) -> Result<Vec<u8>, Error> {
        let alg = kdf_algorithm_to_libcrux_hkdf_algorithm(alg);
        libcrux_hkdf::extract(alg, salt, ikm)
            .map_err(|e| Error::CryptoLibraryError(format!("KDF extract error: {:?}", e)))
    }

    fn kdf_expand(
        alg: KdfAlgorithm,
        prk: &[u8],
        info: &[u8],
        output_size: usize,
    ) -> Result<Vec<u8>, Error> {
        let alg = kdf_algorithm_to_libcrux_hkdf_algorithm(alg);
        libcrux_hkdf::expand(alg, prk, info, output_size)
            .map_err(|e| Error::CryptoLibraryError(format!("KDF expand error: {:?}", e)))
    }

    fn dh(alg: KemAlgorithm, pk: &[u8], sk: &[u8]) -> Result<Vec<u8>, Error> {
        let alg = kem_key_type_to_ecdh_alg(alg)?;

        libcrux_ecdh::derive(alg, pk, sk)
            .map_err(|e| Error::CryptoLibraryError(format!("ECDH derive error: {:?}", e)))
            .map(|mut p| {
                if alg == libcrux_ecdh::Algorithm::P256 {
                    p.truncate(32);
                    p
                } else {
                    p
                }
            })
    }

    fn secret_to_public(alg: KemAlgorithm, sk: &[u8]) -> Result<Vec<u8>, Error> {
        let alg = kem_key_type_to_ecdh_alg(alg)?;

        kem_ecdh_secret_to_public(alg, sk)
    }

    fn kem_key_gen(
        alg: KemAlgorithm,
        prng: &mut Self::HpkePrng,
    ) -> Result<(Vec<u8>, Vec<u8>), Error> {
        match alg {
            KemAlgorithm::XWingDraft06 => {
                libcrux_kem::key_gen(libcrux_kem::Algorithm::XWingKemDraft06, prng)
                    .map(|(sk, pk)| (pk.encode(), sk.encode()))
                    .map_err(|e| Error::CryptoLibraryError(format!("KEM key gen error: {:?}", e)))
            }
            other_alg => {
                // ECDH only
                let ecdh_alg = kem_key_type_to_ecdh_alg(other_alg)?;
                let sk = libcrux_ecdh::generate_secret(ecdh_alg, prng).map_err(|e| {
                    Error::CryptoLibraryError(format!("KEM key gen error: {:?}", e))
                })?;

                let pk = kem_ecdh_secret_to_public(ecdh_alg, &sk)?;

                Ok((pk, sk))
            }
        }
    }

    fn kem_key_gen_derand(alg: KemAlgorithm, seed: &[u8]) -> Result<(Vec<u8>, Vec<u8>), Error> {
        let alg = kem_key_type_to_libcrux_alg(alg)?;

        libcrux_kem::key_gen_derand(alg, seed)
            .map_err(|e| Error::CryptoLibraryError(format!("KEM key gen error: {:?}", e)))
            .map(|(sk, pk)| (pk.encode(), sk.encode()))
    }

    fn kem_encaps(
        alg: KemAlgorithm,
        pk_r: &[u8],
        prng: &mut Self::HpkePrng,
    ) -> Result<(Vec<u8>, Vec<u8>), Error> {
        let alg = kem_key_type_to_libcrux_alg(alg)?;

        let pk =
            libcrux_kem::PublicKey::decode(alg, pk_r).map_err(|_| Error::KemInvalidPublicKey)?;
        pk.encapsulate(prng)
            .map_err(|e| Error::CryptoLibraryError(format!("Encaps error {:?}", e)))
            .map(|(ss, ct)| (ss.encode(), ct.encode()))
    }

    fn kem_decaps(alg: KemAlgorithm, ct: &[u8], sk_r: &[u8]) -> Result<Vec<u8>, Error> {
        let alg = kem_key_type_to_libcrux_alg(alg)?;

        let ct = libcrux_kem::Ct::decode(alg, ct).map_err(|_| Error::AeadInvalidCiphertext)?;
        let sk =
            libcrux_kem::PrivateKey::decode(alg, sk_r).map_err(|_| Error::KemInvalidSecretKey)?;
        ct.decapsulate(&sk)
            .map_err(|e| Error::CryptoLibraryError(format!("Decaps error {:?}", e)))
            .map(|ss| ss.encode())
    }

    fn dh_validate_sk(alg: KemAlgorithm, sk: &[u8]) -> Result<Vec<u8>, Error> {
        match alg {
            KemAlgorithm::DhKemP256 => libcrux_ecdh::p256::validate_scalar_slice(&sk)
                .map_err(|e| Error::CryptoLibraryError(format!("ECDH invalid sk error: {:?}", e)))
                .map(|sk| sk.0.to_vec()),
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
        // only chacha20poly1305 is supported
        if !matches!(alg, AeadAlgorithm::ChaCha20Poly1305) {
            return Err(Error::UnknownAeadAlgorithm);
        }

        let iv = <&[u8; 12]>::try_from(nonce).map_err(|_| Error::AeadInvalidNonce)?;

        // TODO: instead, use key conversion from the libcrux-chacha20poly1305 crate, when available,
        let key = <&[u8; 32]>::try_from(key)
            .map_err(|_| Error::CryptoLibraryError("AEAD invalid key length".into()))?;

        let mut msg_ctx: Vec<u8> = vec![0; msg.len() + 16];
        libcrux_chacha20poly1305::encrypt(key, msg, &mut msg_ctx, aad, iv)
            .map_err(|_| Error::CryptoLibraryError("Invalid configuration".into()))?;

        Ok(msg_ctx)
    }

    fn aead_open(
        alg: AeadAlgorithm,
        key: &[u8],
        nonce: &[u8],
        aad: &[u8],
        cipher_txt: &[u8],
    ) -> Result<Vec<u8>, Error> {
        // only chacha20poly1305 is supported
        if !matches!(alg, AeadAlgorithm::ChaCha20Poly1305) {
            return Err(Error::UnknownAeadAlgorithm);
        }
        if cipher_txt.len() < 16 {
            return Err(Error::AeadInvalidCiphertext);
        }

        let boundary = cipher_txt.len() - 16;

        let mut ptext = vec![0; boundary];

        let iv = <&[u8; 12]>::try_from(nonce).map_err(|_| Error::AeadInvalidNonce)?;

        // TODO: instead, use key conversion from the libcrux-chacha20poly1305 crate, when available,
        let key = <&[u8; 32]>::try_from(key)
            .map_err(|_| Error::CryptoLibraryError("AEAD invalid key length".into()))?;
        libcrux_chacha20poly1305::decrypt(key, &mut ptext, cipher_txt, aad, iv).map_err(
            |e| match e {
                libcrux_chacha20poly1305::AeadError::InvalidCiphertext => {
                    Error::CryptoLibraryError(format!("AEAD decryption error: {:?}", e))
                }
                _ => Error::CryptoLibraryError("Invalid configuration".into()),
            },
        )?;

        Ok(ptext)
    }

    type HpkePrng = HpkeLibcruxPrng;

    fn prng() -> Self::HpkePrng {
        #[cfg(feature = "deterministic-prng")]
        {
            use rand::TryRngCore;
            let mut fake_rng = vec![0u8; 256];
            rand_chacha::ChaCha20Rng::from_os_rng()
                .try_fill_bytes(&mut fake_rng)
                .unwrap();
            HpkeLibcruxPrng {
                fake_rng,
                rng: RwLock::new(rand_chacha::ChaCha20Rng::from_os_rng()),
            }
        }
        #[cfg(not(feature = "deterministic-prng"))]
        HpkeLibcruxPrng {
            rng: RwLock::new(rand_chacha::ChaCha20Rng::from_os_rng()),
        }
    }

    /// Returns an error if the KDF algorithm is not supported by this crypto provider.
    fn supports_kdf(_: KdfAlgorithm) -> Result<(), Error> {
        Ok(())
    }

    /// Returns an error if the KEM algorithm is not supported by this crypto provider.
    fn supports_kem(alg: KemAlgorithm) -> Result<(), Error> {
        match alg {
            KemAlgorithm::DhKem25519 | KemAlgorithm::DhKemP256 | KemAlgorithm::XWingDraft06 => {
                Ok(())
            }
            _ => Err(Error::UnknownKemAlgorithm),
        }
    }

    /// Returns an error if the AEAD algorithm is not supported by this crypto provider.
    fn supports_aead(alg: AeadAlgorithm) -> Result<(), Error> {
        match alg {
            // Don't support Aes
            AeadAlgorithm::Aes128Gcm | AeadAlgorithm::Aes256Gcm => Err(Error::UnknownAeadAlgorithm),
            AeadAlgorithm::ChaCha20Poly1305 => Ok(()),
            AeadAlgorithm::HpkeExport => Ok(()),
        }
    }
}

#[inline(always)]
fn kem_ecdh_secret_to_public(alg: libcrux_ecdh::Algorithm, sk: &[u8]) -> Result<Vec<u8>, Error> {
    libcrux_ecdh::secret_to_public(alg, sk)
        .map_err(|e| Error::CryptoLibraryError(format!("ECDH derive base error: {:?}", e)))
        .map(|p| {
            if alg == libcrux_ecdh::Algorithm::P256 {
                nist_format_uncompressed(p)
            } else {
                p
            }
        })
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
fn kdf_algorithm_to_libcrux_hkdf_algorithm(alg: KdfAlgorithm) -> libcrux_hkdf::Algorithm {
    match alg {
        KdfAlgorithm::HkdfSha256 => libcrux_hkdf::Algorithm::Sha256,
        KdfAlgorithm::HkdfSha384 => libcrux_hkdf::Algorithm::Sha384,
        KdfAlgorithm::HkdfSha512 => libcrux_hkdf::Algorithm::Sha512,
    }
}

#[inline(always)]
fn kem_key_type_to_libcrux_alg(alg: KemAlgorithm) -> Result<libcrux_kem::Algorithm, Error> {
    match alg {
        KemAlgorithm::DhKem25519 => Ok(libcrux_kem::Algorithm::X25519),
        KemAlgorithm::DhKemP256 => Ok(libcrux_kem::Algorithm::Secp256r1),
        KemAlgorithm::XWingDraft06 => Ok(libcrux_kem::Algorithm::XWingKemDraft06),
        _ => Err(Error::UnknownKemAlgorithm),
    }
}

#[inline(always)]
fn kem_key_type_to_ecdh_alg(alg: KemAlgorithm) -> Result<libcrux_ecdh::Algorithm, Error> {
    match alg {
        KemAlgorithm::DhKem25519 => Ok(libcrux_ecdh::Algorithm::X25519),
        KemAlgorithm::DhKemP256 => Ok(libcrux_ecdh::Algorithm::P256),
        _ => Err(Error::UnknownKemAlgorithm),
    }
}

impl hpke_rs_crypto::RngCore for HpkeLibcruxPrng {
    fn next_u32(&mut self) -> u32 {
        self.rng.write().unwrap().next_u32()
    }

    fn next_u64(&mut self) -> u64 {
        self.rng.write().unwrap().next_u64()
    }

    fn fill_bytes(&mut self, dest: &mut [u8]) {
        self.rng.write().unwrap().fill_bytes(dest)
    }
}
impl CryptoRng for HpkeLibcruxPrng {}

impl HpkeTestRng for HpkeLibcruxPrng {
    type Error = Error;

    #[cfg(feature = "deterministic-prng")]
    fn try_fill_test_bytes(&mut self, dest: &mut [u8]) -> Result<(), Error> {
        // Here we fake our randomness for testing.
        if dest.len() > self.fake_rng.len() {
            return Err(Error::InsufficientRandomness);
        }
        dest.clone_from_slice(&self.fake_rng.split_off(self.fake_rng.len() - dest.len()));
        Ok(())
    }
    #[cfg(not(feature = "deterministic-prng"))]
    fn try_fill_test_bytes(&mut self, dest: &mut [u8]) -> Result<(), Error> {
        use rand_core::TryRngCore;
        self.try_fill_bytes(dest)
            .map_err(|_| Error::InsufficientRandomness)
    }

    #[cfg(feature = "deterministic-prng")]
    fn seed(&mut self, seed: &[u8]) {
        self.fake_rng = seed.to_vec();
    }
    #[cfg(not(feature = "deterministic-prng"))]
    fn seed(&mut self, _: &[u8]) {}
}

impl Display for HpkeLibcrux {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", Self::name())
    }
}
