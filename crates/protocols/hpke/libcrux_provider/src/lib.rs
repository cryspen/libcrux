#![doc = include_str!("../Readme.md")]
#![cfg_attr(not(test), no_std)]
extern crate alloc;

use alloc::{format, string::String, vec::Vec};
use core::fmt::Display;
use zeroize::Zeroize;

use hpke_rs_crypto::{
    error::Error,
    types::{AeadAlgorithm, KdfAlgorithm, KemAlgorithm},
    CryptoRng, HpkeCrypto, HpkeTestRng,
};

#[cfg(feature = "rustcrypto-p-curves")]
use p384::{
    elliptic_curve::{ecdh::diffie_hellman as p384diffie_hellman, sec1::ToSec1Point, Generate},
    PublicKey as P384PublicKey, SecretKey as P384SecretKey,
};
#[cfg(feature = "rustcrypto-p-curves")]
use p521::{
    elliptic_curve::ecdh::diffie_hellman as p521diffie_hellman, PublicKey as P521PublicKey,
    SecretKey as P521SecretKey,
};

use rand::{rngs::SysRng, Rng, SeedableRng};
use rand_core::UnwrapErr;

/// The Libcrux HPKE Provider
#[derive(Debug)]
pub struct HpkeLibcrux {}

/// The PRNG for the Libcrux Provider.
pub struct HpkeLibcruxPrng {
    #[cfg(feature = "deterministic-prng")]
    fake_rng: Vec<u8>,
    rng: rand_chacha::ChaCha20Rng,
}

impl Zeroize for HpkeLibcruxPrng {
    fn zeroize(&mut self) {
        // ChaCha20Rng doesn't implement zeroize and fake_rng is just for testing.
    }
}

impl HpkeCrypto for HpkeLibcrux {
    fn name() -> String {
        "Libcrux".into()
    }

    fn kdf_extract(alg: KdfAlgorithm, salt: &[u8], ikm: &[u8]) -> Result<Vec<u8>, Error> {
        let alg = kdf_algorithm_to_libcrux_hkdf_algorithm(alg);
        let mut prk = alloc::vec![0u8; alg.hash_len()];
        libcrux_hkdf::extract(alg, &mut prk, salt, ikm)
            .map_err(|e| Error::CryptoLibraryError(format!("KDF extract error: {:?}", e)))?;
        Ok(prk)
    }

    fn kdf_expand(
        alg: KdfAlgorithm,
        prk: &[u8],
        info: &[u8],
        output_size: usize,
    ) -> Result<Vec<u8>, Error> {
        let alg = kdf_algorithm_to_libcrux_hkdf_algorithm(alg);
        let mut okm = alloc::vec![0u8; output_size];
        libcrux_hkdf::expand(alg, &mut okm, prk, info)
            .map_err(|e| Error::CryptoLibraryError(format!("KDF expand error: {:?}", e)))?;
        Ok(okm)
    }

    fn dh(alg: KemAlgorithm, pk: &[u8], sk: &[u8]) -> Result<Vec<u8>, Error> {
        match alg {
            #[cfg(feature = "rustcrypto-p-curves")]
            KemAlgorithm::DhKemP384 => {
                let sk = P384SecretKey::from_slice(sk).map_err(|_| Error::KemInvalidSecretKey)?;
                let pk =
                    P384PublicKey::from_sec1_bytes(pk).map_err(|_| Error::KemInvalidPublicKey)?;
                Ok(p384diffie_hellman(sk.to_nonzero_scalar(), pk.as_affine())
                    .raw_secret_bytes()
                    .as_slice()
                    .into())
            }
            #[cfg(feature = "rustcrypto-p-curves")]
            KemAlgorithm::DhKemP521 => {
                let sk = P521SecretKey::from_slice(sk).map_err(|_| Error::KemInvalidSecretKey)?;
                let pk =
                    P521PublicKey::from_sec1_bytes(pk).map_err(|_| Error::KemInvalidPublicKey)?;
                Ok(p521diffie_hellman(sk.to_nonzero_scalar(), pk.as_affine())
                    .raw_secret_bytes()
                    .as_slice()
                    .into())
            }
            other => {
                let alg = kem_key_type_to_ecdh_alg(other)?;

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
        }
    }

    fn secret_to_public(alg: KemAlgorithm, sk: &[u8]) -> Result<Vec<u8>, Error> {
        match alg {
            #[cfg(feature = "rustcrypto-p-curves")]
            KemAlgorithm::DhKemP384 => {
                let sk = P384SecretKey::from_slice(sk).map_err(|_| Error::KemInvalidSecretKey)?;
                Ok(sk.public_key().to_sec1_point(false).as_bytes().into())
            }
            #[cfg(feature = "rustcrypto-p-curves")]
            KemAlgorithm::DhKemP521 => {
                let sk = P521SecretKey::from_slice(sk).map_err(|_| Error::KemInvalidSecretKey)?;
                Ok(sk.public_key().to_sec1_point(false).as_bytes().into())
            }
            other => {
                let alg = kem_key_type_to_ecdh_alg(other)?;
                kem_ecdh_secret_to_public(alg, sk)
            }
        }
    }

    fn kem_key_gen(
        alg: KemAlgorithm,
        prng: &mut Self::HpkePrng,
    ) -> Result<(Vec<u8>, Vec<u8>), Error> {
        match alg {
            #[cfg(feature = "draft-connolly-cfrg-hpke-mlkem")]
            KemAlgorithm::MlKem768 | KemAlgorithm::MlKem1024 => {
                let kem_alg = kem_key_type_to_libcrux_alg(alg)?;
                libcrux_kem::key_gen(kem_alg, prng)
                    .map(|(sk, pk)| (pk.encode(), sk.encode()))
                    .map_err(|e| Error::CryptoLibraryError(format!("KEM key gen error: {:?}", e)))
            }
            KemAlgorithm::XWingDraft06 => {
                let kem_alg = kem_key_type_to_libcrux_alg(alg)?;
                libcrux_kem::key_gen(kem_alg, prng)
                    .map(|(sk, pk)| (pk.encode(), sk.encode()))
                    .map_err(|e| Error::CryptoLibraryError(format!("KEM key gen error: {:?}", e)))
            }
            #[cfg(feature = "rustcrypto-p-curves")]
            KemAlgorithm::DhKemP384 => {
                let sk = P384SecretKey::generate_from_rng(&mut prng.rng);
                let pk = sk.public_key().to_sec1_point(false).as_bytes().into();
                let sk = sk.to_bytes().as_slice().into();
                Ok((pk, sk))
            }
            #[cfg(feature = "rustcrypto-p-curves")]
            KemAlgorithm::DhKemP521 => {
                let sk = P521SecretKey::generate_from_rng(&mut prng.rng);
                let pk = sk.public_key().to_sec1_point(false).as_bytes().into();
                let sk = sk.to_bytes().as_slice().into();
                Ok((pk, sk))
            }
            other_alg => {
                // ECDH only (libcrux curves)
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
        match alg {
            #[cfg(feature = "rustcrypto-p-curves")]
            KemAlgorithm::DhKemP384 => {
                let chacha_seed = p_curve_key_gen_seed(alg, seed)?;
                let mut rng = rand_chacha::ChaCha20Rng::from_seed(chacha_seed);
                let sk = P384SecretKey::generate_from_rng(&mut rng);
                let sk_bytes: Vec<u8> = sk.to_bytes().as_slice().into();
                if sk_bytes.iter().all(|&b| b == 0) {
                    return Err(Error::KemInvalidSecretKey);
                }
                let pk = sk.public_key().to_sec1_point(false).as_bytes().into();
                Ok((pk, sk_bytes))
            }
            #[cfg(feature = "rustcrypto-p-curves")]
            KemAlgorithm::DhKemP521 => {
                let chacha_seed = p_curve_key_gen_seed(alg, seed)?;
                let mut rng = rand_chacha::ChaCha20Rng::from_seed(chacha_seed);
                let sk = P521SecretKey::generate_from_rng(&mut rng);
                let sk_bytes: Vec<u8> = sk.to_bytes().as_slice().into();
                if sk_bytes.iter().all(|&b| b == 0) {
                    return Err(Error::KemInvalidSecretKey);
                }
                let pk = sk.public_key().to_sec1_point(false).as_bytes().into();
                Ok((pk, sk_bytes))
            }
            _ => {
                let alg = kem_key_type_to_libcrux_alg(alg)?;
                libcrux_kem::key_gen_derand(alg, seed)
                    .map_err(|e| Error::CryptoLibraryError(format!("KEM key gen error: {:?}", e)))
                    .map(|(sk, pk)| (pk.encode(), sk.encode()))
            }
        }
    }

    fn kem_encaps(
        alg: KemAlgorithm,
        pk_r: &[u8],
        prng: &mut Self::HpkePrng,
    ) -> Result<(Vec<u8>, Vec<u8>), Error> {
        match alg {
            #[cfg(feature = "rustcrypto-p-curves")]
            KemAlgorithm::DhKemP384 | KemAlgorithm::DhKemP521 => {
                let (enc, sk_e) = <HpkeLibcrux as HpkeCrypto>::kem_key_gen(alg, prng)?;
                let dh = <HpkeLibcrux as HpkeCrypto>::dh(alg, pk_r, &sk_e)?;
                let kem_context = concat(&[&enc, pk_r]);
                let ss = dh_kem_extract_and_expand(alg, &dh, &kem_context)?;
                Ok((ss, enc))
            }
            _ => {
                let alg = kem_key_type_to_libcrux_alg(alg)?;

                let pk = libcrux_kem::PublicKey::decode(alg, pk_r)
                    .map_err(|_| Error::KemInvalidPublicKey)?;
                pk.encapsulate(prng)
                    .map_err(|e| Error::CryptoLibraryError(format!("Encaps error {:?}", e)))
                    .map(|(ss, ct)| (ss.encode(), ct.encode()))
            }
        }
    }

    fn kem_decaps(alg: KemAlgorithm, ct: &[u8], sk_r: &[u8]) -> Result<Vec<u8>, Error> {
        match alg {
            #[cfg(feature = "rustcrypto-p-curves")]
            KemAlgorithm::DhKemP384 | KemAlgorithm::DhKemP521 => {
                let dh = <HpkeLibcrux as HpkeCrypto>::dh(alg, ct, sk_r)?;
                let pk_r = <HpkeLibcrux as HpkeCrypto>::secret_to_public(alg, sk_r)?;
                let kem_context = concat(&[ct, &pk_r]);
                dh_kem_extract_and_expand(alg, &dh, &kem_context)
            }
            _ => {
                let alg = kem_key_type_to_libcrux_alg(alg)?;

                let ct =
                    libcrux_kem::Ct::decode(alg, ct).map_err(|_| Error::AeadInvalidCiphertext)?;
                let sk = libcrux_kem::PrivateKey::decode(alg, sk_r)
                    .map_err(|_| Error::KemInvalidSecretKey)?;
                ct.decapsulate(&sk)
                    .map_err(|e| Error::CryptoLibraryError(format!("Decaps error {:?}", e)))
                    .map(|ss| ss.encode())
            }
        }
    }

    fn dh_validate_sk(alg: KemAlgorithm, sk: &[u8]) -> Result<Vec<u8>, Error> {
        match alg {
            KemAlgorithm::DhKemP256 => libcrux_ecdh::p256::validate_scalar_slice(sk)
                .map_err(|e| Error::CryptoLibraryError(format!("ECDH invalid sk error: {:?}", e)))
                .map(|sk| sk.0.to_vec()),
            #[cfg(feature = "rustcrypto-p-curves")]
            KemAlgorithm::DhKemP384 => P384SecretKey::from_slice(sk)
                .map_err(|_| Error::KemInvalidSecretKey)
                .map(|_| sk.into()),
            #[cfg(feature = "rustcrypto-p-curves")]
            KemAlgorithm::DhKemP521 => P521SecretKey::from_slice(sk)
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
        let alg = aead_alg(alg)?;

        use libcrux_traits::aead::typed_refs::Aead as _;

        // set up buffer for ctxt and tag
        let mut msg_ctx: Vec<u8> = alloc::vec![0; msg.len() + alg.tag_len()];
        let (ctxt, tag) = msg_ctx.split_at_mut(msg.len());

        // set up nonce
        let nonce = alg.new_nonce(nonce).map_err(|_| Error::AeadInvalidNonce)?;

        // set up key
        let key = alg
            .new_key(key)
            .map_err(|_| Error::CryptoLibraryError("AEAD invalid key length".into()))?;

        // set up tag
        let tag = alg
            .new_tag_mut(tag)
            .map_err(|_| Error::CryptoLibraryError("Invalid tag length".into()))?;

        key.encrypt(ctxt, tag, nonce, aad, msg)
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
        let alg = aead_alg(alg)?;

        use libcrux_traits::aead::typed_refs::{Aead as _, DecryptError};

        if cipher_txt.len() < alg.tag_len() {
            return Err(Error::AeadInvalidCiphertext);
        }

        let boundary = cipher_txt.len() - alg.tag_len();

        // set up buffers for ptext, ctext, and tag
        let mut ptext = alloc::vec![0; boundary];
        let (ctext, tag) = cipher_txt.split_at(boundary);

        // set up nonce
        let nonce = alg.new_nonce(nonce).map_err(|_| Error::AeadInvalidNonce)?;

        // set up key
        let key = alg
            .new_key(key)
            .map_err(|_| Error::CryptoLibraryError("AEAD invalid key length".into()))?;

        // set up tag
        let tag = alg
            .new_tag(tag)
            .map_err(|_| Error::CryptoLibraryError("Invalid tag length".into()))?;

        key.decrypt(&mut ptext, nonce, aad, ctext, tag)
            .map_err(|e| match e {
                DecryptError::InvalidTag => Error::AeadOpenError,
                _ => Error::CryptoLibraryError("Invalid configuration".into()),
            })?;

        Ok(ptext)
    }

    type HpkePrng = HpkeLibcruxPrng;

    fn prng() -> Self::HpkePrng {
        #[cfg(feature = "deterministic-prng")]
        {
            let mut fake_rng = alloc::vec![0u8; 256];
            rand_chacha::ChaCha20Rng::from_rng(&mut UnwrapErr(SysRng)).fill_bytes(&mut fake_rng);
            HpkeLibcruxPrng {
                fake_rng,
                rng: rand_chacha::ChaCha20Rng::from_rng(&mut UnwrapErr(SysRng)),
            }
        }

        #[cfg(not(feature = "deterministic-prng"))]
        HpkeLibcruxPrng {
            rng: rand_chacha::ChaCha20Rng::from_rng(&mut UnwrapErr(SysRng)),
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
            #[cfg(feature = "rustcrypto-p-curves")]
            KemAlgorithm::DhKemP384 | KemAlgorithm::DhKemP521 => Ok(()),
            #[cfg(feature = "draft-connolly-cfrg-hpke-mlkem")]
            KemAlgorithm::MlKem768 | KemAlgorithm::MlKem1024 => Ok(()),
            _ => Err(Error::UnknownKemAlgorithm),
        }
    }

    /// Returns an error if the AEAD algorithm is not supported by this crypto provider.
    fn supports_aead(alg: AeadAlgorithm) -> Result<(), Error> {
        match alg {
            AeadAlgorithm::Aes128Gcm | AeadAlgorithm::Aes256Gcm => Ok(()),
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

#[cfg(feature = "rustcrypto-p-curves")]
#[inline(always)]
fn dh_kem_extract_and_expand(
    alg: KemAlgorithm,
    dh: &[u8],
    kem_context: &[u8],
) -> Result<Vec<u8>, Error> {
    let kdf_alg: KdfAlgorithm = alg.into();
    let suite_id = kem_suite_id(alg);
    let eae_prk = labeled_extract(kdf_alg, &[], &suite_id, "eae_prk", dh)?;
    labeled_expand(
        kdf_alg,
        &eae_prk,
        &suite_id,
        "shared_secret",
        kem_context,
        alg.shared_secret_len(),
    )
}

#[cfg(feature = "rustcrypto-p-curves")]
#[inline(always)]
fn kem_suite_id(alg: KemAlgorithm) -> [u8; 5] {
    let kem_id = (alg as u16).to_be_bytes();
    [b'K', b'E', b'M', kem_id[0], kem_id[1]]
}

#[cfg(feature = "rustcrypto-p-curves")]
#[inline(always)]
fn labeled_extract(
    alg: KdfAlgorithm,
    salt: &[u8],
    suite_id: &[u8],
    label: &str,
    ikm: &[u8],
) -> Result<Vec<u8>, Error> {
    const HPKE_VERSION: &[u8] = b"HPKE-v1";

    let labeled_ikm = concat(&[HPKE_VERSION, suite_id, label.as_bytes(), ikm]);
    <HpkeLibcrux as HpkeCrypto>::kdf_extract(alg, salt, &labeled_ikm)
}

#[cfg(feature = "rustcrypto-p-curves")]
#[inline(always)]
fn labeled_expand(
    alg: KdfAlgorithm,
    prk: &[u8],
    suite_id: &[u8],
    label: &str,
    info: &[u8],
    len: usize,
) -> Result<Vec<u8>, Error> {
    const HPKE_VERSION: &[u8] = b"HPKE-v1";

    if len > u16::MAX.into() {
        return Err(Error::HpkeInvalidOutputLength);
    }

    let len_bytes = (len as u16).to_be_bytes();
    let labeled_info = concat(&[&len_bytes, HPKE_VERSION, suite_id, label.as_bytes(), info]);
    <HpkeLibcrux as HpkeCrypto>::kdf_expand(alg, prk, &labeled_info, len)
}

#[cfg(feature = "rustcrypto-p-curves")]
#[inline(always)]
fn p_curve_key_gen_seed(alg: KemAlgorithm, seed: &[u8]) -> Result<[u8; 32], Error> {
    if seed.len() != alg.private_key_len() {
        return Err(Error::InsufficientRandomness);
    }

    let kdf_alg: KdfAlgorithm = alg.into();
    let extracted = <HpkeLibcrux as HpkeCrypto>::kdf_extract(kdf_alg, &[], seed)?;
    extracted[..32]
        .try_into()
        .map_err(|_| Error::InsufficientRandomness)
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
        #[cfg(feature = "draft-connolly-cfrg-hpke-mlkem")]
        KemAlgorithm::MlKem768 => Ok(libcrux_kem::Algorithm::MlKem768),
        #[cfg(feature = "draft-connolly-cfrg-hpke-mlkem")]
        KemAlgorithm::MlKem1024 => Ok(libcrux_kem::Algorithm::MlKem1024),
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

#[inline(always)]
fn aead_alg(alg_type: AeadAlgorithm) -> Result<libcrux_aead::Aead, Error> {
    match alg_type {
        AeadAlgorithm::ChaCha20Poly1305 => Ok(libcrux_aead::Aead::ChaCha20Poly1305),
        AeadAlgorithm::Aes128Gcm => Ok(libcrux_aead::Aead::AesGcm128),
        AeadAlgorithm::Aes256Gcm => Ok(libcrux_aead::Aead::AesGcm256),
        _ => Err(Error::UnknownAeadAlgorithm),
    }
}

#[cfg(feature = "rustcrypto-p-curves")]
#[inline(always)]
fn concat(values: &[&[u8]]) -> Vec<u8> {
    values.join(&[][..])
}

impl hpke_rs_crypto::RngCore for HpkeLibcruxPrng {
    fn next_u32(&mut self) -> u32 {
        self.rng.next_u32()
    }

    fn next_u64(&mut self) -> u64 {
        self.rng.next_u64()
    }

    fn fill_bytes(&mut self, dest: &mut [u8]) {
        self.rng.fill_bytes(dest)
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
        use hpke_rs_crypto::RngCore;

        self.fill_bytes(dest);
        Ok(())
    }

    #[cfg(feature = "deterministic-prng")]
    fn seed(&mut self, seed: &[u8]) {
        self.fake_rng = seed.to_vec();
    }
    #[cfg(not(feature = "deterministic-prng"))]
    fn seed(&mut self, _: &[u8]) {}
}

impl Display for HpkeLibcrux {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}", Self::name())
    }
}
