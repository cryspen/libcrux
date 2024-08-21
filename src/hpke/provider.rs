use std::io::Write as _;

#[derive(Debug)]
pub struct Provider;

fn kdf_alg(alg: hpke_rs_crypto::types::KdfAlgorithm) -> crate::hkdf::Algorithm {
    match alg {
        hpke_rs_crypto::types::KdfAlgorithm::HkdfSha256 => crate::hkdf::Algorithm::Sha256,
        hpke_rs_crypto::types::KdfAlgorithm::HkdfSha384 => crate::hkdf::Algorithm::Sha384,
        hpke_rs_crypto::types::KdfAlgorithm::HkdfSha512 => crate::hkdf::Algorithm::Sha512,
    }
}

fn kem_alg(alg: hpke_rs_crypto::types::KemAlgorithm) -> crate::kem::Algorithm {
    match alg {
        hpke_rs_crypto::types::KemAlgorithm::DhKemP256 => crate::kem::Algorithm::Secp256r1,
        hpke_rs_crypto::types::KemAlgorithm::DhKemP384 => crate::kem::Algorithm::Secp384r1,
        hpke_rs_crypto::types::KemAlgorithm::DhKemP521 => crate::kem::Algorithm::Secp521r1,
        hpke_rs_crypto::types::KemAlgorithm::DhKem25519 => crate::kem::Algorithm::X25519,
        hpke_rs_crypto::types::KemAlgorithm::DhKem448 => crate::kem::Algorithm::X448,
    }
}

fn aead_key(
    alg: hpke_rs_crypto::types::AeadAlgorithm,
    key: &[u8],
) -> Result<crate::aead::Key, hpke_rs_crypto::error::Error> {
    match alg {
        hpke_rs_crypto::types::AeadAlgorithm::Aes128Gcm => key
            .try_into()
            .map_err(|_| {
                hpke_rs_crypto::error::Error::CryptoLibraryError("invalid key length".to_string())
            })
            .map(crate::aead::Aes128Key)
            .map(crate::aead::Key::Aes128),
        hpke_rs_crypto::types::AeadAlgorithm::Aes256Gcm => key
            .try_into()
            .map_err(|_| {
                hpke_rs_crypto::error::Error::CryptoLibraryError("invalid key length".to_string())
            })
            .map(crate::aead::Aes256Key)
            .map(crate::aead::Key::Aes256),
        hpke_rs_crypto::types::AeadAlgorithm::ChaCha20Poly1305 => key
            .try_into()
            .map_err(|_| {
                hpke_rs_crypto::error::Error::CryptoLibraryError("invalid key length".to_string())
            })
            .map(crate::aead::Chacha20Key)
            .map(crate::aead::Key::Chacha20Poly1305),
        hpke_rs_crypto::types::AeadAlgorithm::HpkeExport => {
            Err(hpke_rs_crypto::error::Error::UnknownAeadAlgorithm)
        }
    }
}

impl hpke_rs_crypto::HpkeCrypto for Provider {
    type HpkePrng = crate::drbg::Drbg;

    fn name() -> String {
        "libcrux".to_string()
    }

    fn supports_kdf(
        alg: hpke_rs_crypto::types::KdfAlgorithm,
    ) -> Result<(), hpke_rs_crypto::error::Error> {
        match alg {
            hpke_rs_crypto::types::KdfAlgorithm::HkdfSha256
            | hpke_rs_crypto::types::KdfAlgorithm::HkdfSha384
            | hpke_rs_crypto::types::KdfAlgorithm::HkdfSha512 => Ok(()),
        }
    }

    fn supports_kem(
        alg: hpke_rs_crypto::types::KemAlgorithm,
    ) -> Result<(), hpke_rs_crypto::error::Error> {
        match alg {
            hpke_rs_crypto::types::KemAlgorithm::DhKemP256
            | hpke_rs_crypto::types::KemAlgorithm::DhKem25519 => Ok(()),
            hpke_rs_crypto::types::KemAlgorithm::DhKemP384
            | hpke_rs_crypto::types::KemAlgorithm::DhKemP521
            | hpke_rs_crypto::types::KemAlgorithm::DhKem448 => {
                Err(hpke_rs_crypto::error::Error::UnknownKemAlgorithm)
            }
        }
    }

    fn supports_aead(
        alg: hpke_rs_crypto::types::AeadAlgorithm,
    ) -> Result<(), hpke_rs_crypto::error::Error> {
        match alg {
            hpke_rs_crypto::types::AeadAlgorithm::Aes128Gcm
            | hpke_rs_crypto::types::AeadAlgorithm::Aes256Gcm
            | hpke_rs_crypto::types::AeadAlgorithm::ChaCha20Poly1305
            | hpke_rs_crypto::types::AeadAlgorithm::HpkeExport => Ok(()),
        }
    }

    fn prng() -> Self::HpkePrng {
        crate::drbg::Drbg::new(crate::digest::Algorithm::Sha256).unwrap()
    }

    fn kdf_extract(alg: hpke_rs_crypto::types::KdfAlgorithm, salt: &[u8], ikm: &[u8]) -> Vec<u8> {
        let alg = kdf_alg(alg);
        crate::hkdf::extract(alg, salt, ikm)
    }

    fn kdf_expand(
        alg: hpke_rs_crypto::types::KdfAlgorithm,
        prk: &[u8],
        info: &[u8],
        output_size: usize,
    ) -> Result<Vec<u8>, hpke_rs_crypto::error::Error> {
        let alg = kdf_alg(alg);
        crate::hkdf::expand(alg, prk, info, output_size)
            .map_err(|_| hpke_rs_crypto::error::Error::HpkeInvalidOutputLength)
    }

    fn kem_derive(
        alg: hpke_rs_crypto::types::KemAlgorithm,
        mut pk: &[u8],
        sk: &[u8],
    ) -> Result<Vec<u8>, hpke_rs_crypto::error::Error> {
        let alg = kem_alg(alg);

        if alg == crate::kem::Algorithm::Secp256r1 {
            debug_assert_eq!(pk.len(), 65);
            debug_assert_eq!(pk[0], 4);
            pk = &pk[1..];
        }

        let ct = crate::kem::Ct::decode(alg, pk)
            .map_err(|_| hpke_rs_crypto::error::Error::KemInvalidPublicKey)?;
        let key = crate::kem::PrivateKey::decode(alg, sk)
            .map_err(|_| hpke_rs_crypto::error::Error::KemInvalidSecretKey)?;
        ct.decapsulate(&key)
            .map_err(|_| {
                hpke_rs_crypto::error::Error::CryptoLibraryError("decaps error".to_string())
            })
            .map(|ss| {
                let mut ss = ss.encode();
                ss.truncate(32);
                debug_assert_eq!(ss.len(), 32);
                ss
            })
    }

    fn kem_derive_base(
        alg: hpke_rs_crypto::types::KemAlgorithm,
        sk: &[u8],
    ) -> Result<Vec<u8>, hpke_rs_crypto::error::Error> {
        let alg = kem_alg(alg);

        crate::kem::secret_to_public(alg, sk)
            .map_err(|_| hpke_rs_crypto::error::Error::KemInvalidSecretKey)
            .map(|pk| {
                if alg == crate::kem::Algorithm::Secp256r1 {
                    debug_assert_eq!(pk.len(), 64);
                    [4].into_iter().chain(pk.into_iter()).collect()
                } else {
                    pk
                }
            })
    }

    fn kem_key_gen(
        alg: hpke_rs_crypto::types::KemAlgorithm,
        prng: &mut Self::HpkePrng,
    ) -> Result<Vec<u8>, hpke_rs_crypto::error::Error> {
        let alg = kem_alg(alg);
        crate::kem::key_gen(alg, prng)
            .map_err(|_| hpke_rs_crypto::error::Error::InsufficientRandomness)
            .map(|(sk, _pk)| sk.encode())
            .map(|sk| {
                debug_assert_eq!(sk.len(), 32);
                sk
            })
    }

    fn kem_validate_sk(
        alg: hpke_rs_crypto::types::KemAlgorithm,
        sk: &[u8],
    ) -> Result<Vec<u8>, hpke_rs_crypto::error::Error> {
        let alg = kem_alg(alg);

        debug_assert_eq!(sk.len(), 32);

        crate::kem::PrivateKey::decode(alg, sk)
            .map_err(|_| hpke_rs_crypto::error::Error::KemInvalidSecretKey)
            .map(|sk| {
                let sk = sk.encode();
                debug_assert_eq!(sk.len(), 32);
                sk
            })
    }

    fn aead_seal(
        alg: hpke_rs_crypto::types::AeadAlgorithm,
        key: &[u8],
        nonce: &[u8],
        aad: &[u8],
        msg: &[u8],
    ) -> Result<Vec<u8>, hpke_rs_crypto::error::Error> {
        let key = aead_key(alg, key)?;
        let iv = crate::aead::Iv(
            nonce
                .try_into()
                .map_err(|_| hpke_rs_crypto::error::Error::AeadInvalidNonce)?,
        );

        let msg_len = msg.len();
        let mut out: Vec<u8> = msg.iter().cloned().chain(vec![0u8; alg.tag_length()].into_iter()).collect();
        let mut msg_ctxt = &mut out[..msg_len];


        let tag = crate::aead::encrypt(&key, msg_ctxt, iv, aad).map_err(|_| {
            hpke_rs_crypto::error::Error::CryptoLibraryError("aead encrypt error".to_string())
        })?;

        let mut tag_writer = &mut out[msg_len..];
        tag_writer.write_all(tag.as_ref()).unwrap();

        Ok(out)
    }

    fn aead_open(
        alg: hpke_rs_crypto::types::AeadAlgorithm,
        key: &[u8],
        nonce: &[u8],
        aad: &[u8],
        msg: &[u8],
    ) -> Result<Vec<u8>, hpke_rs_crypto::error::Error> {
        let key = aead_key(alg, key)?;
        let iv = crate::aead::Iv(
            nonce
                .try_into()
                .map_err(|_| hpke_rs_crypto::error::Error::AeadInvalidNonce)?,
        );

        if msg.len() < alg.tag_length() {
            return Err(hpke_rs_crypto::error::Error::AeadInvalidCiphertext)
        }

        let msg_len = msg.len() - alg.tag_length();
        let tag = crate::aead::Tag::from_slice(&msg[msg_len..]).unwrap();
        let msg = &msg[..msg_len];


        let mut msg_ctxt = msg.to_vec();
        crate::aead::decrypt(&key, &mut msg_ctxt, iv, aad, &tag)
            .map_err(|x| {panic!("wat {x}");})
            .map_err(|_| hpke_rs_crypto::error::Error::AeadOpenError)
            .map(|_| msg_ctxt)
    }
}

impl hpke_rs_crypto::HpkeTestRng for crate::drbg::Drbg {
    fn try_fill_test_bytes(&mut self, dest: &mut [u8]) -> Result<(), rand::Error> {
        self.generate(dest).map_err(rand::Error::new)
    }

    fn seed(&mut self, seed: &[u8]) {
        self.reseed(seed, b"").expect("reseed failed")
    }
}

#[cfg(test)]
mod tests {
    #![allow(non_snake_case)]

    use super::Provider;

    hpke_rs_tests::kat_fun!(Provider);
    hpke_rs_tests::test_funs!(Provider);
}
