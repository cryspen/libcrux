use alloc::{vec, vec::Vec};

use hpke_rs_crypto::{error::Error, types::KemAlgorithm, HpkeCrypto, RngCore};

use crate::{dh_kem, util, Hpke};

pub(crate) type PrivateKey = Vec<u8>;
pub(crate) type PublicKey = Vec<u8>;

#[inline(always)]
fn ciphersuite(alg: KemAlgorithm) -> Vec<u8> {
    util::concat(&[b"KEM", &(alg as u16).to_be_bytes()])
}

pub(crate) fn encaps<Crypto: HpkeCrypto>(
    hpke: &mut Hpke<Crypto>,
    pk_r: &[u8],
) -> Result<(Vec<u8>, Vec<u8>), Error> {
    let alg = hpke.kem_id;
    match alg {
        KemAlgorithm::DhKemP256
        | KemAlgorithm::DhKemK256
        | KemAlgorithm::DhKemP384
        | KemAlgorithm::DhKemP521
        | KemAlgorithm::DhKem25519
        | KemAlgorithm::DhKem448 => {
            let randomness = hpke
                .random(alg.private_key_len())
                .map_err(|_| Error::InsufficientRandomness)?;
            dh_kem::encaps::<Crypto>(alg, pk_r, &ciphersuite(alg), &randomness)
        }
        KemAlgorithm::XWingDraft06 => Crypto::kem_encaps(alg, pk_r, hpke.rng()),
    }
}

pub(crate) fn decaps<Crypto: HpkeCrypto>(
    alg: KemAlgorithm,
    enc: &[u8],
    sk_r: &[u8],
) -> Result<Vec<u8>, Error> {
    match alg {
        KemAlgorithm::DhKemP256
        | KemAlgorithm::DhKemK256
        | KemAlgorithm::DhKemP384
        | KemAlgorithm::DhKemP521
        | KemAlgorithm::DhKem25519
        | KemAlgorithm::DhKem448 => dh_kem::decaps::<Crypto>(alg, enc, sk_r, &ciphersuite(alg)),
        KemAlgorithm::XWingDraft06 => Crypto::kem_decaps(alg, enc, sk_r),
    }
}

pub(crate) fn auth_encaps<Crypto: HpkeCrypto>(
    hpke: &mut Hpke<Crypto>,
    pk_r: &[u8],
    sk_s: &[u8],
) -> Result<(Vec<u8>, Vec<u8>), Error> {
    let alg = hpke.kem_id;
    match alg {
        KemAlgorithm::DhKemP256
        | KemAlgorithm::DhKemK256
        | KemAlgorithm::DhKemP384
        | KemAlgorithm::DhKemP521
        | KemAlgorithm::DhKem25519
        | KemAlgorithm::DhKem448 => {
            let randomness = hpke
                .random(alg.private_key_len())
                .map_err(|_| Error::InsufficientRandomness)?;
            dh_kem::auth_encaps::<Crypto>(alg, pk_r, sk_s, &ciphersuite(alg), &randomness)
        }
        KemAlgorithm::XWingDraft06 => Err(Error::UnsupportedKemOperation),
    }
}

pub(crate) fn auth_decaps<Crypto: HpkeCrypto>(
    alg: KemAlgorithm,
    enc: &[u8],
    sk_r: &[u8],
    pk_s: &[u8],
) -> Result<Vec<u8>, Error> {
    match alg {
        KemAlgorithm::DhKemP256
        | KemAlgorithm::DhKemK256
        | KemAlgorithm::DhKemP384
        | KemAlgorithm::DhKemP521
        | KemAlgorithm::DhKem25519
        | KemAlgorithm::DhKem448 => {
            dh_kem::auth_decaps::<Crypto>(alg, enc, sk_r, pk_s, &ciphersuite(alg))
        }
        KemAlgorithm::XWingDraft06 => Err(Error::UnsupportedKemOperation),
    }
}

/// Returns (private, public)
pub(crate) fn key_gen<Crypto: HpkeCrypto>(
    alg: KemAlgorithm,
    prng: &mut Crypto::HpkePrng,
) -> Result<(Vec<u8>, Vec<u8>), Error> {
    match alg {
        // For ECDH based keys, we generate a completely fresh key.
        KemAlgorithm::DhKemP256
        | KemAlgorithm::DhKemK256
        | KemAlgorithm::DhKemP384
        | KemAlgorithm::DhKemP521
        | KemAlgorithm::DhKem25519
        | KemAlgorithm::DhKem448 => dh_kem::key_gen::<Crypto>(alg, prng),
        KemAlgorithm::XWingDraft06 => {
            // For XWing we use the derive key pair function.
            let mut seed = vec![0u8; alg.private_key_len()];
            prng.fill_bytes(&mut seed);
            let (pk, sk) = derive_key_pair::<Crypto>(alg, &seed)?;
            Ok((sk, pk))
        }
    }
}

/// Derive key pair from the input key material `ikm`.
///
/// Returns (PublicKey, PrivateKey).
pub(crate) fn derive_key_pair<Crypto: HpkeCrypto>(
    alg: KemAlgorithm,
    ikm: &[u8],
) -> Result<(PublicKey, PrivateKey), Error> {
    match alg {
        KemAlgorithm::DhKemP256
        | KemAlgorithm::DhKemK256
        | KemAlgorithm::DhKemP384
        | KemAlgorithm::DhKemP521
        | KemAlgorithm::DhKem25519
        | KemAlgorithm::DhKem448 => dh_kem::derive_key_pair::<Crypto>(alg, &ciphersuite(alg), ikm),
        KemAlgorithm::XWingDraft06 => {
            let seed = libcrux_sha3::shake256::<32>(ikm);
            let kp = Crypto::kem_key_gen_derand(alg, &seed)?;
            Ok(kp)
        }
    }
}
