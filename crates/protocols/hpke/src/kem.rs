use hpke_rs_crypto::{error::Error, types::KemAlgorithm, HpkeCrypto};

use crate::dh_kem;
use crate::util;

pub(crate) type PrivateKey = Vec<u8>;
pub(crate) type PublicKey = Vec<u8>;

#[inline(always)]
fn ciphersuite(alg: KemAlgorithm) -> Vec<u8> {
    util::concat(&[b"KEM", &(alg as u16).to_be_bytes()])
}

pub(crate) fn encaps<Crypto: HpkeCrypto>(
    alg: KemAlgorithm,
    pk_r: &[u8],
    randomness: &[u8],
) -> Result<(Vec<u8>, Vec<u8>), Error> {
    match alg {
        KemAlgorithm::DhKemP256
        | KemAlgorithm::DhKemP384
        | KemAlgorithm::DhKemP521
        | KemAlgorithm::DhKem25519
        | KemAlgorithm::DhKem448 => {
            dh_kem::encaps::<Crypto>(alg, pk_r, &ciphersuite(alg), randomness)
        }
    }
}

pub(crate) fn decaps<Crypto: HpkeCrypto>(
    alg: KemAlgorithm,
    enc: &[u8],
    sk_r: &[u8],
) -> Result<Vec<u8>, Error> {
    match alg {
        KemAlgorithm::DhKemP256
        | KemAlgorithm::DhKemP384
        | KemAlgorithm::DhKemP521
        | KemAlgorithm::DhKem25519
        | KemAlgorithm::DhKem448 => dh_kem::decaps::<Crypto>(alg, enc, sk_r, &ciphersuite(alg)),
    }
}

pub(crate) fn auth_encaps<Crypto: HpkeCrypto>(
    alg: KemAlgorithm,
    pk_r: &[u8],
    sk_s: &[u8],
    randomness: &[u8],
) -> Result<(Vec<u8>, Vec<u8>), Error> {
    match alg {
        KemAlgorithm::DhKemP256
        | KemAlgorithm::DhKemP384
        | KemAlgorithm::DhKemP521
        | KemAlgorithm::DhKem25519
        | KemAlgorithm::DhKem448 => {
            dh_kem::auth_encaps::<Crypto>(alg, pk_r, sk_s, &ciphersuite(alg), randomness)
        }
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
        | KemAlgorithm::DhKemP384
        | KemAlgorithm::DhKemP521
        | KemAlgorithm::DhKem25519
        | KemAlgorithm::DhKem448 => {
            dh_kem::auth_decaps::<Crypto>(alg, enc, sk_r, pk_s, &ciphersuite(alg))
        }
    }
}

pub(crate) fn key_gen<Crypto: HpkeCrypto>(
    alg: KemAlgorithm,
    prng: &mut Crypto::HpkePrng,
) -> Result<(Vec<u8>, Vec<u8>), Error> {
    match alg {
        KemAlgorithm::DhKemP256
        | KemAlgorithm::DhKemP384
        | KemAlgorithm::DhKemP521
        | KemAlgorithm::DhKem25519
        | KemAlgorithm::DhKem448 => dh_kem::key_gen::<Crypto>(alg, prng),
    }
}

/// Derive key pair from the input key material `ikm`.
///
/// Returns (PublicKey, PrivateKey).
pub(crate) fn derive_key_pair<Crypto: HpkeCrypto>(
    alg: KemAlgorithm,
    ikm: &[u8],
) -> Result<(PublicKey, PrivateKey), Error> {
    dh_kem::derive_key_pair::<Crypto>(alg, &ciphersuite(alg), ikm)
}
