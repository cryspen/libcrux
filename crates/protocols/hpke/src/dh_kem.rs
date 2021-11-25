//! DH KEM as described in §4.1. DH-Based KEM.

use hpke_rs_crypto::{error::Error, types::KemAlgorithm, HpkeCrypto};

use crate::util::*;
use crate::{
    kdf::{labeled_expand, labeled_extract},
    kem::*,
};

fn extract_and_expand<Crypto: HpkeCrypto>(
    alg: KemAlgorithm,
    pk: PublicKey,
    kem_context: &[u8],
    suite_id: &[u8],
) -> Result<Vec<u8>, Error> {
    let prk = labeled_extract::<Crypto>(alg.into(), &[], suite_id, "eae_prk", &pk);
    labeled_expand::<Crypto>(
        alg.into(),
        &prk,
        suite_id,
        "shared_secret",
        kem_context,
        alg.shared_secret_len(),
    )
}

/// Serialize public key.
/// This is an identity function for X25519.
/// Because P256 public keys are already encoded before it is the identity
/// function here as well.
#[inline(always)]
pub(super) fn serialize(pk: &[u8]) -> Vec<u8> {
    pk.to_vec()
}

#[inline(always)]
pub(super) fn deserialize(enc: &[u8]) -> Vec<u8> {
    enc.to_vec()
}

pub(super) fn key_gen<Crypto: HpkeCrypto>(
    alg: KemAlgorithm,
    prng: &mut Crypto::HpkePrng,
) -> Result<(Vec<u8>, Vec<u8>), Error> {
    let sk = Crypto::kem_key_gen(alg, prng)?;
    let pk = Crypto::kem_derive_base(alg, &sk)?;
    Ok((sk, pk))
}

pub(super) fn derive_key_pair<Crypto: HpkeCrypto>(
    alg: KemAlgorithm,
    suite_id: &[u8],
    ikm: &[u8],
) -> Result<(PublicKey, PrivateKey), Error> {
    let dkp_prk = labeled_extract::<Crypto>(alg.into(), &[], suite_id, "dkp_prk", ikm);

    let sk = match alg {
        KemAlgorithm::DhKem25519 => labeled_expand::<Crypto>(
            alg.into(),
            &dkp_prk,
            suite_id,
            "sk",
            &[],
            alg.private_key_len(),
        )?,
        KemAlgorithm::DhKemP256 => {
            let mut ctr = 0u8;
            // Do rejection sampling trying to find a valid key.
            // It is expected that there aren't too many iteration and that
            // the loop will always terminate.
            loop {
                let candidate = labeled_expand::<Crypto>(
                    alg.into(),
                    &dkp_prk,
                    suite_id,
                    "candidate",
                    &ctr.to_be_bytes(),
                    alg.private_key_len(),
                );
                if let Ok(sk) = &candidate {
                    if let Ok(sk) = Crypto::kem_validate_sk(alg, sk) {
                        break sk;
                    }
                }
                if ctr == u8::MAX {
                    // If we get here we lost. This should never happen.
                    return Err(Error::CryptoLibraryError(
                        "Unable to generate a valid P256 private key".to_string(),
                    ));
                }
                ctr += 1;
            }
        }
        _ => {
            panic!("This should be unreachable. Only x25519 and P256 KEMs are implemented")
        }
    };
    Ok((Crypto::kem_derive_base(alg, &sk)?, sk))
}

pub(super) fn encaps<Crypto: HpkeCrypto>(
    alg: KemAlgorithm,
    pk_r: &[u8],
    suite_id: &[u8],
    randomness: &[u8],
) -> Result<(Vec<u8>, Vec<u8>), Error> {
    debug_assert_eq!(randomness.len(), alg.private_key_len());
    let (pk_e, sk_e) = derive_key_pair::<Crypto>(alg, suite_id, randomness)?;
    let dh_pk = Crypto::kem_derive(alg, pk_r, &sk_e)?;
    let enc = serialize(&pk_e);

    let pk_rm = serialize(pk_r);
    let kem_context = concat(&[&enc, &pk_rm]);

    let zz = extract_and_expand::<Crypto>(alg, dh_pk, &kem_context, suite_id)?;
    Ok((zz, enc))
}

pub(super) fn decaps<Crypto: HpkeCrypto>(
    alg: KemAlgorithm,
    enc: &[u8],
    sk_r: &[u8],
    suite_id: &[u8],
) -> Result<Vec<u8>, Error> {
    let pk_e = deserialize(enc);
    let dh_pk = Crypto::kem_derive(alg, &pk_e, sk_r)?;

    let pk_rm = serialize(&Crypto::kem_derive_base(alg, sk_r)?);
    let kem_context = concat(&[enc, &pk_rm]);

    extract_and_expand::<Crypto>(alg, dh_pk, &kem_context, suite_id)
}

pub(super) fn auth_encaps<Crypto: HpkeCrypto>(
    alg: KemAlgorithm,
    pk_r: &[u8],
    sk_s: &[u8],
    suite_id: &[u8],
    randomness: &[u8],
) -> Result<(Vec<u8>, Vec<u8>), Error> {
    debug_assert_eq!(randomness.len(), alg.private_key_len());
    let (pk_e, sk_e) = derive_key_pair::<Crypto>(alg, suite_id, randomness)?;
    let dh_pk = concat(&[
        &Crypto::kem_derive(alg, pk_r, &sk_e)?,
        &Crypto::kem_derive(alg, pk_r, sk_s)?,
    ]);

    let enc = serialize(&pk_e);
    let pk_rm = serialize(pk_r);
    let pk_sm = serialize(&Crypto::kem_derive_base(alg, sk_s)?);

    let kem_context = concat(&[&enc, &pk_rm, &pk_sm]);

    let zz = extract_and_expand::<Crypto>(alg, dh_pk, &kem_context, suite_id)?;
    Ok((zz, enc))
}

pub(super) fn auth_decaps<Crypto: HpkeCrypto>(
    alg: KemAlgorithm,
    enc: &[u8],
    sk_r: &[u8],
    pk_s: &[u8],
    suite_id: &[u8],
) -> Result<Vec<u8>, Error> {
    let pk_e = deserialize(enc);
    let dh_pk = concat(&[
        &Crypto::kem_derive(alg, &pk_e, sk_r)?,
        &Crypto::kem_derive(alg, pk_s, sk_r)?,
    ]);

    let pk_rm = serialize(&Crypto::kem_derive_base(alg, sk_r)?);
    let pk_sm = serialize(pk_s);
    let kem_context = concat(&[enc, &pk_rm, &pk_sm]);

    extract_and_expand::<Crypto>(alg, dh_pk, &kem_context, suite_id)
}
