mod compress;
mod ind_cpa;
mod ntt;
mod parameters;
mod sampling;
mod serialize;
mod utils;
mod field_element;

use utils::{ArrayConversion, UpdatingArray2};

use parameters::{
    hash_functions::{G, H, H_DIGEST_SIZE, KDF},
    CPA_PKE_KEY_GENERATION_SEED_SIZE, CPA_PKE_MESSAGE_SIZE, CPA_PKE_PUBLIC_KEY_SIZE,
    CPA_PKE_SECRET_KEY_SIZE,
};

pub const SHARED_SECRET_SIZE: usize = CPA_PKE_MESSAGE_SIZE;

pub const KEY_GENERATION_SEED_SIZE: usize = CPA_PKE_KEY_GENERATION_SEED_SIZE + SHARED_SECRET_SIZE;

pub const PUBLIC_KEY_SIZE: usize = CPA_PKE_PUBLIC_KEY_SIZE;

pub const SECRET_KEY_SIZE: usize =
    CPA_PKE_SECRET_KEY_SIZE + CPA_PKE_PUBLIC_KEY_SIZE + H_DIGEST_SIZE + SHARED_SECRET_SIZE;

pub const CIPHERTEXT_SIZE: usize = parameters::CPA_PKE_CIPHERTEXT_SIZE;

pub type Kyber768PublicKey = [u8; PUBLIC_KEY_SIZE];
pub type Kyber768PrivateKey = [u8; SECRET_KEY_SIZE];

pub type Kyber768Ciphertext = [u8; CIPHERTEXT_SIZE];
pub type Kyber768SharedSecret = [u8; SHARED_SECRET_SIZE];

#[derive(Debug)]
pub struct BadRejectionSamplingRandomnessError;

pub fn generate_keypair(
    randomness: [u8; KEY_GENERATION_SEED_SIZE],
) -> Result<(Kyber768PublicKey, Kyber768PrivateKey), BadRejectionSamplingRandomnessError> {
    let ind_cpa_keypair_randomness = &randomness[0..parameters::CPA_PKE_KEY_GENERATION_SEED_SIZE];
    let implicit_rejection_value = &randomness[parameters::CPA_PKE_KEY_GENERATION_SEED_SIZE..];

    let ind_cpa_key_pair = ind_cpa::generate_keypair(&ind_cpa_keypair_randomness.as_array())?;

    let secret_key_serialized =
        ind_cpa_key_pair.serialize_secret_key(&implicit_rejection_value.as_array());

    Ok((ind_cpa_key_pair.pk(), secret_key_serialized))
}

pub fn encapsulate(
    public_key: Kyber768PublicKey,
    randomness: [u8; SHARED_SECRET_SIZE],
) -> Result<(Kyber768Ciphertext, Kyber768SharedSecret), BadRejectionSamplingRandomnessError> {
    let randomness_hashed = H(&randomness);

    let to_hash: [u8; 2 * H_DIGEST_SIZE] = randomness_hashed.push(&H(&public_key));

    let hashed = G(&to_hash);
    let (k_not, pseudorandomness) = hashed.split_at(32);

    let ciphertext =
        ind_cpa::encrypt(&public_key, randomness_hashed, &pseudorandomness.as_array())?;

    let to_hash: [u8; 2 * H_DIGEST_SIZE] = k_not.push(&H(&ciphertext));
    let shared_secret: Kyber768SharedSecret = KDF(&to_hash);

    Ok((ciphertext, shared_secret))
}

pub fn decapsulate(
    secret_key: Kyber768PrivateKey,
    ciphertext: Kyber768Ciphertext,
) -> Kyber768SharedSecret {
    let (ind_cpa_secret_key, secret_key) = secret_key.split_at(CPA_PKE_SECRET_KEY_SIZE);
    let (ind_cpa_public_key, secret_key) = secret_key.split_at(CPA_PKE_PUBLIC_KEY_SIZE);
    let (ind_cpa_public_key_hash, implicit_rejection_value) = secret_key.split_at(H_DIGEST_SIZE);

    let decrypted = ind_cpa::decrypt(&ind_cpa_secret_key.as_array(), &ciphertext);

    let to_hash: [u8; CPA_PKE_MESSAGE_SIZE + H_DIGEST_SIZE] =
        decrypted.push(ind_cpa_public_key_hash);

    let hashed = G(&to_hash);
    let (k_not, pseudorandomness) = hashed.split_at(32);

    let reencrypted_ciphertext = ind_cpa::encrypt(
        &ind_cpa_public_key.as_array(),
        decrypted,
        &pseudorandomness.as_array(),
    );

    let to_hash = if let Ok(reencrypted) = reencrypted_ciphertext {
        if ciphertext == reencrypted {
            k_not
        } else {
            implicit_rejection_value
        }
    } else {
        implicit_rejection_value
    };
    assert!(to_hash.len() == 32);
    let to_hash: [u8; 32 + H_DIGEST_SIZE] = to_hash.push(&H(&ciphertext));

    KDF(&to_hash)
}
