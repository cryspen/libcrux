// This module is declared here since otherwise, hax reports the following error:
//
// The THIR body of item
// DefId(0:986 ~ libcrux[92b3]::kem::kyber768::parameters::COEFFICIENTS_IN_RING_ELEMENT)
// was stolen.
//
// This is being tracked in https://github.com/hacspec/hacspec-v2/issues/27
mod parameters;

mod arithmetic;
mod compress;
mod constant_time_ops;
mod conversions;
mod ind_cpa;
mod ntt;
mod sampling;
mod serialize;

use constant_time_ops::{
    compare_ciphertexts_in_constant_time, select_shared_secret_in_constant_time,
};
use conversions::into_padded_array;
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

    let (ind_cpa_key_pair, sampling_a_error) =
        ind_cpa::generate_keypair(ind_cpa_keypair_randomness);

    let secret_key_serialized = ind_cpa_key_pair.serialize_secret_key(implicit_rejection_value);

    if sampling_a_error.is_some() {
        Err(sampling_a_error.unwrap())
    } else {
        Ok((ind_cpa_key_pair.pk(), secret_key_serialized))
    }
}

pub fn encapsulate(
    public_key: &Kyber768PublicKey,
    randomness: [u8; SHARED_SECRET_SIZE],
) -> Result<(Kyber768Ciphertext, Kyber768SharedSecret), BadRejectionSamplingRandomnessError> {
    let randomness_hashed = H(&randomness);

    let mut to_hash: [u8; 2 * H_DIGEST_SIZE] = into_padded_array(&randomness_hashed);
    to_hash[H_DIGEST_SIZE..].copy_from_slice(&H(public_key));

    let hashed = G(&to_hash);
    let (k_not, pseudorandomness) = hashed.split_at(32);

    let (ciphertext, sampling_a_error) =
        ind_cpa::encrypt(public_key, randomness_hashed, pseudorandomness);

    let mut to_hash: [u8; 2 * H_DIGEST_SIZE] = into_padded_array(&k_not);
    to_hash[H_DIGEST_SIZE..].copy_from_slice(&H(&ciphertext));

    let shared_secret: Kyber768SharedSecret = KDF(&to_hash);

    if sampling_a_error.is_some() {
        Err(sampling_a_error.unwrap())
    } else {
        Ok((ciphertext, shared_secret))
    }
}

pub fn decapsulate(
    secret_key: &Kyber768PrivateKey,
    ciphertext: &Kyber768Ciphertext,
) -> Kyber768SharedSecret {
    let (ind_cpa_secret_key, secret_key) = secret_key.split_at(CPA_PKE_SECRET_KEY_SIZE);
    let (ind_cpa_public_key, secret_key) = secret_key.split_at(CPA_PKE_PUBLIC_KEY_SIZE);
    let (ind_cpa_public_key_hash, implicit_rejection_value) = secret_key.split_at(H_DIGEST_SIZE);

    let decrypted = ind_cpa::decrypt(ind_cpa_secret_key, &ciphertext);

    let mut to_hash: [u8; CPA_PKE_MESSAGE_SIZE + H_DIGEST_SIZE] = into_padded_array(&decrypted);
    to_hash[CPA_PKE_MESSAGE_SIZE..].copy_from_slice(ind_cpa_public_key_hash);

    let hashed = G(&to_hash);
    let (k_not, pseudorandomness) = hashed.split_at(32);

    // If a ciphertext C is well-formed, setting aside the fact that a
    // decryption failure could (with negligible probability) occur, it must hold that:
    //
    // Encrypt(pk, Decrypt(sk, C)) = C
    //
    // Therefore, if |ind_cpa::encrypt| returns an error,
    // |expected_ciphertext| cannot equal |ciphertext|, thereby resulting in
    // implicit rejection.
    //
    // If C is ill-formed, due to the use of hashing to obtain |pseudorandomness|
    // as well as the fact that the Kyber CPA-PKE is sparse pseudo-random, it is
    // highly likely that |expected_ciphertext| will not equal |ciphertext|, thereby
    // also resulting in implicit rejection.
    //
    // Thus, we ignore the second return value of |ind_cpa::encrypt|.
    let (expected_ciphertext, _) =
        ind_cpa::encrypt(ind_cpa_public_key, decrypted, pseudorandomness);

    let selector = compare_ciphertexts_in_constant_time(ciphertext, &expected_ciphertext);
    let to_hash = select_shared_secret_in_constant_time(k_not, implicit_rejection_value, selector);

    let mut to_hash: [u8; SHARED_SECRET_SIZE + H_DIGEST_SIZE] = into_padded_array(&to_hash);
    to_hash[SHARED_SECRET_SIZE..].copy_from_slice(&H(ciphertext));

    KDF(&to_hash)
}
