// This module is declared here since otherwise, hax reports the following error:
//
// The THIR body of item
// DefId(0:986 ~ libcrux[92b3]::kem::kyber768::parameters::COEFFICIENTS_IN_RING_ELEMENT)
// was stolen.
//
// This is being tracked in https://github.com/hacspec/hacspec-v2/issues/27
pub(crate) mod constants;

#[macro_use]
mod types;
mod arithmetic;
mod compress;
mod constant_time_ops;
mod conversions;
mod hash_functions;
mod ind_cpa;
mod ntt;
mod sampling;
mod serialize;

// Variants
pub mod kyber1024;
pub mod kyber512;
pub mod kyber768;

impl_generic_struct!(KyberCiphertext);
impl_generic_struct!(KyberPrivateKey);
impl_generic_struct!(KyberPublicKey);

// TODO: We should make this an actual type as opposed to alias so we can enforce
// some checks at the type level. This is being tracked in:
// https://github.com/cryspen/libcrux/issues/123
pub type KyberSharedSecret = [u8; constants::SHARED_SECRET_SIZE];

/// A Kyber key pair
pub struct KyberKeyPair<const PRIVATE_KEY_SIZE: usize, const PUBLIC_KEY_SIZE: usize> {
    pub(crate) sk: KyberPrivateKey<PRIVATE_KEY_SIZE>,
    pub(crate) pk: KyberPublicKey<PUBLIC_KEY_SIZE>,
}

#[derive(Debug)]
pub struct BadRejectionSamplingRandomnessError;

use self::{
    constant_time_ops::{
        compare_ciphertexts_in_constant_time, select_shared_secret_in_constant_time,
    },
    constants::{CPA_PKE_KEY_GENERATION_SEED_SIZE, H_DIGEST_SIZE, SHARED_SECRET_SIZE},
    conversions::into_padded_array,
    hash_functions::{G, H, PRF},
    ind_cpa::serialize_secret_key,
};

/// Seed size for key generation
pub(in crate::kem) const KEY_GENERATION_SEED_SIZE: usize =
    CPA_PKE_KEY_GENERATION_SEED_SIZE + SHARED_SECRET_SIZE;

pub(super) fn generate_keypair<
    const K: usize,
    const CPA_PRIVATE_KEY_SIZE: usize,
    const PRIVATE_KEY_SIZE: usize,
    const PUBLIC_KEY_SIZE: usize,
    const BYTES_PER_RING_ELEMENT: usize,
    const ETA1: usize,
    const ETA1_RANDOMNESS_SIZE: usize,
>(
    randomness: [u8; KEY_GENERATION_SEED_SIZE],
) -> Result<KyberKeyPair<PRIVATE_KEY_SIZE, PUBLIC_KEY_SIZE>, BadRejectionSamplingRandomnessError> {
    let (ind_cpa_keypair_randomness, implicit_rejection_value) =
        randomness.split_at(CPA_PKE_KEY_GENERATION_SEED_SIZE);

    let ((ind_cpa_private_key, public_key), sampling_a_error) = ind_cpa::generate_keypair::<
        K,
        CPA_PRIVATE_KEY_SIZE,
        PUBLIC_KEY_SIZE,
        BYTES_PER_RING_ELEMENT,
        ETA1,
        ETA1_RANDOMNESS_SIZE,
    >(ind_cpa_keypair_randomness);

    let secret_key_serialized = serialize_secret_key(
        ind_cpa_private_key.as_slice(),
        public_key.as_slice(),
        implicit_rejection_value,
    );
    if let Some(error) = sampling_a_error {
        Err(error)
    } else {
        let private_key: KyberPrivateKey<PRIVATE_KEY_SIZE> =
            KyberPrivateKey::from(secret_key_serialized);

        Ok(KyberKeyPair::from(private_key, public_key))
    }
}

pub(super) fn encapsulate<
    const K: usize,
    const CIPHERTEXT_SIZE: usize,
    const PUBLIC_KEY_SIZE: usize,
    const T_AS_NTT_ENCODED_SIZE: usize,
    const C1_SIZE: usize,
    const C2_SIZE: usize,
    const VECTOR_U_COMPRESSION_FACTOR: usize,
    const VECTOR_V_COMPRESSION_FACTOR: usize,
    const VECTOR_U_BLOCK_LEN: usize,
    const ETA1: usize,
    const ETA1_RANDOMNESS_SIZE: usize,
    const ETA2: usize,
    const ETA2_RANDOMNESS_SIZE: usize,
>(
    public_key: &KyberPublicKey<PUBLIC_KEY_SIZE>,
    randomness: [u8; SHARED_SECRET_SIZE],
) -> Result<
    (KyberCiphertext<CIPHERTEXT_SIZE>, KyberSharedSecret),
    BadRejectionSamplingRandomnessError,
> {
    let mut to_hash: [u8; 2 * H_DIGEST_SIZE] = into_padded_array(&randomness);
    to_hash[H_DIGEST_SIZE..].copy_from_slice(&H(public_key.as_slice()));

    let hashed = G(&to_hash);
    let (shared_secret, pseudorandomness) = hashed.split_at(SHARED_SECRET_SIZE);

    let (ciphertext, sampling_a_error) = ind_cpa::encrypt::<
        K,
        CIPHERTEXT_SIZE,
        T_AS_NTT_ENCODED_SIZE,
        C1_SIZE,
        C2_SIZE,
        VECTOR_U_COMPRESSION_FACTOR,
        VECTOR_V_COMPRESSION_FACTOR,
        VECTOR_U_BLOCK_LEN,
        ETA1,
        ETA1_RANDOMNESS_SIZE,
        ETA2,
        ETA2_RANDOMNESS_SIZE,
    >(public_key.as_slice(), randomness, pseudorandomness);

    match sampling_a_error {
        Some(e) => Err(e),
        None => Ok((ciphertext, shared_secret.try_into().unwrap())),
    }
}

pub(super) fn decapsulate<
    const K: usize,
    const SECRET_KEY_SIZE: usize,
    const CPA_SECRET_KEY_SIZE: usize,
    const PUBLIC_KEY_SIZE: usize,
    const CIPHERTEXT_SIZE: usize,
    const T_AS_NTT_ENCODED_SIZE: usize,
    const C1_SIZE: usize,
    const C2_SIZE: usize,
    const VECTOR_U_COMPRESSION_FACTOR: usize,
    const VECTOR_V_COMPRESSION_FACTOR: usize,
    const C1_BLOCK_SIZE: usize,
    const ETA1: usize,
    const ETA1_RANDOMNESS_SIZE: usize,
    const ETA2: usize,
    const ETA2_RANDOMNESS_SIZE: usize,
    const IMPLICIT_REJECTION_HASH_INPUT_SIZE: usize,
>(
    secret_key: &KyberPrivateKey<SECRET_KEY_SIZE>,
    ciphertext: &KyberCiphertext<CIPHERTEXT_SIZE>,
) -> KyberSharedSecret {
    let (ind_cpa_secret_key, secret_key) = secret_key.split_at(CPA_SECRET_KEY_SIZE);
    let (ind_cpa_public_key, secret_key) = secret_key.split_at(PUBLIC_KEY_SIZE);
    let (ind_cpa_public_key_hash, implicit_rejection_value) = secret_key.split_at(H_DIGEST_SIZE);

    let decrypted = ind_cpa::decrypt::<
        K,
        CIPHERTEXT_SIZE,
        C1_SIZE,
        VECTOR_U_COMPRESSION_FACTOR,
        VECTOR_V_COMPRESSION_FACTOR,
    >(ind_cpa_secret_key, ciphertext);

    let mut to_hash: [u8; SHARED_SECRET_SIZE + H_DIGEST_SIZE] = into_padded_array(&decrypted);
    to_hash[SHARED_SECRET_SIZE..].copy_from_slice(ind_cpa_public_key_hash);

    let hashed = G(&to_hash);
    let (shared_secret, pseudorandomness) = hashed.split_at(SHARED_SECRET_SIZE);

    let mut to_hash: [u8; IMPLICIT_REJECTION_HASH_INPUT_SIZE] =
        into_padded_array(&implicit_rejection_value);
    to_hash[SHARED_SECRET_SIZE..].copy_from_slice(ciphertext.as_ref());
    let implicit_rejection_shared_secret: [u8; SHARED_SECRET_SIZE] = PRF(&to_hash);

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
    let (expected_ciphertext, _) = ind_cpa::encrypt::<
        K,
        CIPHERTEXT_SIZE,
        T_AS_NTT_ENCODED_SIZE,
        C1_SIZE,
        C2_SIZE,
        VECTOR_U_COMPRESSION_FACTOR,
        VECTOR_V_COMPRESSION_FACTOR,
        C1_BLOCK_SIZE,
        ETA1,
        ETA1_RANDOMNESS_SIZE,
        ETA2,
        ETA2_RANDOMNESS_SIZE,
    >(ind_cpa_public_key, decrypted, pseudorandomness);

    let selector = compare_ciphertexts_in_constant_time::<CIPHERTEXT_SIZE>(
        ciphertext.as_ref(),
        expected_ciphertext.as_ref(),
    );

    select_shared_secret_in_constant_time(
        shared_secret,
        &implicit_rejection_shared_secret,
        selector,
    )
}
