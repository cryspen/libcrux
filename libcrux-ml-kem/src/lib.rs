pub(crate) mod hax_utils;
// This module is declared here since otherwise, hax reports the following error:
//
// The THIR body of item
// DefId(0:986 ~ libcrux[92b3]::crate768::parameters::COEFFICIENTS_IN_RING_ELEMENT)
// was stolen.
//
// This is being tracked in https://github.com/hacspec/hacspec-v2/issues/27
pub(crate) mod constants;

/// Helpers for verification and extraction
mod helper;

mod arithmetic;
mod compress;
mod constant_time_ops;
mod hash_functions;
mod ind_cpa;
mod matrix;
mod ntt;
mod sampling;
mod serialize;
mod types;

// Public API
pub mod kyber1024;
pub mod kyber512;
pub mod kyber768;
pub use types::{MlKemCiphertext, MlKemKeyPair, MlKemPrivateKey, MlKemPublicKey};

// use rand::{CryptoRng, Rng};

// /// ML-KEM Variants
// #[derive(Clone, Copy, PartialEq, Debug)]
// pub enum Algorithm {
//     MlKem512,
//     MlKem768,
//     MlKem1024,
// }

// /// ML-KEM Errors
// #[derive(Debug, PartialEq, Eq)]
// pub enum Error {
//     KeyGen,
//     Encapsulate,
//     Decapsulate,
//     InvalidPrivateKey,
//     InvalidPublicKey,
//     InvalidCiphertext,
// }

// fn random_array<const L: usize>(rng: &mut (impl CryptoRng + Rng)) -> Result<[u8; L], Error> {
//     let mut seed = [0; L];
//     rng.try_fill_bytes(&mut seed).map_err(|_| Error::KeyGen)?;
//     Ok(seed)
// }

// /// Generate a key pair for the [`Algorithm`] using the provided rng.
// ///
// /// The function returns a fresh key or a [`Error::KeyGen`] error if
// /// * not enough entropy was available
// /// * it was not possible to generate a valid key within a reasonable amount of iterations.
// pub fn key_gen<const PrivateKeySize: usize, const PublicKeySize: usize>(
//     alg: Algorithm,
//     rng: &mut (impl CryptoRng + Rng),
// ) -> Result<
//     (
//         MlKemPrivateKey<PrivateKeySize>,
//         MlKemPublicKey<PublicKeySize>,
//     ),
//     Error,
// > {
//     match alg {
//         Algorithm::MlKem512 => {
//             generate_keypair::<
//                 RANK_512,
//                 CPA_PKE_SECRET_KEY_SIZE_512,
//                 PrivateKeySize,
//                 PublicKeySize,
//                 RANKED_BYTES_PER_RING_ELEMENT_512,
//                 ETA1,
//                 ETA1_RANDOMNESS_SIZE,
//             >(randomness)
//             // kyber512::generate_key_pair(random_array(rng)?)
//         }
//         Algorithm::MlKem768 => kyber768::generate_key_pair(random_array(rng)?),
//         Algorithm::MlKem1024 => kyber1024::generate_key_pair(random_array(rng)?),
//     }
//     todo!()
// }

// fn kyber_rand(
//     rng: &mut (impl CryptoRng + Rng),
// ) -> Result<[u8; kyber::constants::SHARED_SECRET_SIZE], Error> {
//     let mut seed = [0; kyber::constants::SHARED_SECRET_SIZE];
//     rng.try_fill_bytes(&mut seed).map_err(|_| Error::KeyGen)?;
//     Ok(seed)
// }

// TODO: We should make this an actual type as opposed to alias so we can enforce
// some checks at the type level. This is being tracked in:
// https://github.com/cryspen/libcrux/issues/123
pub type MlKemSharedSecret = [u8; constants::SHARED_SECRET_SIZE];

use self::{
    constant_time_ops::{
        compare_ciphertexts_in_constant_time, select_shared_secret_in_constant_time,
    },
    constants::{CPA_PKE_KEY_GENERATION_SEED_SIZE, H_DIGEST_SIZE, SHARED_SECRET_SIZE},
    hash_functions::{G, H, PRF},
    ind_cpa::{into_padded_array, serialize_public_key},
    serialize::deserialize_ring_elements_reduced,
};

/// Seed size for key generation
pub(crate) const KEY_GENERATION_SEED_SIZE: usize =
    CPA_PKE_KEY_GENERATION_SEED_SIZE + SHARED_SECRET_SIZE;

/// Serialize the secret key.
#[inline(always)]
fn serialize_kem_secret_key<const SERIALIZED_KEY_LEN: usize>(
    private_key: &[u8],
    public_key: &[u8],
    implicit_rejection_value: &[u8],
) -> [u8; SERIALIZED_KEY_LEN] {
    let mut out = [0u8; SERIALIZED_KEY_LEN];
    let mut pointer = 0;
    out[pointer..pointer + private_key.len()].copy_from_slice(private_key);
    pointer += private_key.len();
    out[pointer..pointer + public_key.len()].copy_from_slice(public_key);
    pointer += public_key.len();
    out[pointer..pointer + H_DIGEST_SIZE].copy_from_slice(&H(public_key));
    pointer += H_DIGEST_SIZE;
    out[pointer..pointer + implicit_rejection_value.len()]
        .copy_from_slice(implicit_rejection_value);
    out
}

pub(crate) fn validate_public_key<
    const K: usize,
    const RANKED_BYTES_PER_RING_ELEMENT: usize,
    const PUBLIC_KEY_SIZE: usize,
>(
    public_key: &[u8; PUBLIC_KEY_SIZE],
) -> bool {
    let deserialized_pk = deserialize_ring_elements_reduced::<PUBLIC_KEY_SIZE, K>(
        &public_key[..RANKED_BYTES_PER_RING_ELEMENT],
    );

    let public_key_serialized =
        serialize_public_key::<K, RANKED_BYTES_PER_RING_ELEMENT, PUBLIC_KEY_SIZE>(
            deserialized_pk,
            &public_key[RANKED_BYTES_PER_RING_ELEMENT..],
        );

    *public_key == public_key_serialized
}

pub(crate) fn generate_keypair<
    const K: usize,
    const CPA_PRIVATE_KEY_SIZE: usize,
    const PRIVATE_KEY_SIZE: usize,
    const PUBLIC_KEY_SIZE: usize,
    const BYTES_PER_RING_ELEMENT: usize,
    const ETA1: usize,
    const ETA1_RANDOMNESS_SIZE: usize,
>(
    randomness: [u8; KEY_GENERATION_SEED_SIZE],
) -> MlKemKeyPair<PRIVATE_KEY_SIZE, PUBLIC_KEY_SIZE> {
    let ind_cpa_keypair_randomness = &randomness[0..CPA_PKE_KEY_GENERATION_SEED_SIZE];
    let implicit_rejection_value = &randomness[CPA_PKE_KEY_GENERATION_SEED_SIZE..];

    let (ind_cpa_private_key, public_key) = ind_cpa::generate_keypair::<
        K,
        CPA_PRIVATE_KEY_SIZE,
        PUBLIC_KEY_SIZE,
        BYTES_PER_RING_ELEMENT,
        ETA1,
        ETA1_RANDOMNESS_SIZE,
    >(ind_cpa_keypair_randomness);

    let secret_key_serialized =
        serialize_kem_secret_key(&ind_cpa_private_key, &public_key, implicit_rejection_value);
    let private_key: MlKemPrivateKey<PRIVATE_KEY_SIZE> =
        MlKemPrivateKey::from(secret_key_serialized);

    MlKemKeyPair::from(private_key, public_key.into())
}

pub(crate) fn encapsulate<
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
    public_key: &MlKemPublicKey<PUBLIC_KEY_SIZE>,
    randomness: [u8; SHARED_SECRET_SIZE],
) -> (MlKemCiphertext<CIPHERTEXT_SIZE>, MlKemSharedSecret) {
    let mut to_hash: [u8; 2 * H_DIGEST_SIZE] = into_padded_array(&randomness);
    to_hash[H_DIGEST_SIZE..].copy_from_slice(&H(public_key.as_slice()));

    let hashed = G(&to_hash);
    let (shared_secret, pseudorandomness) = hashed.split_at(SHARED_SECRET_SIZE);

    let ciphertext = ind_cpa::encrypt::<
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

    let mut shared_secret_array = [0u8; constants::SHARED_SECRET_SIZE];
    shared_secret_array.copy_from_slice(shared_secret);
    (ciphertext.into(), shared_secret_array)
}

pub(crate) fn decapsulate<
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
    secret_key: &MlKemPrivateKey<SECRET_KEY_SIZE>,
    ciphertext: &MlKemCiphertext<CIPHERTEXT_SIZE>,
) -> MlKemSharedSecret {
    let (ind_cpa_secret_key, secret_key) = secret_key.split_at(CPA_SECRET_KEY_SIZE);
    let (ind_cpa_public_key, secret_key) = secret_key.split_at(PUBLIC_KEY_SIZE);
    let (ind_cpa_public_key_hash, implicit_rejection_value) = secret_key.split_at(H_DIGEST_SIZE);

    let decrypted = ind_cpa::decrypt::<
        K,
        CIPHERTEXT_SIZE,
        C1_SIZE,
        VECTOR_U_COMPRESSION_FACTOR,
        VECTOR_V_COMPRESSION_FACTOR,
    >(ind_cpa_secret_key, &ciphertext.value);

    let mut to_hash: [u8; SHARED_SECRET_SIZE + H_DIGEST_SIZE] = into_padded_array(&decrypted);
    to_hash[SHARED_SECRET_SIZE..].copy_from_slice(ind_cpa_public_key_hash);

    let hashed = G(&to_hash);
    let (shared_secret, pseudorandomness) = hashed.split_at(SHARED_SECRET_SIZE);

    let mut to_hash: [u8; IMPLICIT_REJECTION_HASH_INPUT_SIZE] =
        into_padded_array(&implicit_rejection_value);
    to_hash[SHARED_SECRET_SIZE..].copy_from_slice(ciphertext.as_ref());
    let implicit_rejection_shared_secret: [u8; SHARED_SECRET_SIZE] = PRF(&to_hash);

    let expected_ciphertext = ind_cpa::encrypt::<
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
        &expected_ciphertext,
    );

    select_shared_secret_in_constant_time(
        shared_secret,
        &implicit_rejection_shared_secret,
        selector,
    )
}
