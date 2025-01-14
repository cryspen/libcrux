//! Incremental API.
//!
//! **WARNING:** This API is not standard compliant and may lead to insecure
//! usage. Use at your own risk.

use core::any::Any;

use crate::{
    hash_functions::Hash,
    ind_cpa::{self, deserialize_secret_key, serialize_secret_key},
    matrix::sample_matrix_A,
    polynomial::PolynomialRingElement,
    utils::into_padded_array,
    SHARED_SECRET_SIZE,
};

use super::{
    unpacked::{encaps_prepare, MlKemPublicKeyUnpacked},
    MlKemPrivateKey, MlKemSharedSecret, Operations, Variant,
};

/// The incremental public key that allows generating [`Ciphertext1`].
pub struct PublicKey1 {
    seed: [u8; 32],
    hash: [u8; 32],
}

impl<const K: usize, Vector: Operations> From<&MlKemPublicKeyUnpacked<K, Vector>> for PublicKey1 {
    fn from(pk: &MlKemPublicKeyUnpacked<K, Vector>) -> Self {
        Self {
            seed: pk.ind_cpa_public_key.seed_for_A,
            hash: pk.public_key_hash,
        }
    }
}

/// The partial ciphertext c1 - first part.
pub struct Ciphertext1<const LEN: usize> {
    pub value: [u8; LEN],
}

/// The incremental public key that allows generating [`Ciphertext2`].
#[repr(transparent)]
pub struct PublicKey2<const K: usize, Vector: Operations> {
    t_as_ntt: [PolynomialRingElement<Vector>; K],
}

/// The incremental public key that allows generating [`Ciphertext2`].
#[repr(transparent)]
pub struct VectorBytes<const LEN: usize> {
    // LEN = K * 512
    bytes: [u8; LEN],
}

impl<const LEN: usize> VectorBytes<LEN> {
    pub fn from_unpacked<const K: usize, Vector: Operations>(
        pk: &MlKemPublicKeyUnpacked<K, Vector>,
    ) -> Self {
        Self {
            bytes: serialize_secret_key(&pk.ind_cpa_public_key.t_as_ntt),
        }
    }
}

impl<const K: usize, Vector: Operations> From<&MlKemPublicKeyUnpacked<K, Vector>>
    for PublicKey2<K, Vector>
{
    fn from(pk: &MlKemPublicKeyUnpacked<K, Vector>) -> Self {
        Self {
            t_as_ntt: pk.ind_cpa_public_key.t_as_ntt,
        }
    }
}

impl<const LEN: usize, const K: usize, Vector: Operations> From<&VectorBytes<LEN>>
    for PublicKey2<K, Vector>
{
    fn from(pk: &VectorBytes<LEN>) -> Self {
        Self {
            t_as_ntt: deserialize_secret_key(&pk.bytes),
        }
    }
}

/// The partial ciphertext c2 - second part.
pub struct Ciphertext2<const LEN: usize> {
    pub value: [u8; LEN],
}

/// The incremental state for encapsulate.
pub struct EncapsState<const VEC_LEN: usize, const RE_LEN: usize> {
    shared_secret: MlKemSharedSecret,
    rho: [u8; 32],
    r_as_ntt: [u8; VEC_LEN],
    error2: [u8; RE_LEN],
    randomness: [u8; 32],
}

pub(crate) fn encapsulate1<
    const K: usize,
    const CIPHERTEXT_SIZE: usize,
    const C1_SIZE: usize,
    const VECTOR_U_COMPRESSION_FACTOR: usize,
    const VECTOR_U_BLOCK_LEN: usize,
    const ETA1: usize,
    const ETA1_RANDOMNESS_SIZE: usize,
    const ETA2: usize,
    const ETA2_RANDOMNESS_SIZE: usize,
    Vector: Operations,
    Hasher: Hash<K>,
>(
    public_key_part: &PublicKey1,
    randomness: [u8; SHARED_SECRET_SIZE],
) -> (Ciphertext1<C1_SIZE>, EncapsState<K, Vector>) {
    let hashed = encaps_prepare::<K, Hasher>(&randomness, &public_key_part.hash);
    let (shared_secret, pseudorandomness) = hashed.split_at(SHARED_SECRET_SIZE);

    // Rebuild the matrix A from the seed
    let mut matrix = [[PolynomialRingElement::<Vector>::ZERO(); K]; K];
    sample_matrix_A::<K, Vector, Hasher>(
        &mut matrix,
        into_padded_array(&public_key_part.seed),
        false,
    );

    let mut ciphertext = [0u8; C1_SIZE];
    let (r_as_ntt, error2) = ind_cpa::encrypt_c1::<
        K,
        C1_SIZE,
        VECTOR_U_COMPRESSION_FACTOR,
        VECTOR_U_BLOCK_LEN,
        ETA1,
        ETA1_RANDOMNESS_SIZE,
        ETA2,
        ETA2_RANDOMNESS_SIZE,
        Vector,
        Hasher,
    >(&pseudorandomness, &matrix, &mut ciphertext);

    let state = EncapsState {
        randomness,
        shared_secret: shared_secret.try_into().unwrap(),
        rho: pseudorandomness.try_into().unwrap(),
        r_as_ntt,
        error2,
    };
    (Ciphertext1 { value: ciphertext }, state)
}

pub(crate) fn encapsulate2<
    const K: usize,
    const C2_SIZE: usize,
    const VECTOR_V_COMPRESSION_FACTOR: usize,
    Vector: Operations,
>(
    state: &EncapsState<K, Vector>,
    public_key_part: &PublicKey2<K, Vector>,
) -> Ciphertext2<C2_SIZE> {
    let mut ciphertext = [0u8; C2_SIZE];
    ind_cpa::encrypt_c2::<K, VECTOR_V_COMPRESSION_FACTOR, C2_SIZE, Vector>(
        &public_key_part.t_as_ntt,
        &state.r_as_ntt,
        &state.error2,
        state.randomness,
        &mut ciphertext,
    );

    Ciphertext2 { value: ciphertext }
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
    Vector: Operations,
    Hasher: Hash<K>,
    Scheme: Variant,
>(
    private_key: &MlKemPrivateKey<SECRET_KEY_SIZE>,
    ciphertext1: &Ciphertext1<C1_SIZE>,
    ciphertext2: &Ciphertext2<C2_SIZE>,
) -> MlKemSharedSecret {
    let mut ciphertext = [0u8; CIPHERTEXT_SIZE];
    ciphertext[..C1_SIZE].copy_from_slice(&ciphertext1.value);
    ciphertext[C1_SIZE..].copy_from_slice(&ciphertext2.value);
    crate::ind_cca::decapsulate::<
        K,
        SECRET_KEY_SIZE,
        CPA_SECRET_KEY_SIZE,
        PUBLIC_KEY_SIZE,
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
        IMPLICIT_REJECTION_HASH_INPUT_SIZE,
        Vector,
        Hasher,
        Scheme,
    >(private_key, &ciphertext.into())
}
