use super::{constants::*, *};

// Kyber 512 parameters
const RANK_512: usize = 2;
const RANKED_BYTES_PER_RING_ELEMENT_512: usize = RANK_512 * BITS_PER_RING_ELEMENT / 8;
const T_AS_NTT_ENCODED_SIZE_512: usize =
    (RANK_512 * COEFFICIENTS_IN_RING_ELEMENT * BITS_PER_COEFFICIENT) / 8;
const VECTOR_U_COMPRESSION_FACTOR_512: usize = 10;
// [hax]: hacspec/hacspec-v2#27 stealing error
// block_len::<VECTOR_U_COMPRESSION_FACTOR_512>()
const C1_BLOCK_SIZE_512: usize =
    (COEFFICIENTS_IN_RING_ELEMENT * VECTOR_U_COMPRESSION_FACTOR_512) / 8;
// [hax]: hacspec/hacspec-v2#27 stealing error
// serialized_len::<RANK_512, C1_BLOCK_SIZE_512>()
const C1_SIZE_512: usize = C1_BLOCK_SIZE_512 * RANK_512;
const VECTOR_V_COMPRESSION_FACTOR_512: usize = 4;
// [hax]: hacspec/hacspec-v2#27 stealing error
// block_len::<VECTOR_V_COMPRESSION_FACTOR_512>()
const C2_SIZE_512: usize = (COEFFICIENTS_IN_RING_ELEMENT * VECTOR_V_COMPRESSION_FACTOR_512) / 8;
const CPA_PKE_SECRET_KEY_SIZE_512: usize =
    (RANK_512 * COEFFICIENTS_IN_RING_ELEMENT * BITS_PER_COEFFICIENT) / 8;
const CPA_PKE_PUBLIC_KEY_SIZE_512: usize = T_AS_NTT_ENCODED_SIZE_512 + 32;
const CPA_PKE_CIPHERTEXT_SIZE_512: usize = C1_SIZE_512 + C2_SIZE_512;
const SECRET_KEY_SIZE_512: usize =
    CPA_PKE_SECRET_KEY_SIZE_512 + CPA_PKE_PUBLIC_KEY_SIZE_512 + H_DIGEST_SIZE + SHARED_SECRET_SIZE;

const ETA1: usize = 3;
const ETA1_RANDOMNESS_SIZE: usize = ETA1 * 64;
const ETA2: usize = 2;
const ETA2_RANDOMNESS_SIZE: usize = ETA2 * 64;

const IMPLICIT_REJECTION_HASH_INPUT_SIZE: usize = SHARED_SECRET_SIZE + CPA_PKE_CIPHERTEXT_SIZE_512;

// Kyber 512 types
/// An ML-KEM 512 Ciphertext
pub type MlKem512Ciphertext = MlKemCiphertext<CPA_PKE_CIPHERTEXT_SIZE_512>;
/// An ML-KEM 512 Private key
pub type MlKem512PrivateKey = MlKemPrivateKey<SECRET_KEY_SIZE_512>;
/// An ML-KEM 512 Public key
pub type MlKem512PublicKey = MlKemPublicKey<CPA_PKE_PUBLIC_KEY_SIZE_512>;

/// Validate a public key.
///
/// Returns `true` if valid, and `false` otherwise.
pub fn validate_public_key(public_key: &MlKem512PublicKey) -> bool {
    super::validate_public_key::<
        RANK_512,
        RANKED_BYTES_PER_RING_ELEMENT_512,
        CPA_PKE_PUBLIC_KEY_SIZE_512,
    >(&public_key.value)
}

/// Generate ML-KEM 512 Key Pair
///
/// The input is a byte array of size
/// [`crate::KEY_GENERATION_SEED_SIZE`].
pub fn generate_key_pair(
    randomness: [u8; KEY_GENERATION_SEED_SIZE],
) -> MlKemKeyPair<SECRET_KEY_SIZE_512, CPA_PKE_PUBLIC_KEY_SIZE_512> {
    generate_keypair::<
        RANK_512,
        CPA_PKE_SECRET_KEY_SIZE_512,
        SECRET_KEY_SIZE_512,
        CPA_PKE_PUBLIC_KEY_SIZE_512,
        RANKED_BYTES_PER_RING_ELEMENT_512,
        ETA1,
        ETA1_RANDOMNESS_SIZE,
    >(randomness)
}

#[allow(unused)]
pub(crate) type MlKem512State = MlKemState<RANK_512>;

#[allow(unused)]
pub(crate) fn generate_key_pair_unpacked(
    randomness: [u8; KEY_GENERATION_SEED_SIZE],
) -> (MlKem512State, MlKem512PublicKey) {
    generate_keypair_unpacked::<
        RANK_512,
        CPA_PKE_SECRET_KEY_SIZE_512,
        SECRET_KEY_SIZE_512,
        CPA_PKE_PUBLIC_KEY_SIZE_512,
        RANKED_BYTES_PER_RING_ELEMENT_512,
        ETA1,
        ETA1_RANDOMNESS_SIZE,
    >(randomness)
}

/// Encapsulate ML-KEM 512
///
/// Generates an ([`MlKem512Ciphertext`], [`MlKemSharedSecret`]) tuple.
/// The input is a reference to an [`MlKem512PublicKey`] and [`crate::SHARED_SECRET_SIZE`]
pub fn encapsulate(
    public_key: &MlKemPublicKey<CPA_PKE_PUBLIC_KEY_SIZE_512>,
    randomness: [u8; SHARED_SECRET_SIZE],
) -> (
    MlKemCiphertext<CPA_PKE_CIPHERTEXT_SIZE_512>,
    MlKemSharedSecret,
) {
    super::encapsulate::<
        RANK_512,
        CPA_PKE_CIPHERTEXT_SIZE_512,
        CPA_PKE_PUBLIC_KEY_SIZE_512,
        T_AS_NTT_ENCODED_SIZE_512,
        C1_SIZE_512,
        C2_SIZE_512,
        VECTOR_U_COMPRESSION_FACTOR_512,
        VECTOR_V_COMPRESSION_FACTOR_512,
        C1_BLOCK_SIZE_512,
        ETA1,
        ETA1_RANDOMNESS_SIZE,
        ETA2,
        ETA2_RANDOMNESS_SIZE,
    >(public_key, randomness)
}

/// Decapsulate ML-KEM 512
///
/// Generates an [`MlKemSharedSecret`].
/// The input is a reference to an [`MlKem512PrivateKey`] and an [`MlKem512Ciphertext`].
pub fn decapsulate(
    secret_key: &MlKemPrivateKey<SECRET_KEY_SIZE_512>,
    ciphertext: &MlKemCiphertext<CPA_PKE_CIPHERTEXT_SIZE_512>,
) -> [u8; SHARED_SECRET_SIZE] {
    super::decapsulate::<
        RANK_512,
        SECRET_KEY_SIZE_512,
        CPA_PKE_SECRET_KEY_SIZE_512,
        CPA_PKE_PUBLIC_KEY_SIZE_512,
        CPA_PKE_CIPHERTEXT_SIZE_512,
        T_AS_NTT_ENCODED_SIZE_512,
        C1_SIZE_512,
        C2_SIZE_512,
        VECTOR_U_COMPRESSION_FACTOR_512,
        VECTOR_V_COMPRESSION_FACTOR_512,
        C1_BLOCK_SIZE_512,
        ETA1,
        ETA1_RANDOMNESS_SIZE,
        ETA2,
        ETA2_RANDOMNESS_SIZE,
        IMPLICIT_REJECTION_HASH_INPUT_SIZE,
    >(secret_key, ciphertext)
}

#[allow(unused)]
pub(crate) fn decapsulate_unpacked(
    state: &MlKem512State,
    ciphertext: &MlKemCiphertext<CPA_PKE_CIPHERTEXT_SIZE_512>,
) -> [u8; SHARED_SECRET_SIZE] {
    super::decapsulate_unpacked::<
        RANK_512,
        SECRET_KEY_SIZE_512,
        CPA_PKE_SECRET_KEY_SIZE_512,
        CPA_PKE_PUBLIC_KEY_SIZE_512,
        CPA_PKE_CIPHERTEXT_SIZE_512,
        T_AS_NTT_ENCODED_SIZE_512,
        C1_SIZE_512,
        C2_SIZE_512,
        VECTOR_U_COMPRESSION_FACTOR_512,
        VECTOR_V_COMPRESSION_FACTOR_512,
        C1_BLOCK_SIZE_512,
        ETA1,
        ETA1_RANDOMNESS_SIZE,
        ETA2,
        ETA2_RANDOMNESS_SIZE,
        IMPLICIT_REJECTION_HASH_INPUT_SIZE,
    >(state, ciphertext)
}
