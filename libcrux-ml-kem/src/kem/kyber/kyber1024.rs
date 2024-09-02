use super::{constants::*, *};

// Kyber 1024 parameters
const RANK_1024: usize = 4;
const RANKED_BYTES_PER_RING_ELEMENT_1024: usize = RANK_1024 * BITS_PER_RING_ELEMENT / 8;
const T_AS_NTT_ENCODED_SIZE_1024: usize =
    (RANK_1024 * COEFFICIENTS_IN_RING_ELEMENT * BITS_PER_COEFFICIENT) / 8;
const VECTOR_U_COMPRESSION_FACTOR_1024: usize = 11;
// [hax]: hacspec/hacspec-v2#27 stealing error
// block_len::<VECTOR_U_COMPRESSION_FACTOR_1024>();
const C1_BLOCK_SIZE_1024: usize =
    (COEFFICIENTS_IN_RING_ELEMENT * VECTOR_U_COMPRESSION_FACTOR_1024) / 8;
// [hax]: hacspec/hacspec-v2#27 stealing error
// serialized_len::<RANK_1024, C1_BLOCK_SIZE_1024>();
const C1_SIZE_1024: usize = C1_BLOCK_SIZE_1024 * RANK_1024;
const VECTOR_V_COMPRESSION_FACTOR_1024: usize = 5;
// [hax]: hacspec/hacspec-v2#27 stealing error
// block_len::<VECTOR_V_COMPRESSION_FACTOR_1024>()
const C2_SIZE_1024: usize = (COEFFICIENTS_IN_RING_ELEMENT * VECTOR_V_COMPRESSION_FACTOR_1024) / 8;
const CPA_PKE_SECRET_KEY_SIZE_1024: usize =
    (RANK_1024 * COEFFICIENTS_IN_RING_ELEMENT * BITS_PER_COEFFICIENT) / 8;
const CPA_PKE_PUBLIC_KEY_SIZE_1024: usize = T_AS_NTT_ENCODED_SIZE_1024 + 32;
const CPA_PKE_CIPHERTEXT_SIZE_1024: usize = C1_SIZE_1024 + C2_SIZE_1024;
const SECRET_KEY_SIZE_1024: usize = CPA_PKE_SECRET_KEY_SIZE_1024
    + CPA_PKE_PUBLIC_KEY_SIZE_1024
    + H_DIGEST_SIZE
    + SHARED_SECRET_SIZE;

const ETA1: usize = 2;
const ETA1_RANDOMNESS_SIZE: usize = ETA1 * 64;
const ETA2: usize = 2;
const ETA2_RANDOMNESS_SIZE: usize = ETA2 * 64;

const IMPLICIT_REJECTION_HASH_INPUT_SIZE: usize = SHARED_SECRET_SIZE + CPA_PKE_CIPHERTEXT_SIZE_1024;

// Kyber 1024 types
/// An ML-KEM 1024 Ciphertext
pub type MlKem1024Ciphertext = MlKemCiphertext<CPA_PKE_CIPHERTEXT_SIZE_1024>;
/// An ML-KEM 1024 Private key
pub type MlKem1024PrivateKey = MlKemPrivateKey<SECRET_KEY_SIZE_1024>;
/// An ML-KEM 1024 Public key
pub type MlKem1024PublicKey = MlKemPublicKey<CPA_PKE_PUBLIC_KEY_SIZE_1024>;

/// Validate a public key.
///
/// Returns `true` if valid, and `false` otherwise.
pub fn validate_public_key(public_key: &MlKem1024PublicKey) -> bool {
    super::validate_public_key::<
        RANK_1024,
        RANKED_BYTES_PER_RING_ELEMENT_1024,
        CPA_PKE_PUBLIC_KEY_SIZE_1024,
    >(&public_key.value)
}

/// Generate ML-KEM 1024 Key Pair
///
/// Generate an ML-KEM key pair. The input is a byte array of size
/// [`crate::KEY_GENERATION_SEED_SIZE`].
pub fn generate_key_pair(
    randomness: [u8; KEY_GENERATION_SEED_SIZE],
) -> MlKemKeyPair<SECRET_KEY_SIZE_1024, CPA_PKE_PUBLIC_KEY_SIZE_1024> {
    generate_keypair::<
        RANK_1024,
        CPA_PKE_SECRET_KEY_SIZE_1024,
        SECRET_KEY_SIZE_1024,
        CPA_PKE_PUBLIC_KEY_SIZE_1024,
        RANKED_BYTES_PER_RING_ELEMENT_1024,
        ETA1,
        ETA1_RANDOMNESS_SIZE,
    >(randomness)
}

#[allow(unused)]
pub(crate) type MlKem1024State = MlKemState<RANK_1024>;

#[allow(unused)]
pub(crate) fn generate_key_pair_unpacked(
    randomness: [u8; KEY_GENERATION_SEED_SIZE],
) -> (MlKem1024State, MlKem1024PublicKey) {
    generate_keypair_unpacked::<
        RANK_1024,
        CPA_PKE_SECRET_KEY_SIZE_1024,
        SECRET_KEY_SIZE_1024,
        CPA_PKE_PUBLIC_KEY_SIZE_1024,
        RANKED_BYTES_PER_RING_ELEMENT_1024,
        ETA1,
        ETA1_RANDOMNESS_SIZE,
    >(randomness)
}

/// Encapsulate ML-KEM 1024
///
/// Generates an ([`MlKem1024Ciphertext`], [`MlKemSharedSecret`]) tuple.
/// The input is a reference to an [`MlKem1024PublicKey`] and [`crate::SHARED_SECRET_SIZE`]
/// bytes of `randomness`.
pub fn encapsulate(
    public_key: &MlKemPublicKey<CPA_PKE_PUBLIC_KEY_SIZE_1024>,
    randomness: [u8; SHARED_SECRET_SIZE],
) -> (
    MlKemCiphertext<CPA_PKE_CIPHERTEXT_SIZE_1024>,
    MlKemSharedSecret,
) {
    super::encapsulate::<
        RANK_1024,
        CPA_PKE_CIPHERTEXT_SIZE_1024,
        CPA_PKE_PUBLIC_KEY_SIZE_1024,
        T_AS_NTT_ENCODED_SIZE_1024,
        C1_SIZE_1024,
        C2_SIZE_1024,
        VECTOR_U_COMPRESSION_FACTOR_1024,
        VECTOR_V_COMPRESSION_FACTOR_1024,
        C1_BLOCK_SIZE_1024,
        ETA1,
        ETA1_RANDOMNESS_SIZE,
        ETA2,
        ETA2_RANDOMNESS_SIZE,
    >(public_key, randomness)
}

/// Decapsulate ML-KEM 1024
///
/// Generates an [`MlKemSharedSecret`].
/// The input is a reference to an [`MlKem1024PrivateKey`] and an [`MlKem1024Ciphertext`].
pub fn decapsulate(
    secret_key: &MlKemPrivateKey<SECRET_KEY_SIZE_1024>,
    ciphertext: &MlKemCiphertext<CPA_PKE_CIPHERTEXT_SIZE_1024>,
) -> [u8; SHARED_SECRET_SIZE] {
    super::decapsulate::<
        RANK_1024,
        SECRET_KEY_SIZE_1024,
        CPA_PKE_SECRET_KEY_SIZE_1024,
        CPA_PKE_PUBLIC_KEY_SIZE_1024,
        CPA_PKE_CIPHERTEXT_SIZE_1024,
        T_AS_NTT_ENCODED_SIZE_1024,
        C1_SIZE_1024,
        C2_SIZE_1024,
        VECTOR_U_COMPRESSION_FACTOR_1024,
        VECTOR_V_COMPRESSION_FACTOR_1024,
        C1_BLOCK_SIZE_1024,
        ETA1,
        ETA1_RANDOMNESS_SIZE,
        ETA2,
        ETA2_RANDOMNESS_SIZE,
        IMPLICIT_REJECTION_HASH_INPUT_SIZE,
    >(secret_key, ciphertext)
}

#[allow(unused)]
pub(crate) fn decapsulate_unpacked(
    state: &MlKem1024State,
    ciphertext: &MlKemCiphertext<CPA_PKE_CIPHERTEXT_SIZE_1024>,
) -> [u8; SHARED_SECRET_SIZE] {
    super::decapsulate_unpacked::<
        RANK_1024,
        SECRET_KEY_SIZE_1024,
        CPA_PKE_SECRET_KEY_SIZE_1024,
        CPA_PKE_PUBLIC_KEY_SIZE_1024,
        CPA_PKE_CIPHERTEXT_SIZE_1024,
        T_AS_NTT_ENCODED_SIZE_1024,
        C1_SIZE_1024,
        C2_SIZE_1024,
        VECTOR_U_COMPRESSION_FACTOR_1024,
        VECTOR_V_COMPRESSION_FACTOR_1024,
        C1_BLOCK_SIZE_1024,
        ETA1,
        ETA1_RANDOMNESS_SIZE,
        ETA2,
        ETA2_RANDOMNESS_SIZE,
        IMPLICIT_REJECTION_HASH_INPUT_SIZE,
    >(state, ciphertext)
}
