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

// Kyber 1024 types
pub type Kyber1024Ciphertext = KyberCiphertext<CPA_PKE_CIPHERTEXT_SIZE_1024>;
pub type Kyber1024PrivateKey = KyberPrivateKey<SECRET_KEY_SIZE_1024>;
pub type Kyber1024PublicKey = KyberPublicKey<CPA_PKE_PUBLIC_KEY_SIZE_1024>;
pub type Kyber1024SharedSecret = KyberSharedSecret<SHARED_SECRET_SIZE>;

/// Generate Kyber 1024 Key Pair
pub fn generate_key_pair_1024(
    randomness: [u8; KEY_GENERATION_SEED_SIZE],
) -> Result<KyberKeyPair<SECRET_KEY_SIZE_1024, CPA_PKE_PUBLIC_KEY_SIZE_1024>, Error> {
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

/// Encapsulate Kyber 1024
pub fn encapsulate_1024(
    public_key: &KyberPublicKey<CPA_PKE_PUBLIC_KEY_SIZE_1024>,
    randomness: [u8; SHARED_SECRET_SIZE],
) -> Result<
    (
        KyberCiphertext<CPA_PKE_CIPHERTEXT_SIZE_1024>,
        KyberSharedSecret<SHARED_SECRET_SIZE>,
    ),
    Error,
> {
    encapsulate::<
        RANK_1024,
        SHARED_SECRET_SIZE,
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

/// Decapsulate Kyber 1024
pub fn decapsulate_1024(
    secret_key: &KyberPrivateKey<SECRET_KEY_SIZE_1024>,
    ciphertext: &KyberCiphertext<CPA_PKE_CIPHERTEXT_SIZE_1024>,
) -> [u8; SHARED_SECRET_SIZE] {
    decapsulate::<
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
    >(secret_key, ciphertext)
}
