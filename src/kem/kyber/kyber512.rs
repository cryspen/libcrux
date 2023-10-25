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

// Kyber 512 types
pub type Kyber512Ciphertext = KyberCiphertext<CPA_PKE_CIPHERTEXT_SIZE_512>;
pub type Kyber512PrivateKey = KyberPrivateKey<SECRET_KEY_SIZE_512>;
pub type Kyber512PublicKey = KyberPublicKey<CPA_PKE_PUBLIC_KEY_SIZE_512>;

/// Generate Kyber 512 Key Pair
pub fn generate_key_pair_512(
    randomness: [u8; KEY_GENERATION_SEED_SIZE],
) -> Result<
    KyberKeyPair<SECRET_KEY_SIZE_512, CPA_PKE_PUBLIC_KEY_SIZE_512>,
    BadRejectionSamplingRandomnessError,
> {
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

/// Encapsulate Kyber 512
pub fn encapsulate_512(
    public_key: &KyberPublicKey<CPA_PKE_PUBLIC_KEY_SIZE_512>,
    randomness: [u8; SHARED_SECRET_SIZE],
) -> Result<
    (
        KyberCiphertext<CPA_PKE_CIPHERTEXT_SIZE_512>,
        KyberSharedSecret,
    ),
    BadRejectionSamplingRandomnessError,
> {
    encapsulate::<
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

/// Decapsulate Kyber 512
pub fn decapsulate_512(
    secret_key: &KyberPrivateKey<SECRET_KEY_SIZE_512>,
    ciphertext: &KyberCiphertext<CPA_PKE_CIPHERTEXT_SIZE_512>,
) -> [u8; SHARED_SECRET_SIZE] {
    decapsulate::<
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
    >(secret_key, ciphertext)
}
