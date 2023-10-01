use super::{constants::*, *};

// Kyber 512 parameters
const RANK_512: usize = 2;
const RANKED_BYTES_PER_RING_ELEMENT_512: usize = RANK_512 * BITS_PER_RING_ELEMENT / 8;
const T_AS_NTT_ENCODED_SIZE_512: usize =
    (RANK_512 * COEFFICIENTS_IN_RING_ELEMENT * BITS_PER_COEFFICIENT) / 8;
const VECTOR_U_COMPRESSION_FACTOR_512: usize = 10;
const C1_BLOCK_SIZE_512: usize = block_len::<VECTOR_U_COMPRESSION_FACTOR_512>();
const C1_SIZE_512: usize = serialized_len::<RANK_512, C1_BLOCK_SIZE_512>();
const VECTOR_V_COMPRESSION_FACTOR_512: usize = 4;
const C2_SIZE_512: usize = block_len::<VECTOR_V_COMPRESSION_FACTOR_512>();
const BYTES_PER_ENCODED_ELEMENT_OF_U: usize =
    (COEFFICIENTS_IN_RING_ELEMENT * VECTOR_U_COMPRESSION_FACTOR_512) / 8;
const VECTOR_U_ENCODED_SIZE_512: usize = RANK_512 * BYTES_PER_ENCODED_ELEMENT_OF_U;
const VECTOR_V_ENCODED_SIZE_512: usize =
    (COEFFICIENTS_IN_RING_ELEMENT * VECTOR_V_COMPRESSION_FACTOR_512) / 8;
const CPA_PKE_SECRET_KEY_SIZE_512: usize =
    (RANK_512 * COEFFICIENTS_IN_RING_ELEMENT * BITS_PER_COEFFICIENT) / 8;
const CPA_PKE_PUBLIC_KEY_SIZE_512: usize = T_AS_NTT_ENCODED_SIZE_512 + 32;
const CPA_PKE_CIPHERTEXT_SIZE_512: usize = VECTOR_U_ENCODED_SIZE_512 + VECTOR_V_ENCODED_SIZE_512;
const SECRET_KEY_SIZE_512: usize =
    CPA_PKE_SECRET_KEY_SIZE_512 + CPA_PKE_PUBLIC_KEY_SIZE_512 + H_DIGEST_SIZE + SHARED_SECRET_SIZE;

// Kyber 512 types
pub type Kyber512Ciphertext = KyberCiphertext<CPA_PKE_CIPHERTEXT_SIZE_512>;
pub type Kyber512PrivateKey = KyberPrivateKey<SECRET_KEY_SIZE_512>;
pub type Kyber512PublicKey = KyberPublicKey<CPA_PKE_PUBLIC_KEY_SIZE_512>;
pub type Kyber512SharedSecret = KyberSharedSecret<SHARED_SECRET_SIZE>;

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
    >(randomness)
}

/// Encapsulate Kyber 512
pub fn encapsulate_512(
    public_key: &KyberPublicKey<CPA_PKE_PUBLIC_KEY_SIZE_512>,
    randomness: [u8; SHARED_SECRET_SIZE],
) -> Result<
    (
        KyberCiphertext<CPA_PKE_CIPHERTEXT_SIZE_512>,
        KyberSharedSecret<SHARED_SECRET_SIZE>,
    ),
    BadRejectionSamplingRandomnessError,
> {
    encapsulate::<
        RANK_512,
        SHARED_SECRET_SIZE,
        CPA_PKE_CIPHERTEXT_SIZE_512,
        CPA_PKE_PUBLIC_KEY_SIZE_512,
        T_AS_NTT_ENCODED_SIZE_512,
        C1_SIZE_512,
        C2_SIZE_512,
        VECTOR_U_COMPRESSION_FACTOR_512,
        VECTOR_V_COMPRESSION_FACTOR_512,
        C1_BLOCK_SIZE_512,
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
    >(secret_key, ciphertext)
}
