use super::{parameters::*, *};

// Kyber 1024 types
pub type Kyber1024Ciphertext = KyberCiphertext<CPA_PKE_CIPHERTEXT_SIZE_1024>;
pub type Kyber1024PrivateKey = KyberPrivateKey<SECRET_KEY_SIZE_1024>;
pub type Kyber1024PublicKey = KyberPublicKey<CPA_PKE_PUBLIC_KEY_SIZE_1024>;
pub type Kyber1024SharedSecret = KyberSharedSecret<SHARED_SECRET_SIZE>;

/// Generate Kyber 1024 Key Pair
pub fn generate_key_pair_1024(
    randomness: [u8; KEY_GENERATION_SEED_SIZE],
) -> Result<
    KyberKeyPair<SECRET_KEY_SIZE_1024, CPA_PKE_PUBLIC_KEY_SIZE_1024>,
    BadRejectionSamplingRandomnessError,
> {
    generate_keypair::<
        RANK_1024,
        CPA_PKE_SECRET_KEY_SIZE_1024,
        SECRET_KEY_SIZE_1024,
        CPA_PKE_PUBLIC_KEY_SIZE_1024,
        RANKED_BYTES_PER_RING_ELEMENT_1024,
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
    BadRejectionSamplingRandomnessError,
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
    >(secret_key, ciphertext)
}
