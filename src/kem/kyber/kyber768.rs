use super::{parameters::*, *};

// Kyber 768 types
pub type Kyber768Ciphertext = KyberCiphertext<CPA_PKE_CIPHERTEXT_SIZE_768>;
pub type Kyber768PrivateKey = KyberPrivateKey<SECRET_KEY_SIZE_768>;
pub type Kyber768PublicKey = KyberPublicKey<CPA_PKE_PUBLIC_KEY_SIZE_768>;
pub type Kyber768SharedSecret = KyberSharedSecret<SHARED_SECRET_SIZE>;

/// Generate Kyber 768 Key Pair
pub fn generate_key_pair_768(
    randomness: [u8; KEY_GENERATION_SEED_SIZE],
) -> Result<
    KyberKeyPair<SECRET_KEY_SIZE_768, CPA_PKE_PUBLIC_KEY_SIZE_768>,
    BadRejectionSamplingRandomnessError,
> {
    generate_keypair::<
        RANK_768,
        CPA_PKE_SECRET_KEY_SIZE_768,
        SECRET_KEY_SIZE_768,
        CPA_PKE_PUBLIC_KEY_SIZE_768,
        RANKED_BYTES_PER_RING_ELEMENT_768,
    >(randomness)
}

/// Encapsulate Kyber 768
pub fn encapsulate_768(
    public_key: &KyberPublicKey<CPA_PKE_PUBLIC_KEY_SIZE_768>,
    randomness: [u8; SHARED_SECRET_SIZE],
) -> Result<
    (
        KyberCiphertext<CPA_PKE_CIPHERTEXT_SIZE_768>,
        KyberSharedSecret<SHARED_SECRET_SIZE>,
    ),
    BadRejectionSamplingRandomnessError,
> {
    encapsulate::<
        RANK_768,
        SHARED_SECRET_SIZE,
        CPA_PKE_CIPHERTEXT_SIZE_768,
        CPA_PKE_PUBLIC_KEY_SIZE_768,
        T_AS_NTT_ENCODED_SIZE_768,
        C1_SIZE_768,
        C2_SIZE_768,
        VECTOR_U_COMPRESSION_FACTOR_768,
        VECTOR_V_COMPRESSION_FACTOR_768,
        C1_BLOCK_SIZE_768,
    >(public_key, randomness)
}

/// Decapsulate Kyber 768
pub fn decapsulate_768(
    secret_key: &KyberPrivateKey<SECRET_KEY_SIZE_768>,
    ciphertext: &KyberCiphertext<CPA_PKE_CIPHERTEXT_SIZE_768>,
) -> [u8; SHARED_SECRET_SIZE] {
    decapsulate::<
        RANK_768,
        SECRET_KEY_SIZE_768,
        CPA_PKE_SECRET_KEY_SIZE_768,
        CPA_PKE_PUBLIC_KEY_SIZE_768,
        CPA_PKE_CIPHERTEXT_SIZE_768,
        T_AS_NTT_ENCODED_SIZE_768,
        C1_SIZE_768,
        C2_SIZE_768,
        VECTOR_U_COMPRESSION_FACTOR_768,
        VECTOR_V_COMPRESSION_FACTOR_768,
        C1_BLOCK_SIZE_768,
    >(secret_key, ciphertext)
}
