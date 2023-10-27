use super::{constants::*, *};

// Kyber 768 parameters
const RANK_768: usize = 3;
const RANKED_BYTES_PER_RING_ELEMENT_768: usize = RANK_768 * BITS_PER_RING_ELEMENT / 8;
const T_AS_NTT_ENCODED_SIZE_768: usize =
    (RANK_768 * COEFFICIENTS_IN_RING_ELEMENT * BITS_PER_COEFFICIENT) / 8;
const VECTOR_U_COMPRESSION_FACTOR_768: usize = 10;
// [hax]: hacspec/hacspec-v2#27 stealing error
// block_len::<VECTOR_U_COMPRESSION_FACTOR_768>()
const C1_BLOCK_SIZE_768: usize =
    (COEFFICIENTS_IN_RING_ELEMENT * VECTOR_U_COMPRESSION_FACTOR_768) / 8;
// [hax]: hacspec/hacspec-v2#27 stealing error
//  serialized_len::<RANK_768, C1_BLOCK_SIZE_768>();
const C1_SIZE_768: usize = C1_BLOCK_SIZE_768 * RANK_768;
const VECTOR_V_COMPRESSION_FACTOR_768: usize = 4;
// [hax]: hacspec/hacspec-v2#27 stealing error
//  block_len::<VECTOR_V_COMPRESSION_FACTOR_768>()
const C2_SIZE_768: usize = (COEFFICIENTS_IN_RING_ELEMENT * VECTOR_V_COMPRESSION_FACTOR_768) / 8;
const CPA_PKE_SECRET_KEY_SIZE_768: usize =
    (RANK_768 * COEFFICIENTS_IN_RING_ELEMENT * BITS_PER_COEFFICIENT) / 8;
const CPA_PKE_PUBLIC_KEY_SIZE_768: usize = T_AS_NTT_ENCODED_SIZE_768 + 32;
// These two are used in the hybrid kem. This could probably be improved.
pub(in crate::kem) const CPA_PKE_CIPHERTEXT_SIZE_768: usize = C1_SIZE_768 + C2_SIZE_768;
pub(in crate::kem) const SECRET_KEY_SIZE_768: usize =
    CPA_PKE_SECRET_KEY_SIZE_768 + CPA_PKE_PUBLIC_KEY_SIZE_768 + H_DIGEST_SIZE + SHARED_SECRET_SIZE;

const ETA1: usize = 2;
const ETA1_RANDOMNESS_SIZE: usize = ETA1 * 64;
const ETA2: usize = 2;
const ETA2_RANDOMNESS_SIZE: usize = ETA2 * 64;

const IMPLICIT_REJECTION_HASH_INPUT_SIZE: usize = SHARED_SECRET_SIZE + CPA_PKE_CIPHERTEXT_SIZE_768;

// Kyber 768 types
pub type Kyber768Ciphertext = KyberCiphertext<CPA_PKE_CIPHERTEXT_SIZE_768>;
pub type Kyber768PrivateKey = KyberPrivateKey<SECRET_KEY_SIZE_768>;
pub type Kyber768PublicKey = KyberPublicKey<CPA_PKE_PUBLIC_KEY_SIZE_768>;

/// Generate Kyber 768 Key Pair
pub fn generate_key_pair_768(
    randomness: [u8; KEY_GENERATION_SEED_SIZE],
) -> Result<KyberKeyPair<SECRET_KEY_SIZE_768, CPA_PKE_PUBLIC_KEY_SIZE_768>, Error> {
    generate_keypair::<
        RANK_768,
        CPA_PKE_SECRET_KEY_SIZE_768,
        SECRET_KEY_SIZE_768,
        CPA_PKE_PUBLIC_KEY_SIZE_768,
        RANKED_BYTES_PER_RING_ELEMENT_768,
        ETA1,
        ETA1_RANDOMNESS_SIZE,
    >(randomness)
}

/// Encapsulate Kyber 768
pub fn encapsulate_768(
    public_key: &KyberPublicKey<CPA_PKE_PUBLIC_KEY_SIZE_768>,
    randomness: [u8; SHARED_SECRET_SIZE],
) -> Result<
    (
        KyberCiphertext<CPA_PKE_CIPHERTEXT_SIZE_768>,
        KyberSharedSecret,
    ),
    Error,
> {
    encapsulate::<
        RANK_768,
        CPA_PKE_CIPHERTEXT_SIZE_768,
        CPA_PKE_PUBLIC_KEY_SIZE_768,
        T_AS_NTT_ENCODED_SIZE_768,
        C1_SIZE_768,
        C2_SIZE_768,
        VECTOR_U_COMPRESSION_FACTOR_768,
        VECTOR_V_COMPRESSION_FACTOR_768,
        C1_BLOCK_SIZE_768,
        ETA1,
        ETA1_RANDOMNESS_SIZE,
        ETA2,
        ETA2_RANDOMNESS_SIZE,
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
        ETA1,
        ETA1_RANDOMNESS_SIZE,
        ETA2,
        ETA2_RANDOMNESS_SIZE,
        IMPLICIT_REJECTION_HASH_INPUT_SIZE,
    >(secret_key, ciphertext)
}
