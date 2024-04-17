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
pub type MlKem768Ciphertext = MlKemCiphertext<CPA_PKE_CIPHERTEXT_SIZE_768>;
pub type MlKem768PrivateKey = MlKemPrivateKey<SECRET_KEY_SIZE_768>;
pub type MlKem768PublicKey = MlKemPublicKey<CPA_PKE_PUBLIC_KEY_SIZE_768>;

/// Validate a public key.
///
/// Returns `Some(public_key)` if valid, and `None` otherwise.
pub fn validate_public_key(public_key: MlKem768PublicKey) -> Option<MlKem768PublicKey> {
    if super::validate_public_key::<
        RANK_768,
        RANKED_BYTES_PER_RING_ELEMENT_768,
        CPA_PKE_PUBLIC_KEY_SIZE_768,
    >(&public_key.value)
    {
        Some(public_key)
    } else {
        None
    }
}

/// Generate ML-KEM 768 Key Pair
pub fn generate_key_pair(
    randomness: [u8; KEY_GENERATION_SEED_SIZE],
) -> MlKemKeyPair<SECRET_KEY_SIZE_768, CPA_PKE_PUBLIC_KEY_SIZE_768> {
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

pub fn generate_key_pair_unpacked(
    randomness: [u8; KEY_GENERATION_SEED_SIZE],
) -> (([PolynomialRingElement;3],[PolynomialRingElement;3],[[PolynomialRingElement;3];3],[u8;32],[u8;32]),MlKemPublicKey<CPA_PKE_PUBLIC_KEY_SIZE_768>)  {
    generate_keypair_unpacked::<
        RANK_768,
        CPA_PKE_SECRET_KEY_SIZE_768,
        SECRET_KEY_SIZE_768,
        CPA_PKE_PUBLIC_KEY_SIZE_768,
        RANKED_BYTES_PER_RING_ELEMENT_768,
        ETA1,
        ETA1_RANDOMNESS_SIZE,
    >(randomness)
}

/// Encapsulate ML-KEM 768
pub fn encapsulate(
    public_key: &MlKemPublicKey<CPA_PKE_PUBLIC_KEY_SIZE_768>,
    randomness: [u8; SHARED_SECRET_SIZE],
) -> (
    MlKemCiphertext<CPA_PKE_CIPHERTEXT_SIZE_768>,
    MlKemSharedSecret,
) {
    super::encapsulate::<
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

/// Decapsulate ML-KEM 768
pub fn decapsulate(
    secret_key: &MlKemPrivateKey<SECRET_KEY_SIZE_768>,
    ciphertext: &MlKemCiphertext<CPA_PKE_CIPHERTEXT_SIZE_768>,
) -> [u8; SHARED_SECRET_SIZE] {
    super::decapsulate::<
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

pub fn decapsulate_unpacked(
    secret_as_ntt: &[PolynomialRingElement;3],
    t_as_ntt: &[PolynomialRingElement;3],
    a_transpose: &[[PolynomialRingElement;3];3],
    implicit_rejection_value: &[u8],
    ind_cpa_public_key_hash: &[u8],
    ciphertext: &MlKemCiphertext<CPA_PKE_CIPHERTEXT_SIZE_768>,
) -> [u8; SHARED_SECRET_SIZE] {
    super::decapsulate_unpacked::<
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
    >(secret_as_ntt,t_as_ntt,a_transpose,implicit_rejection_value,ind_cpa_public_key_hash,ciphertext)
}

#[cfg(test)]
mod tests {
    use rand_core::{OsRng, RngCore};

    use super::{
        kyber768::{generate_key_pair, validate_public_key},
        KEY_GENERATION_SEED_SIZE,
    };

    #[test]
    fn pk_validation() {
        let mut randomness = [0u8; KEY_GENERATION_SEED_SIZE];
        OsRng.fill_bytes(&mut randomness);

        let key_pair = generate_key_pair(randomness);
        assert!(validate_public_key(key_pair.pk).is_some());
    }
}
