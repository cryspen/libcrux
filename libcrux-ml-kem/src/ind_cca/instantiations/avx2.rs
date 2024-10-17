use crate::{
    MlKemCiphertext, MlKemKeyPair, MlKemPrivateKey, MlKemPublicKey, MlKemSharedSecret,
    KEY_GENERATION_SEED_SIZE, SHARED_SECRET_SIZE,
};

/// Portable generate key pair.
#[target_feature(enable = "avx2")]
pub(crate) unsafe fn generate_keypair<
    const K: usize,
    const CPA_PRIVATE_KEY_SIZE: usize,
    const PRIVATE_KEY_SIZE: usize,
    const PUBLIC_KEY_SIZE: usize,
    const BYTES_PER_RING_ELEMENT: usize,
    const ETA1: usize,
    const ETA1_RANDOMNESS_SIZE: usize,
>(
    randomness: [u8; KEY_GENERATION_SEED_SIZE],
) -> MlKemKeyPair<PRIVATE_KEY_SIZE, PUBLIC_KEY_SIZE> {
    crate::ind_cca::generate_keypair::<
        K,
        CPA_PRIVATE_KEY_SIZE,
        PRIVATE_KEY_SIZE,
        PUBLIC_KEY_SIZE,
        BYTES_PER_RING_ELEMENT,
        ETA1,
        ETA1_RANDOMNESS_SIZE,
        crate::vector::SIMD256Vector,
        crate::hash_functions::avx2::Simd256Hash,
        crate::variant::MlKem,
    >(randomness)
}

#[cfg(feature = "kyber")]
#[target_feature(enable = "avx2")]
pub(crate) unsafe fn kyber_generate_keypair<
    const K: usize,
    const CPA_PRIVATE_KEY_SIZE: usize,
    const PRIVATE_KEY_SIZE: usize,
    const PUBLIC_KEY_SIZE: usize,
    const BYTES_PER_RING_ELEMENT: usize,
    const ETA1: usize,
    const ETA1_RANDOMNESS_SIZE: usize,
>(
    randomness: [u8; KEY_GENERATION_SEED_SIZE],
) -> MlKemKeyPair<PRIVATE_KEY_SIZE, PUBLIC_KEY_SIZE> {
    crate::ind_cca::generate_keypair::<
        K,
        CPA_PRIVATE_KEY_SIZE,
        PRIVATE_KEY_SIZE,
        PUBLIC_KEY_SIZE,
        BYTES_PER_RING_ELEMENT,
        ETA1,
        ETA1_RANDOMNESS_SIZE,
        crate::vector::SIMD256Vector,
        crate::hash_functions::avx2::Simd256Hash,
        crate::variant::Kyber,
    >(randomness)
}

/// Portable public key validation
#[target_feature(enable = "avx2")]
pub(crate) unsafe fn validate_public_key<
    const K: usize,
    const RANKED_BYTES_PER_RING_ELEMENT: usize,
    const PUBLIC_KEY_SIZE: usize,
>(
    public_key: &[u8; PUBLIC_KEY_SIZE],
) -> bool {
    crate::ind_cca::validate_public_key::<
        K,
        RANKED_BYTES_PER_RING_ELEMENT,
        PUBLIC_KEY_SIZE,
        crate::vector::SIMD256Vector,
    >(public_key)
}

/// Portable private key validation
#[target_feature(enable = "avx2")]
pub(crate) unsafe fn validate_private_key<
    const K: usize,
    const SECRET_KEY_SIZE: usize,
    const CIPHERTEXT_SIZE: usize,
>(
    private_key: &MlKemPrivateKey<SECRET_KEY_SIZE>,
    ciphertext: &MlKemCiphertext<CIPHERTEXT_SIZE>,
) -> bool {
    crate::ind_cca::validate_private_key::<
        K,
        SECRET_KEY_SIZE,
        CIPHERTEXT_SIZE,
        crate::hash_functions::avx2::Simd256Hash,
    >(private_key, ciphertext)
}

/// Portable encapsulate
#[cfg(feature = "kyber")]
#[target_feature(enable = "avx2")]
pub(crate) unsafe fn kyber_encapsulate<
    const K: usize,
    const CIPHERTEXT_SIZE: usize,
    const PUBLIC_KEY_SIZE: usize,
    const T_AS_NTT_ENCODED_SIZE: usize,
    const C1_SIZE: usize,
    const C2_SIZE: usize,
    const VECTOR_U_COMPRESSION_FACTOR: usize,
    const VECTOR_V_COMPRESSION_FACTOR: usize,
    const VECTOR_U_BLOCK_LEN: usize,
    const ETA1: usize,
    const ETA1_RANDOMNESS_SIZE: usize,
    const ETA2: usize,
    const ETA2_RANDOMNESS_SIZE: usize,
>(
    public_key: &MlKemPublicKey<PUBLIC_KEY_SIZE>,
    randomness: [u8; SHARED_SECRET_SIZE],
) -> (MlKemCiphertext<CIPHERTEXT_SIZE>, MlKemSharedSecret) {
    crate::ind_cca::encapsulate::<
        K,
        CIPHERTEXT_SIZE,
        PUBLIC_KEY_SIZE,
        T_AS_NTT_ENCODED_SIZE,
        C1_SIZE,
        C2_SIZE,
        VECTOR_U_COMPRESSION_FACTOR,
        VECTOR_V_COMPRESSION_FACTOR,
        VECTOR_U_BLOCK_LEN,
        ETA1,
        ETA1_RANDOMNESS_SIZE,
        ETA2,
        ETA2_RANDOMNESS_SIZE,
        crate::vector::SIMD256Vector,
        crate::hash_functions::avx2::Simd256Hash,
        crate::variant::Kyber,
    >(public_key, randomness)
}

#[target_feature(enable = "avx2")]
pub(crate) unsafe fn encapsulate<
    const K: usize,
    const CIPHERTEXT_SIZE: usize,
    const PUBLIC_KEY_SIZE: usize,
    const T_AS_NTT_ENCODED_SIZE: usize,
    const C1_SIZE: usize,
    const C2_SIZE: usize,
    const VECTOR_U_COMPRESSION_FACTOR: usize,
    const VECTOR_V_COMPRESSION_FACTOR: usize,
    const VECTOR_U_BLOCK_LEN: usize,
    const ETA1: usize,
    const ETA1_RANDOMNESS_SIZE: usize,
    const ETA2: usize,
    const ETA2_RANDOMNESS_SIZE: usize,
>(
    public_key: &MlKemPublicKey<PUBLIC_KEY_SIZE>,
    randomness: [u8; SHARED_SECRET_SIZE],
) -> (MlKemCiphertext<CIPHERTEXT_SIZE>, MlKemSharedSecret) {
    crate::ind_cca::encapsulate::<
        K,
        CIPHERTEXT_SIZE,
        PUBLIC_KEY_SIZE,
        T_AS_NTT_ENCODED_SIZE,
        C1_SIZE,
        C2_SIZE,
        VECTOR_U_COMPRESSION_FACTOR,
        VECTOR_V_COMPRESSION_FACTOR,
        VECTOR_U_BLOCK_LEN,
        ETA1,
        ETA1_RANDOMNESS_SIZE,
        ETA2,
        ETA2_RANDOMNESS_SIZE,
        crate::vector::SIMD256Vector,
        crate::hash_functions::avx2::Simd256Hash,
        crate::variant::MlKem,
    >(public_key, randomness)
}

/// Portable decapsulate
#[cfg(feature = "kyber")]
#[target_feature(enable = "avx2")]
pub unsafe fn kyber_decapsulate<
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
>(
    private_key: &MlKemPrivateKey<SECRET_KEY_SIZE>,
    ciphertext: &MlKemCiphertext<CIPHERTEXT_SIZE>,
) -> MlKemSharedSecret {
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
        crate::vector::SIMD256Vector,
        crate::hash_functions::avx2::Simd256Hash,
        crate::variant::Kyber,
    >(private_key, ciphertext)
}

/// Portable decapsulate
#[target_feature(enable = "avx2")]
pub unsafe fn decapsulate<
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
>(
    private_key: &MlKemPrivateKey<SECRET_KEY_SIZE>,
    ciphertext: &MlKemCiphertext<CIPHERTEXT_SIZE>,
) -> MlKemSharedSecret {
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
        crate::vector::SIMD256Vector,
        crate::hash_functions::avx2::Simd256Hash,
        crate::variant::MlKem,
    >(private_key, ciphertext)
}

/// Unpacked API
pub(crate) mod unpacked {
    use super::*;

    pub(crate) type MlKemKeyPairUnpacked<const K: usize> =
        crate::ind_cca::unpacked::MlKemKeyPairUnpacked<K, crate::vector::SIMD256Vector>;
    pub(crate) type MlKemPublicKeyUnpacked<const K: usize> =
        crate::ind_cca::unpacked::MlKemPublicKeyUnpacked<K, crate::vector::SIMD256Vector>;

    /// Get the unpacked public key.
    #[target_feature(enable = "avx2")]
    pub(crate) unsafe fn unpack_public_key<
        const K: usize,
        const T_AS_NTT_ENCODED_SIZE: usize,
        const RANKED_BYTES_PER_RING_ELEMENT: usize,
        const PUBLIC_KEY_SIZE: usize,
    >(
        public_key: &MlKemPublicKey<PUBLIC_KEY_SIZE>,
        unpacked_public_key: &mut MlKemPublicKeyUnpacked<K>,
    ) {
        crate::ind_cca::unpacked::unpack_public_key::<
            K,
            T_AS_NTT_ENCODED_SIZE,
            RANKED_BYTES_PER_RING_ELEMENT,
            PUBLIC_KEY_SIZE,
            crate::hash_functions::avx2::Simd256Hash,
            crate::vector::SIMD256Vector,
        >(public_key, unpacked_public_key)
    }

    /// Generate a key pair
    #[target_feature(enable = "avx2")]
    pub(crate) unsafe fn generate_keypair<
        const K: usize,
        const CPA_PRIVATE_KEY_SIZE: usize,
        const PRIVATE_KEY_SIZE: usize,
        const PUBLIC_KEY_SIZE: usize,
        const BYTES_PER_RING_ELEMENT: usize,
        const ETA1: usize,
        const ETA1_RANDOMNESS_SIZE: usize,
    >(
        randomness: [u8; KEY_GENERATION_SEED_SIZE],
        out: &mut MlKemKeyPairUnpacked<K>,
    ) {
        crate::ind_cca::unpacked::generate_keypair::<
            K,
            CPA_PRIVATE_KEY_SIZE,
            PRIVATE_KEY_SIZE,
            PUBLIC_KEY_SIZE,
            BYTES_PER_RING_ELEMENT,
            ETA1,
            ETA1_RANDOMNESS_SIZE,
            crate::vector::SIMD256Vector,
            crate::hash_functions::avx2::Simd256Hash,
            crate::variant::MlKem,
        >(randomness, out)
    }

    /// Unpacked encapsulate
    #[target_feature(enable = "avx2")]
    pub(crate) unsafe fn encapsulate<
        const K: usize,
        const CIPHERTEXT_SIZE: usize,
        const PUBLIC_KEY_SIZE: usize,
        const T_AS_NTT_ENCODED_SIZE: usize,
        const C1_SIZE: usize,
        const C2_SIZE: usize,
        const VECTOR_U_COMPRESSION_FACTOR: usize,
        const VECTOR_V_COMPRESSION_FACTOR: usize,
        const VECTOR_U_BLOCK_LEN: usize,
        const ETA1: usize,
        const ETA1_RANDOMNESS_SIZE: usize,
        const ETA2: usize,
        const ETA2_RANDOMNESS_SIZE: usize,
    >(
        public_key: &MlKemPublicKeyUnpacked<K>,
        randomness: [u8; SHARED_SECRET_SIZE],
    ) -> (MlKemCiphertext<CIPHERTEXT_SIZE>, MlKemSharedSecret) {
        crate::ind_cca::unpacked::encapsulate::<
            K,
            CIPHERTEXT_SIZE,
            PUBLIC_KEY_SIZE,
            T_AS_NTT_ENCODED_SIZE,
            C1_SIZE,
            C2_SIZE,
            VECTOR_U_COMPRESSION_FACTOR,
            VECTOR_V_COMPRESSION_FACTOR,
            VECTOR_U_BLOCK_LEN,
            ETA1,
            ETA1_RANDOMNESS_SIZE,
            ETA2,
            ETA2_RANDOMNESS_SIZE,
            crate::vector::SIMD256Vector,
            crate::hash_functions::avx2::Simd256Hash,
        >(public_key, randomness)
    }

    /// Unpacked decapsulate
    #[target_feature(enable = "avx2")]
    pub(crate) unsafe fn decapsulate<
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
    >(
        key_pair: &MlKemKeyPairUnpacked<K>,
        ciphertext: &MlKemCiphertext<CIPHERTEXT_SIZE>,
    ) -> MlKemSharedSecret {
        crate::ind_cca::unpacked::decapsulate::<
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
            crate::vector::SIMD256Vector,
            crate::hash_functions::avx2::Simd256Hash,
        >(key_pair, ciphertext)
    }
}
