macro_rules! instantiate {
    ($modp:ident, $vector:path, $hash:path) => {
        pub mod $modp {
            use crate::{
                MlKemCiphertext, MlKemKeyPair, MlKemPrivateKey, MlKemPublicKey, MlKemSharedSecret,
                KEY_GENERATION_SEED_SIZE, SHARED_SECRET_SIZE,
            };

            pub(crate) type MlKemKeyPairUnpacked<const K: usize> =
                crate::ind_cca::unpacked::MlKemKeyPairUnpacked<K, $vector>;
            pub(crate) type MlKemPublicKeyUnpacked<const K: usize> =
                crate::ind_cca::unpacked::MlKemPublicKeyUnpacked<K, $vector>;

            /// Portable generate key pair.
            pub(crate) fn generate_keypair<
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
                    $vector,
                    $hash,
                >(randomness)
            }

            /// Portable public key validation
            pub(crate) fn validate_public_key<
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
                    $vector,
                >(public_key)
            }

            /// Portable encapsulate
            #[cfg(feature = "kyber")]
            pub(crate) fn kyber_encapsulate<
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
                    $vector,
                    $hash,
                    crate::ind_cca::Kyber,
                >(public_key, randomness)
            }

            pub(crate) fn encapsulate<
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
                    $vector,
                    $hash,
                    crate::ind_cca::MlKem,
                >(public_key, randomness)
            }

            /// Portable decapsulate
            #[cfg(feature = "kyber")]
            pub fn kyber_decapsulate<
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
                    $vector,
                    $hash,
                    crate::ind_cca::Kyber,
                >(private_key, ciphertext)
            }

            /// Portable decapsulate
            pub fn decapsulate<
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
                    $vector,
                    $hash,
                    crate::ind_cca::MlKem,
                >(private_key, ciphertext)
            }

            /// Unpacked API
            pub(crate) fn generate_keypair_unpacked<
                const K: usize,
                const CPA_PRIVATE_KEY_SIZE: usize,
                const PRIVATE_KEY_SIZE: usize,
                const PUBLIC_KEY_SIZE: usize,
                const BYTES_PER_RING_ELEMENT: usize,
                const ETA1: usize,
                const ETA1_RANDOMNESS_SIZE: usize,
            >(
                randomness: [u8; KEY_GENERATION_SEED_SIZE],
            ) -> MlKemKeyPairUnpacked<K> {
                crate::ind_cca::unpacked::generate_keypair_unpacked::<
                    K,
                    CPA_PRIVATE_KEY_SIZE,
                    PRIVATE_KEY_SIZE,
                    PUBLIC_KEY_SIZE,
                    BYTES_PER_RING_ELEMENT,
                    ETA1,
                    ETA1_RANDOMNESS_SIZE,
                    $vector,
                    $hash,
                >(randomness)
            }

            /// Portable encapsualte
            pub(crate) fn encapsulate_unpacked<
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
                crate::ind_cca::unpacked::encapsulate_unpacked::<
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
                    $vector,
                    $hash,
                >(public_key, randomness)
            }

            /// Portable decapsulate
            pub fn decapsulate_unpacked<
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
                crate::ind_cca::unpacked::decapsulate_unpacked::<
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
                    $vector,
                    $hash,
                >(key_pair, ciphertext)
            }
        }
    };
}

// Portable generic implementations.
instantiate! {portable, crate::vector::portable::PortableVector, crate::hash_functions::portable::PortableHash<K>}

// AVX2 generic implementation.
#[cfg(feature = "simd256")]
instantiate! {avx2, crate::vector::SIMD256Vector, crate::hash_functions::avx2::Simd256Hash}

// NEON generic implementation.
#[cfg(feature = "simd128")]
instantiate! {neon, crate::vector::SIMD128Vector, crate::hash_functions::neon::Simd128Hash}
