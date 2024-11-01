macro_rules! instantiate {
    ($modp:ident, $vector:path, $hash:path) => {
        pub mod $modp {
            use crate::{
                MlKemCiphertext, MlKemKeyPair, MlKemPrivateKey, MlKemPublicKey, MlKemSharedSecret,
                KEY_GENERATION_SEED_SIZE, SHARED_SECRET_SIZE,
            };

            /// Portable generate key pair.
            #[hax_lib::requires(fstar!("Spec.MLKEM.is_rank $K /\\
                $CPA_PRIVATE_KEY_SIZE == Spec.MLKEM.v_CPA_PRIVATE_KEY_SIZE $K /\\
                $PRIVATE_KEY_SIZE == Spec.MLKEM.v_CCA_PRIVATE_KEY_SIZE $K /\\
                $PUBLIC_KEY_SIZE == Spec.MLKEM.v_CPA_PUBLIC_KEY_SIZE $K /\\
                $RANKED_BYTES_PER_RING_ELEMENT == Spec.MLKEM.v_RANKED_BYTES_PER_RING_ELEMENT $K /\\
                $ETA1 == Spec.MLKEM.v_ETA1 $K /\\
                $ETA1_RANDOMNESS_SIZE == Spec.MLKEM.v_ETA1_RANDOMNESS_SIZE $K"))]
            pub(crate) fn generate_keypair<
                const K: usize,
                const CPA_PRIVATE_KEY_SIZE: usize,
                const PRIVATE_KEY_SIZE: usize,
                const PUBLIC_KEY_SIZE: usize,
                const RANKED_BYTES_PER_RING_ELEMENT: usize,
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
                    RANKED_BYTES_PER_RING_ELEMENT,
                    ETA1,
                    ETA1_RANDOMNESS_SIZE,
                    $vector,
                    $hash,
                    crate::variant::MlKem,
                >(randomness)
            }

            #[cfg(feature = "kyber")]
            pub(crate) fn kyber_generate_keypair<
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
                    crate::variant::Kyber,
                >(randomness)
            }

            /// Portable public key validation
            #[hax_lib::requires(fstar!("Spec.MLKEM.is_rank $K /\\
                $RANKED_BYTES_PER_RING_ELEMENT == Spec.MLKEM.v_RANKED_BYTES_PER_RING_ELEMENT $K /\\
                $PUBLIC_KEY_SIZE == Spec.MLKEM.v_CCA_PUBLIC_KEY_SIZE $K"))]
            #[inline(always)]
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

            /// Portable private key validation
            #[inline(always)]
            #[hax_lib::requires(fstar!("Spec.MLKEM.is_rank $K /\\
                $SECRET_KEY_SIZE == Spec.MLKEM.v_CCA_PRIVATE_KEY_SIZE $K /\\
                $CIPHERTEXT_SIZE == Spec.MLKEM.v_CPA_CIPHERTEXT_SIZE $K"))]
            pub(crate) fn validate_private_key<
                const K: usize,
                const SECRET_KEY_SIZE: usize,
                const CIPHERTEXT_SIZE: usize,
            >(
                private_key: &MlKemPrivateKey<SECRET_KEY_SIZE>,
                ciphertext: &MlKemCiphertext<CIPHERTEXT_SIZE>,
            ) -> bool {
                crate::ind_cca::validate_private_key::<K, SECRET_KEY_SIZE, CIPHERTEXT_SIZE, $hash>(
                    private_key,
                    ciphertext,
                )
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
                    crate::variant::Kyber,
                >(public_key, randomness)
            }

            #[hax_lib::requires(fstar!("Spec.MLKEM.is_rank $K /\\
                $CIPHERTEXT_SIZE == Spec.MLKEM.v_CPA_CIPHERTEXT_SIZE $K /\\
                $PUBLIC_KEY_SIZE == Spec.MLKEM.v_CPA_PUBLIC_KEY_SIZE $K /\\
                $T_AS_NTT_ENCODED_SIZE == Spec.MLKEM.v_T_AS_NTT_ENCODED_SIZE $K /\\
                $C1_SIZE == Spec.MLKEM.v_C1_SIZE $K /\\
                $C2_SIZE == Spec.MLKEM.v_C2_SIZE $K /\\
                $VECTOR_U_COMPRESSION_FACTOR == Spec.MLKEM.v_VECTOR_U_COMPRESSION_FACTOR  $K /\\
                $VECTOR_V_COMPRESSION_FACTOR == Spec.MLKEM.v_VECTOR_V_COMPRESSION_FACTOR  $K /\\
                $C1_BLOCK_SIZE == Spec.MLKEM.v_C1_BLOCK_SIZE $K /\\
                $ETA1 == Spec.MLKEM.v_ETA1 $K /\\
                $ETA1_RANDOMNESS_SIZE == Spec.MLKEM.v_ETA1_RANDOMNESS_SIZE $K /\\
                $ETA2 == Spec.MLKEM.v_ETA2 $K /\\
                $ETA2_RANDOMNESS_SIZE == Spec.MLKEM.v_ETA2_RANDOMNESS_SIZE $K"))]
            pub(crate) fn encapsulate<
                const K: usize,
                const CIPHERTEXT_SIZE: usize,
                const PUBLIC_KEY_SIZE: usize,
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
                    C1_BLOCK_SIZE,
                    ETA1,
                    ETA1_RANDOMNESS_SIZE,
                    ETA2,
                    ETA2_RANDOMNESS_SIZE,
                    $vector,
                    $hash,
                    crate::variant::MlKem,
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
                    crate::variant::Kyber,
                >(private_key, ciphertext)
            }

            /// Portable decapsulate
            #[hax_lib::requires(fstar!("Spec.MLKEM.is_rank $K /\\
                $SECRET_KEY_SIZE == Spec.MLKEM.v_CCA_PRIVATE_KEY_SIZE $K /\\
                $CPA_SECRET_KEY_SIZE == Spec.MLKEM.v_CPA_PRIVATE_KEY_SIZE $K /\\
                $PUBLIC_KEY_SIZE == Spec.MLKEM.v_CPA_PUBLIC_KEY_SIZE $K /\\
                $CIPHERTEXT_SIZE == Spec.MLKEM.v_CPA_CIPHERTEXT_SIZE $K /\\
            
                $T_AS_NTT_ENCODED_SIZE == Spec.MLKEM.v_T_AS_NTT_ENCODED_SIZE $K /\\
                $C1_SIZE == Spec.MLKEM.v_C1_SIZE $K /\\
                $C2_SIZE == Spec.MLKEM.v_C2_SIZE $K /\\
                $VECTOR_U_COMPRESSION_FACTOR == Spec.MLKEM.v_VECTOR_U_COMPRESSION_FACTOR  $K /\\
                $VECTOR_V_COMPRESSION_FACTOR == Spec.MLKEM.v_VECTOR_V_COMPRESSION_FACTOR  $K /\\
                $C1_BLOCK_SIZE == Spec.MLKEM.v_C1_BLOCK_SIZE $K /\\
                $ETA1 == Spec.MLKEM.v_ETA1 $K /\\
                $ETA1_RANDOMNESS_SIZE == Spec.MLKEM.v_ETA1_RANDOMNESS_SIZE $K /\\
                $ETA2 == Spec.MLKEM.v_ETA2 $K /\\
                $ETA2_RANDOMNESS_SIZE == Spec.MLKEM.v_ETA2_RANDOMNESS_SIZE $K /\\
                $IMPLICIT_REJECTION_HASH_INPUT_SIZE == Spec.MLKEM.v_IMPLICIT_REJECTION_HASH_INPUT_SIZE $K"))]
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
                    crate::variant::MlKem,
                >(private_key, ciphertext)
            }

            /// Unpacked API
            pub(crate) mod unpacked {
                use super::*;

                pub(crate) type MlKemKeyPairUnpacked<const K: usize> =
                    crate::ind_cca::unpacked::MlKemKeyPairUnpacked<K, $vector>;
                pub(crate) type MlKemPublicKeyUnpacked<const K: usize> =
                    crate::ind_cca::unpacked::MlKemPublicKeyUnpacked<K, $vector>;

                /// Get the unpacked public key.
                pub(crate) fn unpack_public_key<
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
                        $hash,
                        $vector,
                    >(public_key, unpacked_public_key)
                }

                /// Generate a key pair
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
                        $vector,
                        $hash,
                        crate::variant::MlKem,
                    >(randomness, out)
                }

                /// Unpacked encapsulate
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
                        $vector,
                        $hash,
                    >(public_key, randomness)
                }

                /// Unpacked decapsulate
                pub(crate) fn decapsulate<
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
                        $vector,
                        $hash,
                    >(key_pair, ciphertext)
                }
            }
        }
    };
}

// Portable generic implementations.
instantiate! {portable, crate::vector::portable::PortableVector, crate::hash_functions::portable::PortableHash<K>}

// AVX2 generic implementation.
#[cfg(feature = "simd256")]
pub mod avx2;

// NEON generic implementation.
#[cfg(feature = "simd128")]
instantiate! {neon, crate::vector::SIMD128Vector, crate::hash_functions::neon::Simd128Hash}
