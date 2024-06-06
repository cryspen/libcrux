//! ML-KEM 512

use super::{constants::*, ind_cca::*, *};

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

const IMPLICIT_REJECTION_HASH_INPUT_SIZE: usize = SHARED_SECRET_SIZE + CPA_PKE_CIPHERTEXT_SIZE_512;

// Kyber 512 types
/// An ML-KEM 512 Ciphertext
pub type MlKem512Ciphertext = MlKemCiphertext<CPA_PKE_CIPHERTEXT_SIZE_512>;
/// An ML-KEM 512 Private key
pub type MlKem512PrivateKey = MlKemPrivateKey<SECRET_KEY_SIZE_512>;
/// An ML-KEM 512 Public key
pub type MlKem512PublicKey = MlKemPublicKey<CPA_PKE_PUBLIC_KEY_SIZE_512>;
/// Am ML-KEM 512 Key pair
pub type MlKem512KeyPair = MlKemKeyPair<SECRET_KEY_SIZE_512, CPA_PKE_PUBLIC_KEY_SIZE_512>;

// Instantiate the different functions.
macro_rules! instantiate {
    ($modp:ident, $p:path) => {
        pub mod $modp {
            use super::*;
            use $p as p;

            /// Validate a public key.
            ///
            /// Returns `Some(public_key)` if valid, and `None` otherwise.
            pub fn validate_public_key(public_key: MlKem512PublicKey) -> Option<MlKem512PublicKey> {
                if p::validate_public_key::<
                    RANK_512,
                    RANKED_BYTES_PER_RING_ELEMENT_512,
                    CPA_PKE_PUBLIC_KEY_SIZE_512,
                >(&public_key.value)
                {
                    Some(public_key)
                } else {
                    None
                }
            }

            /// Generate ML-KEM 512 Key Pair
            pub fn generate_key_pair(
                randomness: [u8; KEY_GENERATION_SEED_SIZE],
            ) -> MlKem512KeyPair {
                p::generate_keypair::<
                    RANK_512,
                    CPA_PKE_SECRET_KEY_SIZE_512,
                    SECRET_KEY_SIZE_512,
                    CPA_PKE_PUBLIC_KEY_SIZE_512,
                    RANKED_BYTES_PER_RING_ELEMENT_512,
                    ETA1,
                    ETA1_RANDOMNESS_SIZE,
                >(randomness)
            }

            /// Encapsulate ML-KEM 512
            ///
            /// Generates an ([`MlKem512Ciphertext`], [`MlKemSharedSecret`]) tuple.
            /// The input is a reference to an [`MlKem512PublicKey`] and [`SHARED_SECRET_SIZE`]
            /// bytes of `randomness`.
            pub fn encapsulate(
                public_key: &MlKem512PublicKey,
                randomness: [u8; SHARED_SECRET_SIZE],
            ) -> (MlKem512Ciphertext, MlKemSharedSecret) {
                p::encapsulate::<
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

            /// Decapsulate ML-KEM 512
            ///
            /// Generates an [`MlKemSharedSecret`].
            /// The input is a reference to an [`MlKem512PrivateKey`] and an [`MlKem512Ciphertext`].
            pub fn decapsulate(
                private_key: &MlKem512PrivateKey,
                ciphertext: &MlKem512Ciphertext,
            ) -> MlKemSharedSecret {
                p::decapsulate::<
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
                    IMPLICIT_REJECTION_HASH_INPUT_SIZE,
                >(private_key, ciphertext)
            }
        }
    };
}

// Instantiations

instantiate! {portable, ind_cca::instantiations::portable}
#[cfg(feature = "simd256")]
instantiate! {avx2, ind_cca::instantiations::avx2}
#[cfg(feature = "simd128")]
instantiate! {neon, ind_cca::instantiations::neon}

/// Validate a public key.
///
/// Returns `Some(public_key)` if valid, and `None` otherwise.
#[cfg(not(eurydice))]
pub fn validate_public_key(public_key: MlKem512PublicKey) -> Option<MlKem512PublicKey> {
    if multiplexing::validate_public_key::<
        RANK_512,
        RANKED_BYTES_PER_RING_ELEMENT_512,
        CPA_PKE_PUBLIC_KEY_SIZE_512,
    >(&public_key.value)
    {
        Some(public_key)
    } else {
        None
    }
}

/// Generate ML-KEM 512 Key Pair
///
/// Generate an ML-KEM key pair. The input is a byte array of size
/// [`KEY_GENERATION_SEED_SIZE`].
///
/// This function returns an [`MlKem512KeyPair`].
#[cfg(not(eurydice))]
pub fn generate_key_pair(randomness: [u8; KEY_GENERATION_SEED_SIZE]) -> MlKem512KeyPair {
    multiplexing::generate_keypair::<
        RANK_512,
        CPA_PKE_SECRET_KEY_SIZE_512,
        SECRET_KEY_SIZE_512,
        CPA_PKE_PUBLIC_KEY_SIZE_512,
        RANKED_BYTES_PER_RING_ELEMENT_512,
        ETA1,
        ETA1_RANDOMNESS_SIZE,
    >(randomness)
}

/// Encapsulate ML-KEM 512
///
/// Generates an ([`MlKem512Ciphertext`], [`MlKemSharedSecret`]) tuple.
/// The input is a reference to an [`MlKem512PublicKey`] and [`SHARED_SECRET_SIZE`]
/// bytes of `randomness`.
#[cfg(not(eurydice))]
pub fn encapsulate(
    public_key: &MlKem512PublicKey,
    randomness: [u8; SHARED_SECRET_SIZE],
) -> (MlKem512Ciphertext, MlKemSharedSecret) {
    multiplexing::encapsulate::<
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

/// Decapsulate ML-KEM 512
///
/// Generates an [`MlKemSharedSecret`].
/// The input is a reference to an [`MlKem512PrivateKey`] and an [`MlKem512Ciphertext`].
#[cfg(not(eurydice))]
pub fn decapsulate(
    private_key: &MlKem512PrivateKey,
    ciphertext: &MlKem512Ciphertext,
) -> MlKemSharedSecret {
    multiplexing::decapsulate::<
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
        IMPLICIT_REJECTION_HASH_INPUT_SIZE,
    >(private_key, ciphertext)
}
