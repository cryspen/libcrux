//! ML-KEM 768
//!

use super::{
    constants::*,
    ind_cca::{unpacked::*,*},
    types::*,
    vector::traits::VectorType,
    *,
};

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
pub(crate) const CPA_PKE_PUBLIC_KEY_SIZE_768: usize = T_AS_NTT_ENCODED_SIZE_768 + 32;
// These two are used in the hybrid kem. This could probably be improved.
const CPA_PKE_CIPHERTEXT_SIZE_768: usize = C1_SIZE_768 + C2_SIZE_768;
const SECRET_KEY_SIZE_768: usize =
    CPA_PKE_SECRET_KEY_SIZE_768 + CPA_PKE_PUBLIC_KEY_SIZE_768 + H_DIGEST_SIZE + SHARED_SECRET_SIZE;

const ETA1: usize = 2;
const ETA1_RANDOMNESS_SIZE: usize = ETA1 * 64;
const ETA2: usize = 2;
const ETA2_RANDOMNESS_SIZE: usize = ETA2 * 64;

const IMPLICIT_REJECTION_HASH_INPUT_SIZE: usize = SHARED_SECRET_SIZE + CPA_PKE_CIPHERTEXT_SIZE_768;

// Kyber 768 types
/// An ML-KEM 768 Ciphertext
pub type MlKem768Ciphertext = MlKemCiphertext<CPA_PKE_CIPHERTEXT_SIZE_768>;
/// An ML-KEM 768 Private key
pub type MlKem768PrivateKey = MlKemPrivateKey<SECRET_KEY_SIZE_768>;
/// An ML-KEM 768 Public key
pub type MlKem768PublicKey = MlKemPublicKey<CPA_PKE_PUBLIC_KEY_SIZE_768>;
/// An ML-KEM 768 Key pair
pub type MlKem768KeyPair = MlKemKeyPair<SECRET_KEY_SIZE_768, CPA_PKE_PUBLIC_KEY_SIZE_768>;

/// An Unpacked ML-KEM 768 Public key
#[allow(type_alias_bounds)]
pub type MlKem768PublicKeyUnpacked<Vector: VectorType> = MlKemPublicKeyUnpacked<RANK_768, Vector>;
/// Am Unpacked ML-KEM 768 Key pair
#[allow(type_alias_bounds)]
pub type MlKem768KeyPairUnpacked<Vector: VectorType> = MlKemKeyPairUnpacked<RANK_768, Vector>;

// Instantiate the different functions.
macro_rules! instantiate {
    ($modp:ident, $p:path, $vec:path, $doc:expr) => {
        #[doc = $doc]
        pub mod $modp {
            use super::*;
            use $p as p;

            /// Validate a public key.
            ///
            /// Returns `Some(public_key)` if valid, and `None` otherwise.
            pub fn validate_public_key(public_key: MlKem768PublicKey) -> Option<MlKem768PublicKey> {
                if p::validate_public_key::<
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
            ) -> MlKem768KeyPair {
                p::generate_keypair::<
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
            ///
            /// Generates an ([`MlKem768Ciphertext`], [`MlKemSharedSecret`]) tuple.
            /// The input is a reference to an [`MlKem768PublicKey`] and [`SHARED_SECRET_SIZE`]
            /// bytes of `randomness`.
            pub fn encapsulate(
                public_key: &MlKem768PublicKey,
                randomness: [u8; SHARED_SECRET_SIZE],
            ) -> (MlKem768Ciphertext, MlKemSharedSecret) {
                p::encapsulate::<
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

            /// Encapsulate Kyber 768
            ///
            /// Generates an ([`MlKem768Ciphertext`], [`MlKemSharedSecret`]) tuple.
            /// The input is a reference to an [`MlKem768PublicKey`] and [`SHARED_SECRET_SIZE`]
            /// bytes of `randomness`.
            #[cfg(feature = "kyber")]
            pub fn kyber_encapsulate(
                public_key: &MlKem768PublicKey,
                randomness: [u8; SHARED_SECRET_SIZE],
            ) -> (MlKem768Ciphertext, MlKemSharedSecret) {
                p::kyber_encapsulate::<
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
            ///
            /// Generates an [`MlKemSharedSecret`].
            /// The input is a reference to an [`MlKem768PrivateKey`] and an [`MlKem768Ciphertext`].
            pub fn decapsulate(
                private_key: &MlKem768PrivateKey,
                ciphertext: &MlKem768Ciphertext,
            ) -> MlKemSharedSecret {
                p::decapsulate::<
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
                >(private_key, ciphertext)
            }

            /// Decapsulate Kyber 768
            ///
            /// Generates an [`MlKemSharedSecret`].
            /// The input is a reference to an [`MlKem768PrivateKey`] and an [`MlKem768Ciphertext`].
            #[cfg(feature = "kyber")]
            pub fn kyber_decapsulate(
                private_key: &MlKem768PrivateKey,
                ciphertext: &MlKem768Ciphertext,
            ) -> MlKemSharedSecret {
                p::kyber_decapsulate::<
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
                >(private_key, ciphertext)
            }

            /// Generate ML-KEM 768 Key Pair in "unpacked" form
            pub fn generate_key_pair_unpacked(
                randomness: [u8; KEY_GENERATION_SEED_SIZE],
            ) -> MlKem768KeyPairUnpacked<$vec> {
                p::generate_keypair_unpacked::<
                    RANK_768,
                    CPA_PKE_SECRET_KEY_SIZE_768,
                    SECRET_KEY_SIZE_768,
                    CPA_PKE_PUBLIC_KEY_SIZE_768,
                    RANKED_BYTES_PER_RING_ELEMENT_768,
                    ETA1,
                    ETA1_RANDOMNESS_SIZE,
                >(randomness)
            }

            /// Encapsulate ML-KEM 768 (unpacked)
            ///
            /// Generates an ([`MlKem768Ciphertext`], [`MlKemSharedSecret`]) tuple.
            /// The input is a reference to an unpacked public key of type [`MlKem768PublicKeyUnpacked`],
            /// the SHA3-256 hash of this public key, and [`SHARED_SECRET_SIZE`] bytes of `randomness`.
            pub fn encapsulate_unpacked(
                public_key: &MlKem768PublicKeyUnpacked<$vec>,
                randomness: [u8; SHARED_SECRET_SIZE],
            ) -> (MlKem768Ciphertext, MlKemSharedSecret) {
                p::encapsulate_unpacked::<
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

            /// Decapsulate ML-KEM 768 (unpacked)
            ///
            /// Generates an [`MlKemSharedSecret`].
            /// The input is a reference to an unpacked key pair of type [`MlKem768KeyPairUnpacked`]
            /// and an [`MlKem768Ciphertext`].
            pub fn decapsulate_unpacked(
                private_key: &MlKem768KeyPairUnpacked<$vec>,
                ciphertext: &MlKem768Ciphertext,
            ) -> MlKemSharedSecret {
                p::decapsulate_unpacked::<
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
                >(private_key, ciphertext)
            }
        }
    };
}

// Instantiations

instantiate! {portable, ind_cca::instantiations::portable, vector::portable::PortableVector, "Portable ML-KEM 768"}
#[cfg(feature = "simd256")]
instantiate! {avx2, ind_cca::instantiations::avx2, vector::SIMD256Vector, "AVX2 Optimised ML-KEM 768"}
#[cfg(feature = "simd128")]
instantiate! {neon, ind_cca::instantiations::neon, vector::SIMD128Vector, "Neon Optimised ML-KEM 768"}

/// Validate a public key.
///
/// Returns `Some(public_key)` if valid, and `None` otherwise.
#[cfg(not(eurydice))]
pub fn validate_public_key(public_key: MlKem768PublicKey) -> Option<MlKem768PublicKey> {
    if multiplexing::validate_public_key::<
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
///
/// Generate an ML-KEM key pair. The input is a byte array of size
/// [`KEY_GENERATION_SEED_SIZE`].
///
/// This function returns an [`MlKem768KeyPair`].
#[cfg(not(eurydice))]
pub fn generate_key_pair(randomness: [u8; KEY_GENERATION_SEED_SIZE]) -> MlKem768KeyPair {
    multiplexing::generate_keypair::<
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
///
/// Generates an ([`MlKem768Ciphertext`], [`MlKemSharedSecret`]) tuple.
/// The input is a reference to an [`MlKem768PublicKey`] and [`SHARED_SECRET_SIZE`]
/// bytes of `randomness`.
#[cfg(not(eurydice))]
pub fn encapsulate(
    public_key: &MlKem768PublicKey,
    randomness: [u8; SHARED_SECRET_SIZE],
) -> (MlKem768Ciphertext, MlKemSharedSecret) {
    multiplexing::encapsulate::<
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
///
/// Generates an [`MlKemSharedSecret`].
/// The input is a reference to an [`MlKem768PrivateKey`] and an [`MlKem768Ciphertext`].
#[cfg(not(eurydice))]
pub fn decapsulate(
    private_key: &MlKem768PrivateKey,
    ciphertext: &MlKem768Ciphertext,
) -> MlKemSharedSecret {
    multiplexing::decapsulate::<
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
    >(private_key, ciphertext)
}

#[cfg(all(not(eurydice), feature = "kyber"))]
pub(crate) mod kyber {
    use super::*;

    /// Encapsulate Kyber 768
    ///
    /// Generates an ([`MlKem768Ciphertext`], [`MlKemSharedSecret`]) tuple.
    /// The input is a reference to an [`MlKem768PublicKey`] and [`SHARED_SECRET_SIZE`]
    /// bytes of `randomness`.
    pub fn encapsulate(
        public_key: &MlKem768PublicKey,
        randomness: [u8; SHARED_SECRET_SIZE],
    ) -> (MlKem768Ciphertext, MlKemSharedSecret) {
        multiplexing::kyber_encapsulate::<
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
    ///
    /// Generates an [`MlKemSharedSecret`].
    /// The input is a reference to an [`MlKem768PrivateKey`] and an [`MlKem768Ciphertext`].
    pub fn decapsulate(
        private_key: &MlKem768PrivateKey,
        ciphertext: &MlKem768Ciphertext,
    ) -> MlKemSharedSecret {
        multiplexing::kyber_decapsulate::<
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
        >(private_key, ciphertext)
    }
}
#[cfg(test)]
mod tests {
    use rand::{rngs::OsRng, RngCore};

    use super::{
        mlkem768::{generate_key_pair, validate_public_key},
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
