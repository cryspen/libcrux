//! ML-KEM 512
use super::{constants::*, ind_cca::*, types::*, *};

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
pub(crate) const CPA_PKE_PUBLIC_KEY_SIZE_512: usize = T_AS_NTT_ENCODED_SIZE_512 + 32;
const CPA_PKE_CIPHERTEXT_SIZE_512: usize = C1_SIZE_512 + C2_SIZE_512;
pub(crate) const SECRET_KEY_SIZE_512: usize =
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
/// An ML-KEM 512 Key pair
pub type MlKem512KeyPair = MlKemKeyPair<SECRET_KEY_SIZE_512, CPA_PKE_PUBLIC_KEY_SIZE_512>;

// Instantiate the different functions.
macro_rules! instantiate {
    ($modp:ident, $p:path, $vec:path, $doc:expr) => {
        #[doc = $doc]
        pub mod $modp {
            use super::*;
            use $p as p;

            /// Validate a public key.
            ///
            /// Returns `true` if valid, and `false` otherwise.
            pub fn validate_public_key(public_key: &MlKem512PublicKey) -> bool {
                p::validate_public_key::<
                    RANK_512,
                    RANKED_BYTES_PER_RING_ELEMENT_512,
                    CPA_PKE_PUBLIC_KEY_SIZE_512,
                >(&public_key.value)
            }

            /// Validate a private key.
            ///
            /// Returns `true` if valid, and `false` otherwise.
            pub fn validate_private_key(
                private_key: &MlKem512PrivateKey,
                ciphertext: &MlKem512Ciphertext,
            ) -> bool {
                p::validate_private_key::<
                    RANK_512,
                    SECRET_KEY_SIZE_512,
                    CPA_PKE_CIPHERTEXT_SIZE_512,
                >(private_key, ciphertext)
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

            /// Generate Kyber 512 Key Pair
            #[cfg(feature = "kyber")]
            #[cfg_attr(docsrs, doc(cfg(feature = "kyber")))]
            pub fn kyber_generate_key_pair(
                randomness: [u8; KEY_GENERATION_SEED_SIZE],
            ) -> MlKem512KeyPair {
                p::kyber_generate_keypair::<
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

            /// Encapsulate Kyber 512
            ///
            /// Generates an ([`MlKem512Ciphertext`], [`MlKemSharedSecret`]) tuple.
            /// The input is a reference to an [`MlKem512PublicKey`] and [`SHARED_SECRET_SIZE`]
            /// bytes of `randomness`.
            #[cfg(feature = "kyber")]
            #[cfg_attr(docsrs, doc(cfg(feature = "kyber")))]
            pub fn kyber_encapsulate(
                public_key: &MlKem512PublicKey,
                randomness: [u8; SHARED_SECRET_SIZE],
            ) -> (MlKem512Ciphertext, MlKemSharedSecret) {
                p::kyber_encapsulate::<
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

            /// Decapsulate Kyber 512
            ///
            /// Generates an [`MlKemSharedSecret`].
            /// The input is a reference to an [`MlKem512PrivateKey`] and an [`MlKem512Ciphertext`].
            #[cfg(feature = "kyber")]
            #[cfg_attr(docsrs, doc(cfg(feature = "kyber")))]
            pub fn kyber_decapsulate(
                private_key: &MlKem512PrivateKey,
                ciphertext: &MlKem512Ciphertext,
            ) -> MlKemSharedSecret {
                p::kyber_decapsulate::<
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


            /// Unpacked APIs that don't use serialized keys.
            pub mod unpacked {
                use super::*;

                /// An Unpacked ML-KEM 512 Public key
                pub type MlKem512PublicKeyUnpacked = p::unpacked::MlKemPublicKeyUnpacked<RANK_512>;

                /// Am Unpacked ML-KEM 512 Key pair
                pub type MlKem512KeyPairUnpacked = p::unpacked::MlKemKeyPairUnpacked<RANK_512>;

                /// Create a new, empty unpacked key.
                pub fn init_key_pair() -> MlKem512KeyPairUnpacked {
                    MlKem512KeyPairUnpacked::default()
                }

                /// Create a new, empty unpacked public key.
                pub fn init_public_key() -> MlKem512PublicKeyUnpacked {
                    MlKem512PublicKeyUnpacked::default()
                }

                /// Get the serialized public key.
                pub fn serialized_public_key(
                    public_key: &MlKem512PublicKeyUnpacked,
                    serialized: &mut MlKem512PublicKey
                ) {
                    public_key.serialized_public_key_mut::<
                        RANKED_BYTES_PER_RING_ELEMENT_512,
                        CPA_PKE_PUBLIC_KEY_SIZE_512
                    >(serialized)
                }

                /// Get the unpacked public key.
                pub fn unpacked_public_key(
                    public_key: &MlKem512PublicKey,
                    unpacked_public_key: &mut MlKem512PublicKeyUnpacked ,
                ) {
                    p::unpacked::unpack_public_key::<
                        RANK_512,
                        T_AS_NTT_ENCODED_SIZE_512,
                        RANKED_BYTES_PER_RING_ELEMENT_512,
                        CPA_PKE_PUBLIC_KEY_SIZE_512,
                    >(public_key, unpacked_public_key)
                }

                /// Generate ML-KEM 512 Key Pair in "unpacked" form
                pub fn generate_key_pair(
                    randomness: [u8; KEY_GENERATION_SEED_SIZE],
                    key_pair: &mut MlKem512KeyPairUnpacked,
                ) {
                    p::unpacked::generate_keypair::<
                        RANK_512,
                        CPA_PKE_SECRET_KEY_SIZE_512,
                        SECRET_KEY_SIZE_512,
                        CPA_PKE_PUBLIC_KEY_SIZE_512,
                        RANKED_BYTES_PER_RING_ELEMENT_512,
                        ETA1,
                        ETA1_RANDOMNESS_SIZE,
                    >(randomness, key_pair);
                }

                /// Encapsulate ML-KEM 512 (unpacked)
                ///
                /// Generates an ([`MlKem512Ciphertext`], [`MlKemSharedSecret`]) tuple.
                /// The input is a reference to an unpacked public key of type [`MlKem512PublicKeyUnpacked`],
                /// the SHA3-256 hash of this public key, and [`SHARED_SECRET_SIZE`] bytes of `randomness`.
                #[cfg_attr(
                    hax,
                    hax_lib::fstar::before(
                        interface,
                        "
    let _ =
        (* This module has implicit dependencies, here we make them explicit. *)
        (* The implicit dependencies arise from typeclasses instances. *)
        let open Libcrux_ml_kem.Vector.Portable in
        let open Libcrux_ml_kem.Vector.Neon in
        ()"
                    )
                )]
                pub fn encapsulate(
                    public_key: &MlKem512PublicKeyUnpacked,
                    randomness: [u8; SHARED_SECRET_SIZE],
                ) -> (MlKem512Ciphertext, MlKemSharedSecret) {
                    p::unpacked::encapsulate::<
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

                /// Decapsulate ML-KEM 512 (unpacked)
                ///
                /// Generates an [`MlKemSharedSecret`].
                /// The input is a reference to an unpacked key pair of type [`MlKem512KeyPairUnpacked`]
                /// and an [`MlKem512Ciphertext`].
                pub fn decapsulate(
                    private_key: &MlKem512KeyPairUnpacked,
                    ciphertext: &MlKem512Ciphertext,
                ) -> MlKemSharedSecret {
                    p::unpacked::decapsulate::<
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
        }
    };
}

// Instantiations

instantiate! {portable, ind_cca::instantiations::portable, vector::portable::PortableVector, "Portable ML-KEM 512"}
#[cfg(feature = "simd256")]
instantiate! {avx2, ind_cca::instantiations::avx2, vector::SIMD256Vector, "AVX2 Optimised ML-KEM 512"}
#[cfg(feature = "simd128")]
instantiate! {neon, ind_cca::instantiations::neon, vector::SIMD128Vector, "Neon Optimised ML-KEM 512"}

/// Validate a public key.
///
/// Returns `true` if valid, and `false` otherwise.
#[cfg(not(eurydice))]
pub fn validate_public_key(public_key: &MlKem512PublicKey) -> bool {
    multiplexing::validate_public_key::<
        RANK_512,
        RANKED_BYTES_PER_RING_ELEMENT_512,
        CPA_PKE_PUBLIC_KEY_SIZE_512,
    >(&public_key.value)
}

/// Validate a private key.
///
/// Returns `true` if valid, and `false` otherwise.
#[cfg(not(eurydice))]
pub fn validate_private_key(
    private_key: &MlKem512PrivateKey,
    ciphertext: &MlKem512Ciphertext,
) -> bool {
    multiplexing::validate_private_key::<RANK_512, SECRET_KEY_SIZE_512, CPA_PKE_CIPHERTEXT_SIZE_512>(
        private_key,
        ciphertext,
    )
}

/// Generate ML-KEM 512 Key Pair
///
/// The input is a byte array of size
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

/// Randomized APIs
///
/// The functions in this module are equivalent to the one in the main module,
/// but sample their own randomness, provided a random number generator that
/// implements `RngCore` and `CryptoRng`.
///
/// Decapsulation is not provided in this module as it does not require randomness.
#[cfg(all(not(eurydice), feature = "rand"))]
pub mod rand {
    use super::{
        MlKem512Ciphertext, MlKem512KeyPair, MlKem512PublicKey, MlKemSharedSecret,
        KEY_GENERATION_SEED_SIZE, SHARED_SECRET_SIZE,
    };
    use ::rand::{CryptoRng, RngCore};

    /// Generate ML-KEM 512 Key Pair
    ///
    /// The random number generator `rng` needs to implement `RngCore` and
    /// `CryptoRng` to sample the required randomness internally.
    ///
    /// This function returns an [`MlKem512KeyPair`].
    pub fn generate_key_pair(rng: &mut (impl RngCore + CryptoRng)) -> MlKem512KeyPair {
        let mut randomness = [0u8; KEY_GENERATION_SEED_SIZE];
        rng.fill_bytes(&mut randomness);

        super::generate_key_pair(randomness)
    }

    /// Encapsulate ML-KEM 512
    ///
    /// Generates an ([`MlKem512Ciphertext`], [`MlKemSharedSecret`]) tuple.
    /// The input is a reference to an [`MlKem512PublicKey`].
    /// The random number generator `rng` needs to implement `RngCore` and
    /// `CryptoRng` to sample the required randomness internally.
    pub fn encapsulate(
        public_key: &MlKem512PublicKey,
        rng: &mut (impl RngCore + CryptoRng),
    ) -> (MlKem512Ciphertext, MlKemSharedSecret) {
        let mut randomness = [0u8; SHARED_SECRET_SIZE];
        rng.fill_bytes(&mut randomness);

        super::encapsulate(public_key, randomness)
    }
}

#[cfg(all(not(eurydice), feature = "kyber"))]
pub(crate) mod kyber {
    use super::*;

    /// Generate Kyber 512 Key Pair
    ///
    /// The input is a byte array of size
    /// [`KEY_GENERATION_SEED_SIZE`].
    ///
    /// This function returns an [`MlKem512KeyPair`].
    pub fn generate_key_pair(randomness: [u8; KEY_GENERATION_SEED_SIZE]) -> MlKem512KeyPair {
        multiplexing::kyber_generate_keypair::<
            RANK_512,
            CPA_PKE_SECRET_KEY_SIZE_512,
            SECRET_KEY_SIZE_512,
            CPA_PKE_PUBLIC_KEY_SIZE_512,
            RANKED_BYTES_PER_RING_ELEMENT_512,
            ETA1,
            ETA1_RANDOMNESS_SIZE,
        >(randomness)
    }

    /// Encapsulate Kyber 512
    ///
    /// Generates an ([`MlKem512Ciphertext`], [`MlKemSharedSecret`]) tuple.
    /// The input is a reference to an [`MlKem512PublicKey`] and [`SHARED_SECRET_SIZE`]
    /// bytes of `randomness`.
    pub fn encapsulate(
        public_key: &MlKem512PublicKey,
        randomness: [u8; SHARED_SECRET_SIZE],
    ) -> (MlKem512Ciphertext, MlKemSharedSecret) {
        multiplexing::kyber_encapsulate::<
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

    /// Decapsulate Kyber 512
    ///
    /// Generates an [`MlKemSharedSecret`].
    /// The input is a reference to an [`MlKem512PrivateKey`] and an [`MlKem512Ciphertext`].

    pub fn decapsulate(
        private_key: &MlKem512PrivateKey,
        ciphertext: &MlKem512Ciphertext,
    ) -> MlKemSharedSecret {
        multiplexing::kyber_decapsulate::<
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
