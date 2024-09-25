//! ML-KEM 1024
use super::{constants::*, ind_cca::*, types::*, *};

// Kyber 1024 parameters
const RANK_1024: usize = 4;
const RANKED_BYTES_PER_RING_ELEMENT_1024: usize = RANK_1024 * BITS_PER_RING_ELEMENT / 8;
const T_AS_NTT_ENCODED_SIZE_1024: usize =
    (RANK_1024 * COEFFICIENTS_IN_RING_ELEMENT * BITS_PER_COEFFICIENT) / 8;
const VECTOR_U_COMPRESSION_FACTOR_1024: usize = 11;
// [hax]: hacspec/hacspec-v2#27 stealing error
// block_len::<VECTOR_U_COMPRESSION_FACTOR_1024>();
const C1_BLOCK_SIZE_1024: usize =
    (COEFFICIENTS_IN_RING_ELEMENT * VECTOR_U_COMPRESSION_FACTOR_1024) / 8;
// [hax]: hacspec/hacspec-v2#27 stealing error
// serialized_len::<RANK_1024, C1_BLOCK_SIZE_1024>();
const C1_SIZE_1024: usize = C1_BLOCK_SIZE_1024 * RANK_1024;
const VECTOR_V_COMPRESSION_FACTOR_1024: usize = 5;
// [hax]: hacspec/hacspec-v2#27 stealing error
// block_len::<VECTOR_V_COMPRESSION_FACTOR_1024>()
const C2_SIZE_1024: usize = (COEFFICIENTS_IN_RING_ELEMENT * VECTOR_V_COMPRESSION_FACTOR_1024) / 8;
const CPA_PKE_SECRET_KEY_SIZE_1024: usize =
    (RANK_1024 * COEFFICIENTS_IN_RING_ELEMENT * BITS_PER_COEFFICIENT) / 8;
pub(crate) const CPA_PKE_PUBLIC_KEY_SIZE_1024: usize = T_AS_NTT_ENCODED_SIZE_1024 + 32;
const CPA_PKE_CIPHERTEXT_SIZE_1024: usize = C1_SIZE_1024 + C2_SIZE_1024;
pub(crate) const SECRET_KEY_SIZE_1024: usize = CPA_PKE_SECRET_KEY_SIZE_1024
    + CPA_PKE_PUBLIC_KEY_SIZE_1024
    + H_DIGEST_SIZE
    + SHARED_SECRET_SIZE;

const ETA1: usize = 2;
const ETA1_RANDOMNESS_SIZE: usize = ETA1 * 64;
const ETA2: usize = 2;
const ETA2_RANDOMNESS_SIZE: usize = ETA2 * 64;

const IMPLICIT_REJECTION_HASH_INPUT_SIZE: usize = SHARED_SECRET_SIZE + CPA_PKE_CIPHERTEXT_SIZE_1024;

// Kyber 1024 types
/// An ML-KEM 1024 Ciphertext
pub type MlKem1024Ciphertext = MlKemCiphertext<CPA_PKE_CIPHERTEXT_SIZE_1024>;
/// An ML-KEM 1024 Private key
pub type MlKem1024PrivateKey = MlKemPrivateKey<SECRET_KEY_SIZE_1024>;
/// An ML-KEM 1024 Public key
pub type MlKem1024PublicKey = MlKemPublicKey<CPA_PKE_PUBLIC_KEY_SIZE_1024>;
/// An ML-KEM 1024 Key pair
pub type MlKem1024KeyPair = MlKemKeyPair<SECRET_KEY_SIZE_1024, CPA_PKE_PUBLIC_KEY_SIZE_1024>;

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
            pub fn validate_public_key(public_key: &MlKem1024PublicKey) -> bool {
                p::validate_public_key::<
                    RANK_1024,
                    RANKED_BYTES_PER_RING_ELEMENT_1024,
                    CPA_PKE_PUBLIC_KEY_SIZE_1024,
                >(&public_key.value)
            }

            /// Validate a private key.
            ///
            /// Returns `true` if valid, and `false` otherwise.
            pub fn validate_private_key(
                private_key: &MlKem1024PrivateKey,
                ciphertext: &MlKem1024Ciphertext,
            ) -> bool {
                p::validate_private_key::<
                    RANK_1024,
                    SECRET_KEY_SIZE_1024,
                    CPA_PKE_CIPHERTEXT_SIZE_1024,
                >(private_key, ciphertext)
            }

            /// Generate Kyber 1024 Key Pair
            #[cfg(feature = "kyber")]
            #[cfg_attr(docsrs, doc(cfg(feature = "kyber")))]
            pub fn kyber_generate_key_pair(
                randomness: [u8; KEY_GENERATION_SEED_SIZE],
            ) -> MlKem1024KeyPair {
                p::kyber_generate_keypair::<
                    RANK_1024,
                    CPA_PKE_SECRET_KEY_SIZE_1024,
                    SECRET_KEY_SIZE_1024,
                    CPA_PKE_PUBLIC_KEY_SIZE_1024,
                    RANKED_BYTES_PER_RING_ELEMENT_1024,
                    ETA1,
                    ETA1_RANDOMNESS_SIZE,
                >(randomness)
            }

            /// Generate ML-KEM 1024 Key Pair
            pub fn generate_key_pair(
                randomness: [u8; KEY_GENERATION_SEED_SIZE],
            ) -> MlKem1024KeyPair {
                p::generate_keypair::<
                    RANK_1024,
                    CPA_PKE_SECRET_KEY_SIZE_1024,
                    SECRET_KEY_SIZE_1024,
                    CPA_PKE_PUBLIC_KEY_SIZE_1024,
                    RANKED_BYTES_PER_RING_ELEMENT_1024,
                    ETA1,
                    ETA1_RANDOMNESS_SIZE,
                >(randomness)
            }

            /// Encapsulate ML-KEM 1024
            ///
            /// Generates an ([`MlKem1024Ciphertext`], [`MlKemSharedSecret`]) tuple.
            /// The input is a reference to an [`MlKem1024PublicKey`] and [`SHARED_SECRET_SIZE`]
            /// bytes of `randomness`.
            pub fn encapsulate(
                public_key: &MlKem1024PublicKey,
                randomness: [u8; SHARED_SECRET_SIZE],
            ) -> (MlKem1024Ciphertext, MlKemSharedSecret) {
                p::encapsulate::<
                    RANK_1024,
                    CPA_PKE_CIPHERTEXT_SIZE_1024,
                    CPA_PKE_PUBLIC_KEY_SIZE_1024,
                    T_AS_NTT_ENCODED_SIZE_1024,
                    C1_SIZE_1024,
                    C2_SIZE_1024,
                    VECTOR_U_COMPRESSION_FACTOR_1024,
                    VECTOR_V_COMPRESSION_FACTOR_1024,
                    C1_BLOCK_SIZE_1024,
                    ETA1,
                    ETA1_RANDOMNESS_SIZE,
                    ETA2,
                    ETA2_RANDOMNESS_SIZE,
                >(public_key, randomness)
            }

            /// Encapsulate Kyber 1024
            ///
            /// Generates an ([`MlKem1024Ciphertext`], [`MlKemSharedSecret`]) tuple.
            /// The input is a reference to an [`MlKem1024PublicKey`] and [`SHARED_SECRET_SIZE`]
            /// bytes of `randomness`.
            #[cfg(feature = "kyber")]
            #[cfg_attr(docsrs, doc(cfg(feature = "kyber")))]
            pub fn kyber_encapsulate(
                public_key: &MlKem1024PublicKey,
                randomness: [u8; SHARED_SECRET_SIZE],
            ) -> (MlKem1024Ciphertext, MlKemSharedSecret) {
                p::kyber_encapsulate::<
                    RANK_1024,
                    CPA_PKE_CIPHERTEXT_SIZE_1024,
                    CPA_PKE_PUBLIC_KEY_SIZE_1024,
                    T_AS_NTT_ENCODED_SIZE_1024,
                    C1_SIZE_1024,
                    C2_SIZE_1024,
                    VECTOR_U_COMPRESSION_FACTOR_1024,
                    VECTOR_V_COMPRESSION_FACTOR_1024,
                    C1_BLOCK_SIZE_1024,
                    ETA1,
                    ETA1_RANDOMNESS_SIZE,
                    ETA2,
                    ETA2_RANDOMNESS_SIZE,
                >(public_key, randomness)
            }

            /// Decapsulate ML-KEM 1024
            ///
            /// Generates an [`MlKemSharedSecret`].
            /// The input is a reference to an [`MlKem1024PrivateKey`] and an [`MlKem1024Ciphertext`].
            pub fn decapsulate(
                private_key: &MlKem1024PrivateKey,
                ciphertext: &MlKem1024Ciphertext,
            ) -> MlKemSharedSecret {
                p::decapsulate::<
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
                    ETA1,
                    ETA1_RANDOMNESS_SIZE,
                    ETA2,
                    ETA2_RANDOMNESS_SIZE,
                    IMPLICIT_REJECTION_HASH_INPUT_SIZE,
                >(private_key, ciphertext)
            }

            /// Decapsulate Kyber 1024
            ///
            /// Generates an [`MlKemSharedSecret`].
            /// The input is a reference to an [`MlKem1024PrivateKey`] and an [`MlKem1024Ciphertext`].
            #[cfg(feature = "kyber")]
            #[cfg_attr(docsrs, doc(cfg(feature = "kyber")))]
            pub fn kyber_decapsulate(
                private_key: &MlKem1024PrivateKey,
                ciphertext: &MlKem1024Ciphertext,
            ) -> MlKemSharedSecret {
                p::kyber_decapsulate::<
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

                /// An Unpacked ML-KEM 1024 Public key
                pub type MlKem1024PublicKeyUnpacked =
                    p::unpacked::MlKemPublicKeyUnpacked<RANK_1024>;

                /// Am Unpacked ML-KEM 1024 Key pair
                pub type MlKem1024KeyPairUnpacked = p::unpacked::MlKemKeyPairUnpacked<RANK_1024>;

                /// Create a new, empty unpacked key.
                pub fn init_key_pair() -> MlKem1024KeyPairUnpacked {
                    MlKem1024KeyPairUnpacked::default()
                }

                /// Create a new, empty unpacked public key.
                pub fn init_public_key() -> MlKem1024PublicKeyUnpacked {
                    MlKem1024PublicKeyUnpacked::default()
                }

                /// Get the serialized public key.
                pub fn serialized_public_key(
                    public_key: &MlKem1024PublicKeyUnpacked,
                    serialized: &mut MlKem1024PublicKey,
                ) {
                    public_key.serialized_public_key_mut::<
                        RANKED_BYTES_PER_RING_ELEMENT_1024,
                        CPA_PKE_PUBLIC_KEY_SIZE_1024,
                    >(serialized);
                }

                /// Get the unpacked public key.
                pub fn unpacked_public_key(
                    public_key: &MlKem1024PublicKey,
                    unpacked_public_key: &mut MlKem1024PublicKeyUnpacked,
                ) {
                    p::unpacked::unpack_public_key::<
                        RANK_1024,
                        T_AS_NTT_ENCODED_SIZE_1024,
                        RANKED_BYTES_PER_RING_ELEMENT_1024,
                        CPA_PKE_PUBLIC_KEY_SIZE_1024,
                    >(public_key, unpacked_public_key)
                }

                /// Generate ML-KEM 1024 Key Pair in "unpacked" form
                pub fn generate_key_pair(
                    randomness: [u8; KEY_GENERATION_SEED_SIZE],
                    key_pair: &mut MlKem1024KeyPairUnpacked,
                ) {
                    p::unpacked::generate_keypair::<
                        RANK_1024,
                        CPA_PKE_SECRET_KEY_SIZE_1024,
                        SECRET_KEY_SIZE_1024,
                        CPA_PKE_PUBLIC_KEY_SIZE_1024,
                        RANKED_BYTES_PER_RING_ELEMENT_1024,
                        ETA1,
                        ETA1_RANDOMNESS_SIZE,
                    >(randomness, key_pair)
                }

                /// Encapsulate ML-KEM 1024 (unpacked)
                ///
                /// Generates an ([`MlKem1024Ciphertext`], [`MlKemSharedSecret`]) tuple.
                /// The input is a reference to an unpacked public key of type [`MlKem1024PublicKeyUnpacked`],
                /// the SHA3-256 hash of this public key, and [`SHARED_SECRET_SIZE`] bytes of `randomness`.
                /// TODO: The F* prefix opens required modules, it should go away when the following issue is resolved:
                /// <https://github.com/hacspec/hax/issues/770>
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
                    public_key: &MlKem1024PublicKeyUnpacked,
                    randomness: [u8; SHARED_SECRET_SIZE],
                ) -> (MlKem1024Ciphertext, MlKemSharedSecret) {
                    p::unpacked::encapsulate::<
                        RANK_1024,
                        CPA_PKE_CIPHERTEXT_SIZE_1024,
                        CPA_PKE_PUBLIC_KEY_SIZE_1024,
                        T_AS_NTT_ENCODED_SIZE_1024,
                        C1_SIZE_1024,
                        C2_SIZE_1024,
                        VECTOR_U_COMPRESSION_FACTOR_1024,
                        VECTOR_V_COMPRESSION_FACTOR_1024,
                        C1_BLOCK_SIZE_1024,
                        ETA1,
                        ETA1_RANDOMNESS_SIZE,
                        ETA2,
                        ETA2_RANDOMNESS_SIZE,
                    >(public_key, randomness)
                }

                /// Decapsulate ML-KEM 1024 (unpacked)
                ///
                /// Generates an [`MlKemSharedSecret`].
                /// The input is a reference to an unpacked key pair of type [`MlKem1024KeyPairUnpacked`]
                /// and an [`MlKem1024Ciphertext`].
                pub fn decapsulate(
                    private_key: &MlKem1024KeyPairUnpacked,
                    ciphertext: &MlKem1024Ciphertext,
                ) -> MlKemSharedSecret {
                    p::unpacked::decapsulate::<
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

instantiate! {portable, ind_cca::instantiations::portable, vector::portable::PortableVector, "Portable ML-KEM 1024"}
#[cfg(feature = "simd256")]
instantiate! {avx2, ind_cca::instantiations::avx2, vector::SIMD256Vector, "AVX2 Optimised ML-KEM 1024"}
#[cfg(feature = "simd128")]
instantiate! {neon, ind_cca::instantiations::neon, vector::SIMD128Vector, "Neon Optimised ML-KEM 1024"}

/// Validate a public key.
///
/// Returns `true` if valid, and `false` otherwise.
#[cfg(not(eurydice))]
pub fn validate_public_key(public_key: &MlKem1024PublicKey) -> bool {
    multiplexing::validate_public_key::<
        RANK_1024,
        RANKED_BYTES_PER_RING_ELEMENT_1024,
        CPA_PKE_PUBLIC_KEY_SIZE_1024,
    >(&public_key.value)
}

/// Validate a private key.
///
/// Returns `true` if valid, and `false` otherwise.
#[cfg(not(eurydice))]
pub fn validate_private_key(
    private_key: &MlKem1024PrivateKey,
    ciphertext: &MlKem1024Ciphertext,
) -> bool {
    multiplexing::validate_private_key::<
        RANK_1024,
        SECRET_KEY_SIZE_1024,
        CPA_PKE_CIPHERTEXT_SIZE_1024,
    >(private_key, ciphertext)
}

/// Generate ML-KEM 1024 Key Pair
///
/// Generate an ML-KEM key pair. The input is a byte array of size
/// [`KEY_GENERATION_SEED_SIZE`].
///
/// This function returns an [`MlKem1024KeyPair`].
#[cfg(not(eurydice))]
pub fn generate_key_pair(
    randomness: [u8; KEY_GENERATION_SEED_SIZE],
) -> MlKemKeyPair<SECRET_KEY_SIZE_1024, CPA_PKE_PUBLIC_KEY_SIZE_1024> {
    multiplexing::generate_keypair::<
        RANK_1024,
        CPA_PKE_SECRET_KEY_SIZE_1024,
        SECRET_KEY_SIZE_1024,
        CPA_PKE_PUBLIC_KEY_SIZE_1024,
        RANKED_BYTES_PER_RING_ELEMENT_1024,
        ETA1,
        ETA1_RANDOMNESS_SIZE,
    >(randomness)
}

/// Encapsulate ML-KEM 1024
///
/// Generates an ([`MlKem1024Ciphertext`], [`MlKemSharedSecret`]) tuple.
/// The input is a reference to an [`MlKem1024PublicKey`] and [`SHARED_SECRET_SIZE`]
/// bytes of `randomness`.
#[cfg(not(eurydice))]
pub fn encapsulate(
    public_key: &MlKem1024PublicKey,
    randomness: [u8; SHARED_SECRET_SIZE],
) -> (MlKem1024Ciphertext, MlKemSharedSecret) {
    multiplexing::encapsulate::<
        RANK_1024,
        CPA_PKE_CIPHERTEXT_SIZE_1024,
        CPA_PKE_PUBLIC_KEY_SIZE_1024,
        T_AS_NTT_ENCODED_SIZE_1024,
        C1_SIZE_1024,
        C2_SIZE_1024,
        VECTOR_U_COMPRESSION_FACTOR_1024,
        VECTOR_V_COMPRESSION_FACTOR_1024,
        C1_BLOCK_SIZE_1024,
        ETA1,
        ETA1_RANDOMNESS_SIZE,
        ETA2,
        ETA2_RANDOMNESS_SIZE,
    >(public_key, randomness)
}

/// Decapsulate ML-KEM 1024
///
/// Generates an [`MlKemSharedSecret`].
/// The input is a reference to an [`MlKem1024PrivateKey`] and an [`MlKem1024Ciphertext`].
#[cfg(not(eurydice))]
pub fn decapsulate(
    private_key: &MlKem1024PrivateKey,
    ciphertext: &MlKem1024Ciphertext,
) -> MlKemSharedSecret {
    multiplexing::decapsulate::<
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
        MlKem1024Ciphertext, MlKem1024KeyPair, MlKem1024PublicKey, MlKemSharedSecret,
        KEY_GENERATION_SEED_SIZE, SHARED_SECRET_SIZE,
    };
    use ::rand::{CryptoRng, RngCore};

    /// Generate ML-KEM 1024 Key Pair
    ///
    /// The random number generator `rng` needs to implement `RngCore` and
    /// `CryptoRng` to sample the required randomness internally.
    ///
    /// This function returns an [`MlKem1024KeyPair`].
    pub fn generate_key_pair(rng: &mut (impl RngCore + CryptoRng)) -> MlKem1024KeyPair {
        let mut randomness = [0u8; KEY_GENERATION_SEED_SIZE];
        rng.fill_bytes(&mut randomness);

        super::generate_key_pair(randomness)
    }

    /// Encapsulate ML-KEM 1024
    ///
    /// Generates an ([`MlKem1024Ciphertext`], [`MlKemSharedSecret`]) tuple.
    /// The input is a reference to an [`MlKem1024PublicKey`].
    /// The random number generator `rng` needs to implement `RngCore` and
    /// `CryptoRng` to sample the required randomness internally.
    pub fn encapsulate(
        public_key: &MlKem1024PublicKey,
        rng: &mut (impl RngCore + CryptoRng),
    ) -> (MlKem1024Ciphertext, MlKemSharedSecret) {
        let mut randomness = [0u8; SHARED_SECRET_SIZE];
        rng.fill_bytes(&mut randomness);

        super::encapsulate(public_key, randomness)
    }
}

#[cfg(all(not(eurydice), feature = "kyber"))]
pub(crate) mod kyber {
    use super::*;

    /// Generate Kyber 1024 Key Pair
    ///
    /// Generate an ML-KEM key pair. The input is a byte array of size
    /// [`KEY_GENERATION_SEED_SIZE`].
    ///
    /// This function returns an [`MlKem1024KeyPair`].
    pub fn generate_key_pair(
        randomness: [u8; KEY_GENERATION_SEED_SIZE],
    ) -> MlKemKeyPair<SECRET_KEY_SIZE_1024, CPA_PKE_PUBLIC_KEY_SIZE_1024> {
        multiplexing::kyber_generate_keypair::<
            RANK_1024,
            CPA_PKE_SECRET_KEY_SIZE_1024,
            SECRET_KEY_SIZE_1024,
            CPA_PKE_PUBLIC_KEY_SIZE_1024,
            RANKED_BYTES_PER_RING_ELEMENT_1024,
            ETA1,
            ETA1_RANDOMNESS_SIZE,
        >(randomness)
    }

    /// Encapsulate Kyber 1024
    ///
    /// Generates an ([`MlKem1024Ciphertext`], [`MlKemSharedSecret`]) tuple.
    /// The input is a reference to an [`MlKem1024PublicKey`] and [`SHARED_SECRET_SIZE`]
    /// bytes of `randomness`.
    pub fn encapsulate(
        public_key: &MlKem1024PublicKey,
        randomness: [u8; SHARED_SECRET_SIZE],
    ) -> (MlKem1024Ciphertext, MlKemSharedSecret) {
        multiplexing::kyber_encapsulate::<
            RANK_1024,
            CPA_PKE_CIPHERTEXT_SIZE_1024,
            CPA_PKE_PUBLIC_KEY_SIZE_1024,
            T_AS_NTT_ENCODED_SIZE_1024,
            C1_SIZE_1024,
            C2_SIZE_1024,
            VECTOR_U_COMPRESSION_FACTOR_1024,
            VECTOR_V_COMPRESSION_FACTOR_1024,
            C1_BLOCK_SIZE_1024,
            ETA1,
            ETA1_RANDOMNESS_SIZE,
            ETA2,
            ETA2_RANDOMNESS_SIZE,
        >(public_key, randomness)
    }

    /// Decapsulate Kyber 1024
    ///
    /// Generates an [`MlKemSharedSecret`].
    /// The input is a reference to an [`MlKem1024PrivateKey`] and an [`MlKem1024Ciphertext`].
    #[cfg(all(not(eurydice), feature = "kyber"))]
    pub fn decapsulate(
        private_key: &MlKem1024PrivateKey,
        ciphertext: &MlKem1024Ciphertext,
    ) -> MlKemSharedSecret {
        multiplexing::kyber_decapsulate::<
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
            ETA1,
            ETA1_RANDOMNESS_SIZE,
            ETA2,
            ETA2_RANDOMNESS_SIZE,
            IMPLICIT_REJECTION_HASH_INPUT_SIZE,
        >(private_key, ciphertext)
    }
}
