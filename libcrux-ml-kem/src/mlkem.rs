//! Instantiating the ML-KEM variants for both key sizes, and platforms.

/// ML-KEM 768
mod mlkem768 {
    use crate::constants::*;

    // Kyber 768 parameters
    pub(super) const RANK: usize = 3;
    pub(super) const RANKED_BYTES_PER_RING_ELEMENT: usize = RANK * BITS_PER_RING_ELEMENT / 8;
    pub(super) const T_AS_NTT_ENCODED_SIZE: usize =
        (RANK * COEFFICIENTS_IN_RING_ELEMENT * BITS_PER_COEFFICIENT) / 8;
    pub(super) const VECTOR_U_COMPRESSION_FACTOR: usize = 10;
    // [hax]: hacspec/hacspec-v2#27 stealing error
    // block_len::<VECTOR_U_COMPRESSION_FACTOR>()
    pub(super) const C1_BLOCK_SIZE: usize =
        (COEFFICIENTS_IN_RING_ELEMENT * VECTOR_U_COMPRESSION_FACTOR) / 8;
    // [hax]: hacspec/hacspec-v2#27 stealing error
    //  serialized_len::<RANK, C1_BLOCK_SIZE>();
    pub(super) const C1_SIZE: usize = C1_BLOCK_SIZE * RANK;
    pub(super) const VECTOR_V_COMPRESSION_FACTOR: usize = 4;
    // [hax]: hacspec/hacspec-v2#27 stealing error
    //  block_len::<VECTOR_V_COMPRESSION_FACTOR>()
    pub(super) const C2_SIZE: usize =
        (COEFFICIENTS_IN_RING_ELEMENT * VECTOR_V_COMPRESSION_FACTOR) / 8;
    pub(super) const CPA_PKE_SECRET_KEY_SIZE: usize =
        (RANK * COEFFICIENTS_IN_RING_ELEMENT * BITS_PER_COEFFICIENT) / 8;
    pub(crate) const CPA_PKE_PUBLIC_KEY_SIZE: usize = T_AS_NTT_ENCODED_SIZE + 32;
    // These two are used in the hybrid kem. This could probably be improved.
    pub(super) const CPA_PKE_CIPHERTEXT_SIZE: usize = C1_SIZE + C2_SIZE;
    pub(super) const SECRET_KEY_SIZE: usize =
        CPA_PKE_SECRET_KEY_SIZE + CPA_PKE_PUBLIC_KEY_SIZE + H_DIGEST_SIZE + SHARED_SECRET_SIZE;

    pub(super) const ETA1: usize = 2;
    pub(super) const ETA1_RANDOMNESS_SIZE: usize = ETA1 * 64;
    pub(super) const ETA2: usize = 2;
    pub(super) const ETA2_RANDOMNESS_SIZE: usize = ETA2 * 64;

    pub(super) const IMPLICIT_REJECTION_HASH_INPUT_SIZE: usize =
        SHARED_SECRET_SIZE + CPA_PKE_CIPHERTEXT_SIZE;

    /// An ML-KEM 768 Ciphertext
    pub type MlKemCiphertext = crate::types::MlKemCiphertext<CPA_PKE_CIPHERTEXT_SIZE>;
    /// An ML-KEM 768 Private key
    pub type MlKemPrivateKey = crate::types::MlKemPrivateKey<SECRET_KEY_SIZE>;
    /// An ML-KEM 768 Public key
    pub type MlKemPublicKey = crate::types::MlKemPublicKey<CPA_PKE_PUBLIC_KEY_SIZE>;
    /// An ML-KEM 768 Key pair
    pub type MlKemKeyPair = crate::types::MlKemKeyPair<SECRET_KEY_SIZE, CPA_PKE_PUBLIC_KEY_SIZE>;
}

// Instantiate the different functions.
macro_rules! instantiate {
    ($modp:ident, $const_mod:ident, $vector:path, $hash:path, $doc:expr) => {
        #[doc = $doc]
        pub mod $modp {
            use super::$const_mod::*;
            use crate::{ind_cca::{self,  KEY_GENERATION_SEED_SIZE, MlKemSharedSecret}, constants::SHARED_SECRET_SIZE};

            /// Validate a public key.
            ///
            /// Returns `true` if valid, and `false` otherwise.
            pub fn validate_public_key(public_key: &MlKemPublicKey) -> bool {
                ind_cca::validate_public_key::<
                    RANK,
                    RANKED_BYTES_PER_RING_ELEMENT,
                    CPA_PKE_PUBLIC_KEY_SIZE,
                    $vector
                >(&public_key.value)
            }

            /// Validate a private key.
            ///
            /// Returns `true` if valid, and `false` otherwise.
            pub fn validate_private_key(
                private_key: &MlKemPrivateKey,
                ciphertext: &MlKemCiphertext,
            ) -> bool {
                ind_cca::validate_private_key::<
                    RANK,
                    SECRET_KEY_SIZE,
                    CPA_PKE_CIPHERTEXT_SIZE,
                    $hash
                >(private_key, ciphertext)
            }

            /// Validate the private key only.
            ///
            /// Returns `true` if valid, and `false` otherwise.
            pub fn validate_private_key_only(
                private_key: &MlKemPrivateKey,
            ) -> bool {
                ind_cca::validate_private_key_only::<
                    RANK,
                    SECRET_KEY_SIZE,
                    $hash
                >(private_key)
            }

            /// Generate ML-KEM 768 Key Pair
            pub fn generate_key_pair(
                randomness: [u8; KEY_GENERATION_SEED_SIZE],
            ) -> MlKemKeyPair {
                ind_cca::generate_keypair::<
                    RANK,
                    CPA_PKE_SECRET_KEY_SIZE,
                    SECRET_KEY_SIZE,
                    CPA_PKE_PUBLIC_KEY_SIZE,
                    RANKED_BYTES_PER_RING_ELEMENT,
                    ETA1,
                    ETA1_RANDOMNESS_SIZE,
                    $vector,
                    $hash,
                    crate::variant::MlKem,
                >(randomness)
            }

            /// Generate Kyber 768 Key Pair
            #[cfg(feature = "kyber")]
            #[cfg_attr(docsrs, doc(cfg(feature = "kyber")))]
            pub fn kyber_generate_key_pair(
                randomness: [u8; KEY_GENERATION_SEED_SIZE],
            ) -> MlKemKeyPair {
                ind_cca::generate_keypair::<
                    RANK,
                    CPA_PKE_SECRET_KEY_SIZE,
                    SECRET_KEY_SIZE,
                    CPA_PKE_PUBLIC_KEY_SIZE,
                    RANKED_BYTES_PER_RING_ELEMENT,
                    ETA1,
                    ETA1_RANDOMNESS_SIZE,
                    $vector,
                    $hash,
                    crate::variant::Kyber,
                >(randomness)
            }

            /// Encapsulate ML-KEM 768
            ///
            /// Generates an ([`MlKemCiphertext`], [`MlKemSharedSecret`]) tuple.
            /// The input is a reference to an [`MlKemPublicKey`] and [`SHARED_SECRET_SIZE`]
            /// bytes of `randomness`.
            pub fn encapsulate(
                public_key: &MlKemPublicKey,
                randomness: [u8; SHARED_SECRET_SIZE],
            ) -> (MlKemCiphertext, MlKemSharedSecret) {
                ind_cca::encapsulate::<
                    RANK,
                    CPA_PKE_CIPHERTEXT_SIZE,
                    CPA_PKE_PUBLIC_KEY_SIZE,
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

            /// Encapsulate Kyber 768
            ///
            /// Generates an ([`MlKemCiphertext`], [`MlKemSharedSecret`]) tuple.
            /// The input is a reference to an [`MlKemPublicKey`] and [`SHARED_SECRET_SIZE`]
            /// bytes of `randomness`.
            #[cfg(feature = "kyber")]
            #[cfg_attr(docsrs, doc(cfg(feature = "kyber")))]
            pub fn kyber_encapsulate(
                public_key: &MlKemPublicKey,
                randomness: [u8; SHARED_SECRET_SIZE],
            ) -> (MlKemCiphertext, MlKemSharedSecret) {
                ind_cca::kyber_encapsulate::<
                    RANK,
                    CPA_PKE_CIPHERTEXT_SIZE,
                    CPA_PKE_PUBLIC_KEY_SIZE,
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
                    crate::variant::Kyber,
                >(public_key, randomness)
            }

            /// Decapsulate ML-KEM 768
            ///
            /// Generates an [`MlKemSharedSecret`].
            /// The input is a reference to an [`MlKemPrivateKey`] and an [`MlKemCiphertext`].
            pub fn decapsulate(
                private_key: &MlKemPrivateKey,
                ciphertext: &MlKemCiphertext,
            ) -> MlKemSharedSecret {
                ind_cca::decapsulate::<
                    RANK,
                    SECRET_KEY_SIZE,
                    CPA_PKE_SECRET_KEY_SIZE,
                    CPA_PKE_PUBLIC_KEY_SIZE,
                    CPA_PKE_CIPHERTEXT_SIZE,
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

            /// Decapsulate Kyber 768
            ///
            /// Generates an [`MlKemSharedSecret`].
            /// The input is a reference to an [`MlKemPrivateKey`] and an [`MlKemCiphertext`].
            #[cfg(feature = "kyber")]
            #[cfg_attr(docsrs, doc(cfg(feature = "kyber")))]
            pub fn kyber_decapsulate(
                private_key: &MlKemPrivateKey,
                ciphertext: &MlKemCiphertext,
            ) -> MlKemSharedSecret {
                ind_cca::kyber_decapsulate::<
                    RANK,
                    SECRET_KEY_SIZE,
                    CPA_PKE_SECRET_KEY_SIZE,
                    CPA_PKE_PUBLIC_KEY_SIZE,
                    CPA_PKE_CIPHERTEXT_SIZE,
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

            /// Unpacked APIs that don't use serialized keys.
            pub mod unpacked {
                use super::*;

                /// An Unpacked ML-KEM 768 Public key
                pub type MlKemPublicKeyUnpacked = ind_cca::unpacked::MlKemPublicKeyUnpacked<RANK, $vector>;

                /// Am Unpacked ML-KEM 768 Key pair
                pub type MlKemKeyPairUnpacked = ind_cca::unpacked::MlKemKeyPairUnpacked<RANK, $vector>;

                /// Create a new, empty unpacked key.
                pub fn init_key_pair() -> MlKemKeyPairUnpacked {
                    MlKemKeyPairUnpacked::default()
                }

                /// Create a new, empty unpacked public key.
                pub fn init_public_key() -> MlKemPublicKeyUnpacked {
                    MlKemPublicKeyUnpacked::default()
                }

                /// Get the serialized public key.
                #[hax_lib::requires(fstar!(r#"forall (i:nat). i < 3 ==>
                    Libcrux_ml_kem.Serialize.coefficients_field_modulus_range (Seq.index 
                        ${public_key}.f_ind_cpa_public_key.f_t_as_ntt i)"#))]
                pub fn serialized_public_key(public_key: &MlKemPublicKeyUnpacked, serialized : &mut MlKemPublicKey) {
                    public_key.serialized_mut::<RANKED_BYTES_PER_RING_ELEMENT, CPA_PKE_PUBLIC_KEY_SIZE>(serialized);
                }

                /// Get the serialized private key.
                pub fn key_pair_serialized_private_key(key_pair: &MlKemKeyPairUnpacked) -> MlKemPrivateKey {
                    key_pair.serialized_private_key::<CPA_PKE_SECRET_KEY_SIZE, SECRET_KEY_SIZE, CPA_PKE_PUBLIC_KEY_SIZE, RANKED_BYTES_PER_RING_ELEMENT>()
                }

                /// Get the serialized private key.
                pub fn key_pair_serialized_private_key_mut(key_pair: &MlKemKeyPairUnpacked, serialized: &mut MlKemPrivateKey) {
                    key_pair.serialized_private_key_mut::<CPA_PKE_SECRET_KEY_SIZE, SECRET_KEY_SIZE, CPA_PKE_PUBLIC_KEY_SIZE, RANKED_BYTES_PER_RING_ELEMENT>(serialized);
                }

                /// Get the serialized public key.
                #[hax_lib::requires(fstar!(r#"(forall (i:nat). i < 3 ==>
                        Libcrux_ml_kem.Serialize.coefficients_field_modulus_range (Seq.index 
                            ${key_pair}.f_public_key.f_ind_cpa_public_key.f_t_as_ntt i))"#))]
                pub fn key_pair_serialized_public_key_mut(key_pair: &MlKemKeyPairUnpacked, serialized: &mut MlKemPublicKey) {
                    key_pair.serialized_public_key_mut::<RANKED_BYTES_PER_RING_ELEMENT, CPA_PKE_PUBLIC_KEY_SIZE>(serialized);
                }

                /// Get the serialized public key.
                #[hax_lib::requires(fstar!(r#"forall (i:nat). i < 3 ==>
                    Libcrux_ml_kem.Serialize.coefficients_field_modulus_range (Seq.index 
                        ${key_pair}.f_public_key.f_ind_cpa_public_key.f_t_as_ntt i)"#))]
                pub fn key_pair_serialized_public_key(key_pair: &MlKemKeyPairUnpacked) ->MlKemPublicKey {
                    key_pair.serialized_public_key::<RANKED_BYTES_PER_RING_ELEMENT, CPA_PKE_PUBLIC_KEY_SIZE>()
                }

                /// Get an unpacked key from a private key.
                pub fn key_pair_from_private_mut(private_key: &MlKemPrivateKey, key_pair: &mut MlKemKeyPairUnpacked) {
                    ind_cca::unpacked::keys_from_private_key::<RANK, SECRET_KEY_SIZE, CPA_PKE_SECRET_KEY_SIZE, CPA_PKE_PUBLIC_KEY_SIZE, RANKED_BYTES_PER_RING_ELEMENT, T_AS_NTT_ENCODED_SIZE, $vector>(private_key, key_pair);
                }

                /// Get the unpacked public key.
                pub fn public_key(key_pair: &MlKemKeyPairUnpacked, pk: &mut MlKemPublicKeyUnpacked) {
                    *pk = (*key_pair.public_key()).clone();
                }

                /// Get the unpacked public key.
                pub fn unpacked_public_key(
                    public_key: &MlKemPublicKey,
                    unpacked_public_key: &mut MlKemPublicKeyUnpacked
                ) {
                    ind_cca::unpacked::unpack_public_key::<
                        RANK,
                        T_AS_NTT_ENCODED_SIZE,
                        RANKED_BYTES_PER_RING_ELEMENT,
                        CPA_PKE_PUBLIC_KEY_SIZE,
                        $hash,
                        $vector,
                    >(public_key, unpacked_public_key)
                }

                /// Generate ML-KEM 768 Key Pair in "unpacked" form.
                pub fn generate_key_pair(
                    randomness: [u8; KEY_GENERATION_SEED_SIZE]
                ) ->  MlKemKeyPairUnpacked {
                    let mut key_pair = MlKemKeyPairUnpacked::default();
                    generate_key_pair_mut(randomness, &mut key_pair);
                    key_pair
                }

                /// Generate ML-KEM 768 Key Pair in "unpacked" form.
                pub fn generate_key_pair_mut(
                    randomness: [u8; KEY_GENERATION_SEED_SIZE],
                    key_pair: &mut MlKemKeyPairUnpacked,
                ) {
                    ind_cca::unpacked::generate_keypair::<
                        RANK,
                        CPA_PKE_SECRET_KEY_SIZE,
                        SECRET_KEY_SIZE,
                        CPA_PKE_PUBLIC_KEY_SIZE,
                        RANKED_BYTES_PER_RING_ELEMENT,
                        ETA1,
                        ETA1_RANDOMNESS_SIZE,
                        $vector,
                        $hash,
                        crate::variant::MlKem
                    >(randomness, key_pair);
                }

                /// Encapsulate ML-KEM 768 (unpacked)
                ///
                /// Generates an ([`MlKemCiphertext`], [`MlKemSharedSecret`]) tuple.
                /// The input is a reference to an unpacked public key of type [`MlKemPublicKeyUnpacked`],
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
                    public_key: &MlKemPublicKeyUnpacked,
                    randomness: [u8; SHARED_SECRET_SIZE],
                ) -> (MlKemCiphertext, MlKemSharedSecret) {
                    ind_cca::unpacked::encapsulate::<
                        RANK,
                        CPA_PKE_CIPHERTEXT_SIZE,
                        CPA_PKE_PUBLIC_KEY_SIZE,
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
                    >(public_key, randomness)
                }

                /// Decapsulate ML-KEM 768 (unpacked)
                ///
                /// Generates an [`MlKemSharedSecret`].
                /// The input is a reference to an unpacked key pair of type [`MlKemKeyPairUnpacked`]
                /// and an [`MlKemCiphertext`].
                pub fn decapsulate(
                    private_key: &MlKemKeyPairUnpacked,
                    ciphertext: &MlKemCiphertext,
                ) -> MlKemSharedSecret {
                    ind_cca::unpacked::decapsulate::<
                        RANK,
                        SECRET_KEY_SIZE,
                        CPA_PKE_SECRET_KEY_SIZE,
                        CPA_PKE_PUBLIC_KEY_SIZE,
                        CPA_PKE_CIPHERTEXT_SIZE,
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
                    >(private_key, ciphertext)
                }
            }

            // /// Incremental APIs.
            // /// XXX: Only portable for now here. Needs plumbing
            // pub mod incremental {
            //     use super::*;
            //     pub use ind_cca::incremental::*;

            //     /// Encapsulate with `PublicKey1` to get `c1`.
            //     pub fn encapsulate1
            //     (
            //         public_key_part: &PublicKey1,
            //         randomness: [u8; SHARED_SECRET_SIZE],
            //     ) -> (Ciphertext1<C1_SIZE>, EncapsState<RANK, crate::vector::portable::PortableVector>) {
            //         crate::ind_cca::incremental::encapsulate1::<
            //         RANK,
            //         CPA_PKE_CIPHERTEXT_SIZE,
            //         C1_SIZE,
            //         VECTOR_U_COMPRESSION_FACTOR,
            //         C1_BLOCK_SIZE,
            //         ETA1,
            //         ETA1_RANDOMNESS_SIZE,
            //         ETA2,
            //         ETA2_RANDOMNESS_SIZE,
            //         crate::vector::portable::PortableVector,
            //         crate::hash_functions::portable::PortableHash<RANK>
            //         >(public_key_part, randomness)
            //     }

            //     /// Encapsulate with `PublicKey2` to get `c2`.
            //     pub fn encapsulate2
            //     (
            //         state: &EncapsState<RANK, crate::vector::portable::PortableVector>,
            //         public_key_part: &PublicKey2<RANK, crate::vector::portable::PortableVector>,
            //     ) -> Ciphertext2<C2_SIZE> {
            //         crate::ind_cca::incremental::encapsulate2::<
            //         RANK,
            //         C2_SIZE,
            //         VECTOR_V_COMPRESSION_FACTOR,
            //         crate::vector::portable::PortableVector,
            //         >(state, public_key_part)
            //     }

            //     /// Decapsulate `c1` and `c2`.
            //     pub fn decapsulate(
            //         private_key: &MlKemPrivateKey,
            //         ciphertext1: &Ciphertext1<C1_SIZE>,
            //         ciphertext2: &Ciphertext2<C2_SIZE>,
            //     ) -> MlKemSharedSecret {
            //         crate::ind_cca::incremental::decapsulate::<
            //             RANK,
            //             SECRET_KEY_SIZE,
            //             CPA_PKE_SECRET_KEY_SIZE,
            //             CPA_PKE_PUBLIC_KEY_SIZE,
            //             CPA_PKE_CIPHERTEXT_SIZE,
            //             T_AS_NTT_ENCODED_SIZE,
            //             C1_SIZE,
            //             C2_SIZE,
            //             VECTOR_U_COMPRESSION_FACTOR,
            //             VECTOR_V_COMPRESSION_FACTOR,
            //             C1_BLOCK_SIZE,
            //             ETA1,
            //             ETA1_RANDOMNESS_SIZE,
            //             ETA2,
            //             ETA2_RANDOMNESS_SIZE,
            //             IMPLICIT_REJECTION_HASH_INPUT_SIZE,
            //             crate::vector::portable::PortableVector,
            //             crate::hash_functions::portable::PortableHash<RANK>,
            //             crate::variant::MlKem,
            //         >(private_key, ciphertext1, ciphertext2)
            //     }
            // }
        }
    };
}

instantiate! {
    portable,
    mlkem768,
    crate::vector::portable::PortableVector,
    crate::hash_functions::portable::PortableHash<RANK>,
    "Portable ML-KEM 768"
}
#[cfg(feature = "simd256")]
instantiate! {
    avx2,
    mlkem768,
    crate::vector::SIMD256Vector,
    crate::hash_functions::avx2::Simd256Hash,
    "AVX2 Optimised ML-KEM 768"
}
// instantiate! {avx2, crate::ind_cca::instantiations::avx2, "AVX2 Optimised ML-KEM 768"}
// #[cfg(feature = "simd128")]
// instantiate! {neon, ind_cca::instantiations::neon, "Neon Optimised ML-KEM 768"}
