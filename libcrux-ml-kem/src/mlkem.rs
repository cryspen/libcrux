//! Instantiating the ML-KEM variants for both key sizes, and platforms.

use libcrux_macros::{ml_kem_instantiations, ml_kem_multiplexing};

/// ML-KEM 512
mod mlkem512_constants;

/// ML-KEM 768
mod mlkem768_constants;

/// ML-KEM 1024
mod mlkem1024_constants;

/// Instantiate ML-KEM key sizes and optimizations.
#[ml_kem_instantiations(
    keys(512, 768, 1024),
    platforms(
        portable(
            crate::vector::portable::PortableVector,
            crate::hash_functions::portable::PortableHash<RANK>,
        ),
        avx2(
            crate::vector::SIMD256Vector,
            crate::hash_functions::avx2::Simd256Hash,
        ),
        neon(
            crate::vector::SIMD128Vector,
            crate::hash_functions::neon::Simd128Hash
        )))]
pub mod mlkem {
    use crate::{
        constants::SHARED_SECRET_SIZE,
        ind_cca::{self, MlKemSharedSecret, KEY_GENERATION_SEED_SIZE},
    };

    /// An ML-KEM Ciphertext
    pub type MlKemCiphertext = crate::types::MlKemCiphertext<CPA_PKE_CIPHERTEXT_SIZE>;
    /// An ML-KEM Private key
    pub type MlKemPrivateKey = crate::types::MlKemPrivateKey<SECRET_KEY_SIZE>;
    /// An ML-KEM Public key
    pub type MlKemPublicKey = crate::types::MlKemPublicKey<CPA_PKE_PUBLIC_KEY_SIZE>;
    /// An ML-KEM Key pair
    pub type MlKemKeyPair = crate::types::MlKemKeyPair<SECRET_KEY_SIZE, CPA_PKE_PUBLIC_KEY_SIZE>;

    // ===
    // Key validation
    // ===

    /// Validate a public key.
    ///
    /// Returns `true` if valid, and `false` otherwise.
    pub fn validate_public_key(public_key: &MlKemPublicKey) -> bool {
        ind_cca::validate_public_key::<
            RANK,
            RANKED_BYTES_PER_RING_ELEMENT,
            CPA_PKE_PUBLIC_KEY_SIZE,
            Vector,
        >(&public_key.value)
    }

    /// Validate a private key.
    ///
    /// Returns `true` if valid, and `false` otherwise.
    pub fn validate_private_key(
        private_key: &MlKemPrivateKey,
        ciphertext: &MlKemCiphertext,
    ) -> bool {
        ind_cca::validate_private_key::<RANK, SECRET_KEY_SIZE, CPA_PKE_CIPHERTEXT_SIZE, Hash>(
            private_key,
            ciphertext,
        )
    }

    /// Validate the private key only.
    ///
    /// Returns `true` if valid, and `false` otherwise.
    pub fn validate_private_key_only(private_key: &MlKemPrivateKey) -> bool {
        ind_cca::validate_private_key_only::<RANK, SECRET_KEY_SIZE, Hash>(private_key)
    }

    // ===
    // Key generation
    // ===

    /// Generate ML-KEM 768 Key Pair
    pub fn generate_key_pair(randomness: [u8; KEY_GENERATION_SEED_SIZE]) -> MlKemKeyPair {
        ind_cca::generate_keypair::<
            RANK,
            CPA_PKE_SECRET_KEY_SIZE,
            SECRET_KEY_SIZE,
            CPA_PKE_PUBLIC_KEY_SIZE,
            RANKED_BYTES_PER_RING_ELEMENT,
            ETA1,
            ETA1_RANDOMNESS_SIZE,
            Vector,
            Hash,
            crate::variant::MlKem,
        >(randomness)
    }

    /// Generate Kyber 768 Key Pair
    #[cfg(feature = "kyber")]
    #[cfg_attr(docsrs, doc(cfg(feature = "kyber")))]
    pub fn kyber_generate_key_pair(randomness: [u8; KEY_GENERATION_SEED_SIZE]) -> MlKemKeyPair {
        ind_cca::generate_keypair::<
            RANK,
            CPA_PKE_SECRET_KEY_SIZE,
            SECRET_KEY_SIZE,
            CPA_PKE_PUBLIC_KEY_SIZE,
            RANKED_BYTES_PER_RING_ELEMENT,
            ETA1,
            ETA1_RANDOMNESS_SIZE,
            Vector,
            Hash,
            crate::variant::Kyber,
        >(randomness)
    }

    // ===
    // Encaps
    // ===

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
            Vector,
            Hash,
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
            Vector,
            Hash,
            crate::variant::Kyber,
        >(public_key, randomness)
    }

    // ===
    // Decaps
    // ===

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
            Vector,
            Hash,
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
            Vector,
            Hash,
            crate::variant::Kyber,
        >(private_key, ciphertext)
    }

    /// Unpacked APIs that don't use serialized keys.
    pub mod unpacked {
        use super::*;

        /// An Unpacked ML-KEM 768 Public key
        pub type MlKemPublicKeyUnpacked = ind_cca::unpacked::MlKemPublicKeyUnpacked<RANK, Vector>;

        /// Am Unpacked ML-KEM 768 Key pair
        pub type MlKemKeyPairUnpacked = ind_cca::unpacked::MlKemKeyPairUnpacked<RANK, Vector>;

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
        pub fn serialized_public_key(
            public_key: &MlKemPublicKeyUnpacked,
            serialized: &mut MlKemPublicKey,
        ) {
            public_key.serialized_mut::<RANKED_BYTES_PER_RING_ELEMENT, CPA_PKE_PUBLIC_KEY_SIZE>(
                serialized,
            );
        }

        /// Get the serialized private key.
        pub fn key_pair_serialized_private_key(key_pair: &MlKemKeyPairUnpacked) -> MlKemPrivateKey {
            key_pair.serialized_private_key::<CPA_PKE_SECRET_KEY_SIZE, SECRET_KEY_SIZE, CPA_PKE_PUBLIC_KEY_SIZE, RANKED_BYTES_PER_RING_ELEMENT>()
        }

        /// Get the serialized private key.
        pub fn key_pair_serialized_private_key_mut(
            key_pair: &MlKemKeyPairUnpacked,
            serialized: &mut MlKemPrivateKey,
        ) {
            key_pair.serialized_private_key_mut::<CPA_PKE_SECRET_KEY_SIZE, SECRET_KEY_SIZE, CPA_PKE_PUBLIC_KEY_SIZE, RANKED_BYTES_PER_RING_ELEMENT>(serialized);
        }

        /// Get the serialized public key.
        #[hax_lib::requires(fstar!(r#"(forall (i:nat). i < 3 ==>
                    Libcrux_ml_kem.Serialize.coefficients_field_modulus_range (Seq.index
                        ${key_pair}.f_public_key.f_ind_cpa_public_key.f_t_as_ntt i))"#))]
        pub fn key_pair_serialized_public_key_mut(
            key_pair: &MlKemKeyPairUnpacked,
            serialized: &mut MlKemPublicKey,
        ) {
            key_pair.serialized_public_key_mut::<RANKED_BYTES_PER_RING_ELEMENT, CPA_PKE_PUBLIC_KEY_SIZE>(serialized);
        }

        /// Get the serialized public key.
        #[hax_lib::requires(fstar!(r#"forall (i:nat). i < 3 ==>
                Libcrux_ml_kem.Serialize.coefficients_field_modulus_range (Seq.index
                    ${key_pair}.f_public_key.f_ind_cpa_public_key.f_t_as_ntt i)"#))]
        pub fn key_pair_serialized_public_key(key_pair: &MlKemKeyPairUnpacked) -> MlKemPublicKey {
            key_pair
                .serialized_public_key::<RANKED_BYTES_PER_RING_ELEMENT, CPA_PKE_PUBLIC_KEY_SIZE>()
        }

        /// Get an unpacked key from a private key.
        pub fn key_pair_from_private_mut(
            private_key: &MlKemPrivateKey,
            key_pair: &mut MlKemKeyPairUnpacked,
        ) {
            ind_cca::unpacked::keys_from_private_key::<
                RANK,
                SECRET_KEY_SIZE,
                CPA_PKE_SECRET_KEY_SIZE,
                CPA_PKE_PUBLIC_KEY_SIZE,
                RANKED_BYTES_PER_RING_ELEMENT,
                T_AS_NTT_ENCODED_SIZE,
                Vector,
            >(private_key, key_pair);
        }

        /// Get the unpacked public key.
        pub fn public_key(key_pair: &MlKemKeyPairUnpacked, pk: &mut MlKemPublicKeyUnpacked) {
            *pk = (*key_pair.public_key()).clone();
        }

        /// Get the unpacked public key.
        pub fn unpacked_public_key(
            public_key: &MlKemPublicKey,
            unpacked_public_key: &mut MlKemPublicKeyUnpacked,
        ) {
            ind_cca::unpacked::unpack_public_key::<
                RANK,
                T_AS_NTT_ENCODED_SIZE,
                RANKED_BYTES_PER_RING_ELEMENT,
                CPA_PKE_PUBLIC_KEY_SIZE,
                Hash,
                Vector,
            >(public_key, unpacked_public_key)
        }

        /// Generate ML-KEM 768 Key Pair in "unpacked" form.
        pub fn generate_key_pair(
            randomness: [u8; KEY_GENERATION_SEED_SIZE],
        ) -> MlKemKeyPairUnpacked {
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
                Vector,
                Hash,
                crate::variant::MlKem,
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
                Vector,
                Hash,
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
                Vector,
                Hash,
            >(private_key, ciphertext)
        }
    }

    // // /// Incremental APIs.
    // // /// XXX: Only portable for now here. Needs plumbing
    // // pub mod incremental {
    // //     use super::*;
    // //     pub use ind_cca::incremental::*;

    // //     /// Encapsulate with `PublicKey1` to get `c1`.
    // //     pub fn encapsulate1
    // //     (
    // //         public_key_part: &PublicKey1,
    // //         randomness: [u8; SHARED_SECRET_SIZE],
    // //     ) -> (Ciphertext1<C1_SIZE>, EncapsState<RANK, crate::vector::portable::PortableVector>) {
    // //         crate::ind_cca::incremental::encapsulate1::<
    // //         RANK,
    // //         CPA_PKE_CIPHERTEXT_SIZE,
    // //         C1_SIZE,
    // //         VECTOR_U_COMPRESSION_FACTOR,
    // //         C1_BLOCK_SIZE,
    // //         ETA1,
    // //         ETA1_RANDOMNESS_SIZE,
    // //         ETA2,
    // //         ETA2_RANDOMNESS_SIZE,
    // //         crate::vector::portable::PortableVector,
    // //         crate::hash_functions::portable::PortableHash<RANK>
    // //         >(public_key_part, randomness)
    // //     }

    // //     /// Encapsulate with `PublicKey2` to get `c2`.
    // //     pub fn encapsulate2
    // //     (
    // //         state: &EncapsState<RANK, crate::vector::portable::PortableVector>,
    // //         public_key_part: &PublicKey2<RANK, crate::vector::portable::PortableVector>,
    // //     ) -> Ciphertext2<C2_SIZE> {
    // //         crate::ind_cca::incremental::encapsulate2::<
    // //         RANK,
    // //         C2_SIZE,
    // //         VECTOR_V_COMPRESSION_FACTOR,
    // //         crate::vector::portable::PortableVector,
    // //         >(state, public_key_part)
    // //     }

    // //     /// Decapsulate `c1` and `c2`.
    // //     pub fn decapsulate(
    // //         private_key: &MlKemPrivateKey,
    // //         ciphertext1: &Ciphertext1<C1_SIZE>,
    // //         ciphertext2: &Ciphertext2<C2_SIZE>,
    // //     ) -> MlKemSharedSecret {
    // //         crate::ind_cca::incremental::decapsulate::<
    // //             RANK,
    // //             SECRET_KEY_SIZE,
    // //             CPA_PKE_SECRET_KEY_SIZE,
    // //             CPA_PKE_PUBLIC_KEY_SIZE,
    // //             CPA_PKE_CIPHERTEXT_SIZE,
    // //             T_AS_NTT_ENCODED_SIZE,
    // //             C1_SIZE,
    // //             C2_SIZE,
    // //             VECTOR_U_COMPRESSION_FACTOR,
    // //             VECTOR_V_COMPRESSION_FACTOR,
    // //             C1_BLOCK_SIZE,
    // //             ETA1,
    // //             ETA1_RANDOMNESS_SIZE,
    // //             ETA2,
    // //             ETA2_RANDOMNESS_SIZE,
    // //             IMPLICIT_REJECTION_HASH_INPUT_SIZE,
    // //             crate::vector::portable::PortableVector,
    // //             crate::hash_functions::portable::PortableHash<RANK>,
    // //             crate::variant::MlKem,
    // //         >(private_key, ciphertext1, ciphertext2)
    // //     }
    // // }
}

/// The Rust API with runtime CPU feature detection.
#[ml_kem_multiplexing(keys(512, 768, 1024), platforms(portable, avx2, neon))]
pub mod mlkem {
    // For the case where we didn't compile with the simd128/simd256 features but
    // have a CPU that has it and thus tries to call the simd128/simd256 version,
    // we fall back to the portable version in this case.

    /// An ML-KEM Ciphertext
    pub type MlKemCiphertext = crate::types::MlKemCiphertext<CPA_PKE_CIPHERTEXT_SIZE>;
    /// An ML-KEM Private key
    pub type MlKemPrivateKey = crate::types::MlKemPrivateKey<SECRET_KEY_SIZE>;
    /// An ML-KEM Public key
    pub type MlKemPublicKey = crate::types::MlKemPublicKey<CPA_PKE_PUBLIC_KEY_SIZE>;
    /// An ML-KEM Key pair
    pub type MlKemKeyPair = crate::types::MlKemKeyPair<SECRET_KEY_SIZE, CPA_PKE_PUBLIC_KEY_SIZE>;

    #[cfg(feature = "simd256")]
    use avx2_instantiation::{
        decapsulate as decapsulate_avx2, encapsulate as encapsulate_avx2,
        generate_key_pair as generate_keypair_avx2,
    };

    #[cfg(feature = "simd128")]
    use neon_instantiation::{
        decapsulate as decapsulate_neon, encapsulate as encapsulate_neon,
        generate_key_pair as generate_keypair_neon,
    };

    #[cfg(not(feature = "simd256"))]
    use portable_instantiation::{
        decapsulate as decapsulate_avx2, encapsulate as encapsulate_avx2,
        generate_key_pair as generate_keypair_avx2,
    };

    #[cfg(not(feature = "simd128"))]
    use portable_instantiation::{
        decapsulate as decapsulate_neon, encapsulate as encapsulate_neon,
        generate_key_pair as generate_keypair_neon,
    };

    use crate::{MlKemSharedSecret, KEY_GENERATION_SEED_SIZE, SHARED_SECRET_SIZE};

    /// Validate a public key.
    #[hax_lib::requires(fstar!(r#"Spec.MLKEM.is_rank $K /\
    $RANKED_BYTES_PER_RING_ELEMENT == Spec.MLKEM.v_RANKED_BYTES_PER_RING_ELEMENT $K /\
    $PUBLIC_KEY_SIZE == Spec.MLKEM.v_CCA_PUBLIC_KEY_SIZE $K"#))]
    #[inline(always)]
    pub fn validate_public_key(public_key: &MlKemPublicKey) -> bool {
        portable_instantiation::validate_public_key(public_key)
    }

    /// Validate a private key.
    #[inline(always)]
    #[hax_lib::requires(fstar!(r#"Spec.MLKEM.is_rank $K /\
                $SECRET_KEY_SIZE == Spec.MLKEM.v_CCA_PRIVATE_KEY_SIZE $K /\
                $CIPHERTEXT_SIZE == Spec.MLKEM.v_CPA_CIPHERTEXT_SIZE $K"#))]
    pub fn validate_private_key(
        private_key: &MlKemPrivateKey,
        ciphertext: &MlKemCiphertext,
    ) -> bool {
        portable_instantiation::validate_private_key(private_key, ciphertext)
    }

    /// Generate a new key pair based on the `randomness`.
    #[hax_lib::requires(fstar!(r#"Spec.MLKEM.is_rank $K /\
    $CPA_PRIVATE_KEY_SIZE == Spec.MLKEM.v_CPA_PRIVATE_KEY_SIZE $K /\
    $PRIVATE_KEY_SIZE == Spec.MLKEM.v_CCA_PRIVATE_KEY_SIZE $K /\
    $PUBLIC_KEY_SIZE == Spec.MLKEM.v_CPA_PUBLIC_KEY_SIZE $K /\
    $RANKED_BYTES_PER_RING_ELEMENT == Spec.MLKEM.v_RANKED_BYTES_PER_RING_ELEMENT $K /\
    $ETA1 == Spec.MLKEM.v_ETA1 $K /\
    $ETA1_RANDOMNESS_SIZE == Spec.MLKEM.v_ETA1_RANDOMNESS_SIZE $K"#))]
    pub fn generate_key_pair(randomness: [u8; KEY_GENERATION_SEED_SIZE]) -> MlKemKeyPair {
        // Runtime feature detection.
        if libcrux_platform::simd256_support() {
            generate_keypair_avx2(randomness)
        } else if libcrux_platform::simd128_support() {
            generate_keypair_neon(randomness)
        } else {
            portable_instantiation::generate_key_pair(randomness)
        }
    }

    /// Encapsulate to the `public_key` using the `randomness`.
    #[hax_lib::requires(fstar!(r#"Spec.MLKEM.is_rank $K /\
    $CIPHERTEXT_SIZE == Spec.MLKEM.v_CPA_CIPHERTEXT_SIZE $K /\
    $PUBLIC_KEY_SIZE == Spec.MLKEM.v_CPA_PUBLIC_KEY_SIZE $K /\
    $T_AS_NTT_ENCODED_SIZE == Spec.MLKEM.v_T_AS_NTT_ENCODED_SIZE $K /\
    $C1_SIZE == Spec.MLKEM.v_C1_SIZE $K /\
    $C2_SIZE == Spec.MLKEM.v_C2_SIZE $K /\
    $VECTOR_U_COMPRESSION_FACTOR == Spec.MLKEM.v_VECTOR_U_COMPRESSION_FACTOR  $K /\
    $VECTOR_V_COMPRESSION_FACTOR == Spec.MLKEM.v_VECTOR_V_COMPRESSION_FACTOR  $K /\
    $C1_BLOCK_SIZE == Spec.MLKEM.v_C1_BLOCK_SIZE $K /\
    $ETA1 == Spec.MLKEM.v_ETA1 $K /\
    $ETA1_RANDOMNESS_SIZE == Spec.MLKEM.v_ETA1_RANDOMNESS_SIZE $K /\
    $ETA2 == Spec.MLKEM.v_ETA2 $K /\
    $ETA2_RANDOMNESS_SIZE == Spec.MLKEM.v_ETA2_RANDOMNESS_SIZE $K"#))]
    pub fn encapsulate(
        public_key: &MlKemPublicKey,
        randomness: [u8; SHARED_SECRET_SIZE],
    ) -> (MlKemCiphertext, MlKemSharedSecret) {
        if libcrux_platform::simd256_support() {
            encapsulate_avx2(public_key, randomness)
        } else if libcrux_platform::simd128_support() {
            encapsulate_neon(public_key, randomness)
        } else {
            portable_instantiation::encapsulate(public_key, randomness)
        }
    }

    /// Decapsulate a `ciphertext` with a `private_key`.
    #[hax_lib::requires(fstar!(r#"Spec.MLKEM.is_rank $K /\
    $SECRET_KEY_SIZE == Spec.MLKEM.v_CCA_PRIVATE_KEY_SIZE $K /\
    $CPA_SECRET_KEY_SIZE == Spec.MLKEM.v_CPA_PRIVATE_KEY_SIZE $K /\
    $PUBLIC_KEY_SIZE == Spec.MLKEM.v_CPA_PUBLIC_KEY_SIZE $K /\
    $CIPHERTEXT_SIZE == Spec.MLKEM.v_CPA_CIPHERTEXT_SIZE $K /\
    $T_AS_NTT_ENCODED_SIZE == Spec.MLKEM.v_T_AS_NTT_ENCODED_SIZE $K /\
    $C1_SIZE == Spec.MLKEM.v_C1_SIZE $K /\
    $C2_SIZE == Spec.MLKEM.v_C2_SIZE $K /\
    $VECTOR_U_COMPRESSION_FACTOR == Spec.MLKEM.v_VECTOR_U_COMPRESSION_FACTOR  $K /\
    $VECTOR_V_COMPRESSION_FACTOR == Spec.MLKEM.v_VECTOR_V_COMPRESSION_FACTOR  $K /\
    $C1_BLOCK_SIZE == Spec.MLKEM.v_C1_BLOCK_SIZE $K /\
    $ETA1 == Spec.MLKEM.v_ETA1 $K /\
    $ETA1_RANDOMNESS_SIZE == Spec.MLKEM.v_ETA1_RANDOMNESS_SIZE $K /\
    $ETA2 == Spec.MLKEM.v_ETA2 $K /\
    $ETA2_RANDOMNESS_SIZE == Spec.MLKEM.v_ETA2_RANDOMNESS_SIZE $K /\
    $IMPLICIT_REJECTION_HASH_INPUT_SIZE == Spec.MLKEM.v_IMPLICIT_REJECTION_HASH_INPUT_SIZE $K"#))]
    pub fn decapsulate(
        private_key: &MlKemPrivateKey,
        ciphertext: &MlKemCiphertext,
    ) -> MlKemSharedSecret {
        if libcrux_platform::simd256_support() {
            decapsulate_avx2(private_key, ciphertext)
        } else if libcrux_platform::simd128_support() {
            decapsulate_neon(private_key, ciphertext)
        } else {
            portable_instantiation::decapsulate(private_key, ciphertext)
        }
    }

    /// Round 3 Kyber variant.
    #[cfg(feature = "kyber")]
    pub mod kyber {
        use super::*;

        #[cfg(feature = "simd256")]
        use avx2_instantiation::{
            kyber_decapsulate as kyber_decapsulate_avx2,
            kyber_encapsulate as kyber_encapsulate_avx2,
            kyber_generate_key_pair as kyber_generate_keypair_avx2,
        };

        #[cfg(feature = "simd128")]
        use neon_instantiation::{
            kyber_decapsulate as kyber_decapsulate_neon,
            kyber_encapsulate as kyber_encapsulate_neon,
            kyber_generate_key_pair as kyber_generate_keypair_neon,
        };

        #[cfg(not(feature = "simd256"))]
        use portable_instantiation::{
            kyber_decapsulate as kyber_decapsulate_avx2,
            kyber_encapsulate as kyber_encapsulate_avx2,
            kyber_generate_key_pair as kyber_generate_keypair_avx2,
        };

        #[cfg(not(feature = "simd128"))]
        use portable_instantiation::{
            kyber_decapsulate as kyber_decapsulate_neon,
            kyber_encapsulate as kyber_encapsulate_neon,
            kyber_generate_key_pair as kyber_generate_keypair_neon,
        };

        /// Generate a new key pair.
        pub fn generate_key_pair(randomness: [u8; KEY_GENERATION_SEED_SIZE]) -> MlKemKeyPair {
            // Runtime feature detection.
            if libcrux_platform::simd256_support() {
                kyber_generate_keypair_avx2(randomness)
            } else if libcrux_platform::simd128_support() {
                kyber_generate_keypair_neon(randomness)
            } else {
                portable_instantiation::kyber_generate_key_pair(randomness)
            }
        }

        /// Encapsulate `randomness` to the `public_key`.
        pub fn encapsulate(
            public_key: &MlKemPublicKey,
            randomness: [u8; SHARED_SECRET_SIZE],
        ) -> (MlKemCiphertext, MlKemSharedSecret) {
            if libcrux_platform::simd256_support() {
                kyber_encapsulate_avx2(public_key, randomness)
            } else if libcrux_platform::simd128_support() {
                kyber_encapsulate_neon(public_key, randomness)
            } else {
                portable_instantiation::kyber_encapsulate(public_key, randomness)
            }
        }

        /// Decapsulate the `ciphertext` using the `private_key`.
        pub fn decapsulate(
            private_key: &MlKemPrivateKey,
            ciphertext: &MlKemCiphertext,
        ) -> MlKemSharedSecret {
            if libcrux_platform::simd256_support() {
                kyber_decapsulate_avx2(private_key, ciphertext)
            } else if libcrux_platform::simd128_support() {
                kyber_decapsulate_neon(private_key, ciphertext)
            } else {
                portable_instantiation::kyber_decapsulate(private_key, ciphertext)
            }
        }
    }
}
