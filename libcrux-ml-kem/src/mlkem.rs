//! Instantiating the ML-KEM variants for both key sizes, and platforms.

use libcrux_macros::ml_kem_variants;

/// ML-KEM 512
mod mlkem512_constants {
    use crate::constants::*;

    pub(super) const RANK: usize = 2;
    pub(super) const RANKED_BYTES_PER_RING_ELEMENT: usize = RANK * BITS_PER_RING_ELEMENT / 8;
    pub(super) const T_AS_NTT_ENCODED_SIZE: usize =
        (RANK * COEFFICIENTS_IN_RING_ELEMENT * BITS_PER_COEFFICIENT) / 8;
    pub(super) const VECTOR_U_COMPRESSION_FACTOR: usize = 10;
    pub(super) const C1_BLOCK_SIZE: usize =
        (COEFFICIENTS_IN_RING_ELEMENT * VECTOR_U_COMPRESSION_FACTOR) / 8;
    pub(super) const C1_SIZE: usize = C1_BLOCK_SIZE * RANK;
    pub(super) const VECTOR_V_COMPRESSION_FACTOR: usize = 4;
    pub(super) const C2_SIZE: usize =
        (COEFFICIENTS_IN_RING_ELEMENT * VECTOR_V_COMPRESSION_FACTOR) / 8;
    pub(super) const CPA_PKE_SECRET_KEY_SIZE: usize =
        (RANK * COEFFICIENTS_IN_RING_ELEMENT * BITS_PER_COEFFICIENT) / 8;
    pub(crate) const CPA_PKE_PUBLIC_KEY_SIZE: usize = T_AS_NTT_ENCODED_SIZE + 32;
    pub(super) const CPA_PKE_CIPHERTEXT_SIZE: usize = C1_SIZE + C2_SIZE;

    pub(crate) const SECRET_KEY_SIZE: usize =
        CPA_PKE_SECRET_KEY_SIZE + CPA_PKE_PUBLIC_KEY_SIZE + H_DIGEST_SIZE + SHARED_SECRET_SIZE;

    pub(super) const ETA1: usize = 3;
    pub(super) const ETA1_RANDOMNESS_SIZE: usize = ETA1 * 64;
    pub(super) const ETA2: usize = 2;
    pub(super) const ETA2_RANDOMNESS_SIZE: usize = ETA2 * 64;

    pub(super) const IMPLICIT_REJECTION_HASH_INPUT_SIZE: usize =
        SHARED_SECRET_SIZE + CPA_PKE_CIPHERTEXT_SIZE;
}

/// ML-KEM 768
mod mlkem768_constants {
    use crate::constants::*;

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
}

/// ML-KEM 1024
mod mlkem1024_constants {
    use crate::constants::*;

    pub(super) const RANK: usize = 4;
    pub(super) const RANKED_BYTES_PER_RING_ELEMENT: usize = RANK * BITS_PER_RING_ELEMENT / 8;
    pub(super) const T_AS_NTT_ENCODED_SIZE: usize =
        (RANK * COEFFICIENTS_IN_RING_ELEMENT * BITS_PER_COEFFICIENT) / 8;
    pub(super) const VECTOR_U_COMPRESSION_FACTOR: usize = 11;
    // [hax]: hacspec/hacspec-v2#27 stealing error
    // block_len::<VECTOR_U_COMPRESSION_FACTOR>();
    pub(super) const C1_BLOCK_SIZE: usize =
        (COEFFICIENTS_IN_RING_ELEMENT * VECTOR_U_COMPRESSION_FACTOR) / 8;
    // [hax]: hacspec/hacspec-v2#27 stealing error
    // serialized_len::<RANK, C1_BLOCK_SIZE>();
    pub(super) const C1_SIZE: usize = C1_BLOCK_SIZE * RANK;
    pub(super) const VECTOR_V_COMPRESSION_FACTOR: usize = 5;
    // [hax]: hacspec/hacspec-v2#27 stealing error
    // block_len::<VECTOR_V_COMPRESSION_FACTOR>()
    pub(super) const C2_SIZE: usize =
        (COEFFICIENTS_IN_RING_ELEMENT * VECTOR_V_COMPRESSION_FACTOR) / 8;
    pub(super) const CPA_PKE_SECRET_KEY_SIZE: usize =
        (RANK * COEFFICIENTS_IN_RING_ELEMENT * BITS_PER_COEFFICIENT) / 8;
    pub(crate) const CPA_PKE_PUBLIC_KEY_SIZE: usize = T_AS_NTT_ENCODED_SIZE + 32;
    pub(super) const CPA_PKE_CIPHERTEXT_SIZE: usize = C1_SIZE + C2_SIZE;
    pub(crate) const SECRET_KEY_SIZE: usize =
        CPA_PKE_SECRET_KEY_SIZE + CPA_PKE_PUBLIC_KEY_SIZE + H_DIGEST_SIZE + SHARED_SECRET_SIZE;

    pub(super) const ETA1: usize = 2;
    pub(super) const ETA1_RANDOMNESS_SIZE: usize = ETA1 * 64;
    pub(super) const ETA2: usize = 2;
    pub(super) const ETA2_RANDOMNESS_SIZE: usize = ETA2 * 64;

    pub(super) const IMPLICIT_REJECTION_HASH_INPUT_SIZE: usize =
        SHARED_SECRET_SIZE + CPA_PKE_CIPHERTEXT_SIZE;
}

#[ml_kem_variants(
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
pub mod mlkem {
    // For the case where we didn't compile with the simd128/simd256 features but
    // have a CPU that has it and thus tries to call the simd128/simd256 version,
    // we fall back to the portable version in this case.

    #[cfg(feature = "simd256")]
    use instantiations::avx2::{
        decapsulate as decapsulate_avx2, encapsulate as encapsulate_avx2,
        generate_keypair as generate_keypair_avx2,
    };

    #[cfg(feature = "simd128")]
    use instantiations::neon::{
        decapsulate as decapsulate_neon, encapsulate as encapsulate_neon,
        generate_keypair as generate_keypair_neon,
    };

    #[cfg(not(feature = "simd256"))]
    use instantiations::portable::{
        decapsulate as decapsulate_avx2, encapsulate as encapsulate_avx2,
        generate_keypair as generate_keypair_avx2,
    };

    #[cfg(not(feature = "simd128"))]
    use instantiations::portable::{
        decapsulate as decapsulate_neon, encapsulate as encapsulate_neon,
        generate_keypair as generate_keypair_neon,
    };

    #[cfg(all(feature = "simd256", feature = "kyber"))]
    use instantiations::avx2::{
        kyber_decapsulate as kyber_decapsulate_avx2, kyber_encapsulate as kyber_encapsulate_avx2,
        kyber_generate_keypair as kyber_generate_keypair_avx2,
    };

    #[cfg(all(feature = "simd128", feature = "kyber"))]
    use instantiations::neon::{
        kyber_decapsulate as kyber_decapsulate_neon, kyber_encapsulate as kyber_encapsulate_neon,
        kyber_generate_keypair as kyber_generate_keypair_neon,
    };

    #[cfg(all(not(feature = "simd256"), feature = "kyber"))]
    use instantiations::portable::{
        kyber_decapsulate as kyber_decapsulate_avx2, kyber_encapsulate as kyber_encapsulate_avx2,
        kyber_generate_keypair as kyber_generate_keypair_avx2,
    };

    #[cfg(all(not(feature = "simd128"), feature = "kyber"))]
    use instantiations::portable::{
        kyber_decapsulate as kyber_decapsulate_neon, kyber_encapsulate as kyber_encapsulate_neon,
        kyber_generate_keypair as kyber_generate_keypair_neon,
    };

    #[hax_lib::requires(fstar!(r#"Spec.MLKEM.is_rank $K /\
    $RANKED_BYTES_PER_RING_ELEMENT == Spec.MLKEM.v_RANKED_BYTES_PER_RING_ELEMENT $K /\
    $PUBLIC_KEY_SIZE == Spec.MLKEM.v_CCA_PUBLIC_KEY_SIZE $K"#))]
    #[inline(always)]
    pub(crate) fn validate_public_key<
        const K: usize,
        const RANKED_BYTES_PER_RING_ELEMENT: usize,
        const PUBLIC_KEY_SIZE: usize,
    >(
        public_key: &[u8; PUBLIC_KEY_SIZE],
    ) -> bool {
        instantiations::portable::validate_public_key::<
            K,
            RANKED_BYTES_PER_RING_ELEMENT,
            PUBLIC_KEY_SIZE,
        >(public_key)
    }

    #[inline(always)]
    #[hax_lib::requires(fstar!(r#"Spec.MLKEM.is_rank $K /\
                $SECRET_KEY_SIZE == Spec.MLKEM.v_CCA_PRIVATE_KEY_SIZE $K /\
                $CIPHERTEXT_SIZE == Spec.MLKEM.v_CPA_CIPHERTEXT_SIZE $K"#))]
    pub(crate) fn validate_private_key<
        const K: usize,
        const SECRET_KEY_SIZE: usize,
        const CIPHERTEXT_SIZE: usize,
    >(
        private_key: &MlKemPrivateKey<SECRET_KEY_SIZE>,
        ciphertext: &MlKemCiphertext<CIPHERTEXT_SIZE>,
    ) -> bool {
        instantiations::portable::validate_private_key::<K, SECRET_KEY_SIZE, CIPHERTEXT_SIZE>(
            private_key,
            ciphertext,
        )
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
        // Runtime feature detection.
        if libcrux_platform::simd256_support() {
            kyber_generate_keypair_avx2::<
                K,
                CPA_PRIVATE_KEY_SIZE,
                PRIVATE_KEY_SIZE,
                PUBLIC_KEY_SIZE,
                BYTES_PER_RING_ELEMENT,
                ETA1,
                ETA1_RANDOMNESS_SIZE,
            >(randomness)
        } else if libcrux_platform::simd128_support() {
            kyber_generate_keypair_neon::<
                K,
                CPA_PRIVATE_KEY_SIZE,
                PRIVATE_KEY_SIZE,
                PUBLIC_KEY_SIZE,
                BYTES_PER_RING_ELEMENT,
                ETA1,
                ETA1_RANDOMNESS_SIZE,
            >(randomness)
        } else {
            instantiations::portable::kyber_generate_keypair::<
                K,
                CPA_PRIVATE_KEY_SIZE,
                PRIVATE_KEY_SIZE,
                PUBLIC_KEY_SIZE,
                BYTES_PER_RING_ELEMENT,
                ETA1,
                ETA1_RANDOMNESS_SIZE,
            >(randomness)
        }
    }

    #[hax_lib::requires(fstar!(r#"Spec.MLKEM.is_rank $K /\
    $CPA_PRIVATE_KEY_SIZE == Spec.MLKEM.v_CPA_PRIVATE_KEY_SIZE $K /\
    $PRIVATE_KEY_SIZE == Spec.MLKEM.v_CCA_PRIVATE_KEY_SIZE $K /\
    $PUBLIC_KEY_SIZE == Spec.MLKEM.v_CPA_PUBLIC_KEY_SIZE $K /\
    $RANKED_BYTES_PER_RING_ELEMENT == Spec.MLKEM.v_RANKED_BYTES_PER_RING_ELEMENT $K /\
    $ETA1 == Spec.MLKEM.v_ETA1 $K /\
    $ETA1_RANDOMNESS_SIZE == Spec.MLKEM.v_ETA1_RANDOMNESS_SIZE $K"#))]
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
        // Runtime feature detection.
        if libcrux_platform::simd256_support() {
            generate_keypair_avx2::<
                K,
                CPA_PRIVATE_KEY_SIZE,
                PRIVATE_KEY_SIZE,
                PUBLIC_KEY_SIZE,
                RANKED_BYTES_PER_RING_ELEMENT,
                ETA1,
                ETA1_RANDOMNESS_SIZE,
            >(randomness)
        } else if libcrux_platform::simd128_support() {
            generate_keypair_neon::<
                K,
                CPA_PRIVATE_KEY_SIZE,
                PRIVATE_KEY_SIZE,
                PUBLIC_KEY_SIZE,
                RANKED_BYTES_PER_RING_ELEMENT,
                ETA1,
                ETA1_RANDOMNESS_SIZE,
            >(randomness)
        } else {
            instantiations::portable::generate_keypair::<
                K,
                CPA_PRIVATE_KEY_SIZE,
                PRIVATE_KEY_SIZE,
                PUBLIC_KEY_SIZE,
                RANKED_BYTES_PER_RING_ELEMENT,
                ETA1,
                ETA1_RANDOMNESS_SIZE,
            >(randomness)
        }
    }

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
        if libcrux_platform::simd256_support() {
            kyber_encapsulate_avx2::<
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
            >(public_key, randomness)
        } else if libcrux_platform::simd128_support() {
            kyber_encapsulate_neon::<
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
            >(public_key, randomness)
        } else {
            instantiations::portable::kyber_encapsulate::<
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
            >(public_key, randomness)
        }
    }

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
        if libcrux_platform::simd256_support() {
            encapsulate_avx2::<
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
            >(public_key, randomness)
        } else if libcrux_platform::simd128_support() {
            encapsulate_neon::<
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
            >(public_key, randomness)
        } else {
            instantiations::portable::encapsulate::<
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
            >(public_key, randomness)
        }
    }

    #[cfg(feature = "kyber")]
    pub(crate) fn kyber_decapsulate<
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
        if libcrux_platform::simd256_support() {
            kyber_decapsulate_avx2::<
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
            >(private_key, ciphertext)
        } else if libcrux_platform::simd128_support() {
            kyber_decapsulate_neon::<
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
            >(private_key, ciphertext)
        } else {
            instantiations::portable::kyber_decapsulate::<
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
            >(private_key, ciphertext)
        }
    }

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
        private_key: &MlKemPrivateKey<SECRET_KEY_SIZE>,
        ciphertext: &MlKemCiphertext<CIPHERTEXT_SIZE>,
    ) -> MlKemSharedSecret {
        if libcrux_platform::simd256_support() {
            decapsulate_avx2::<
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
            >(private_key, ciphertext)
        } else if libcrux_platform::simd128_support() {
            decapsulate_neon::<
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
            >(private_key, ciphertext)
        } else {
            instantiations::portable::decapsulate::<
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
            >(private_key, ciphertext)
        }
    }
}
