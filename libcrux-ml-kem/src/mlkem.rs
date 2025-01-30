//! Top level entry points for ML-KEM

// This should be replaced with a nicer proc macro later.

macro_rules! impl_incr_key_size {
    () => {
        use crate::ind_cca::incremental::multiplexing;

        use self::incremental::types::{self, Error, State};
        pub use self::incremental::types::{PublicKey1, PublicKey2};

        use super::*;
        use ind_cca::incremental::{self, types::Keys};

        /// Ciphertext 1
        pub type Ciphertext1 = types::Ciphertext1<C1_SIZE>;

        /// Ciphertext 2
        pub type Ciphertext2 = types::Ciphertext2<C2_SIZE>;

        /// Get the size of the first public key in bytes.
        pub const fn pk1_len() -> usize {
            PublicKey1::len()
        }

        /// Get the size of the second public key in bytes.
        pub const fn pk2_len() -> usize {
            // 1184
            // 3 * 16 * 32 = 1536
            // uncompressed: RANK * 16 * 32
            RANKED_BYTES_PER_RING_ELEMENT
        }

        /// The size of the key pair in bytes.
        pub const fn key_pair_len() -> usize {
            // Because const generics are too limited, we compute it here from scratch.

            // PK1
            pk1_len()
            // PK2
            + pk2_len()
            // SK
            + RANK * 16 * 32 + 32
            // Matrix
            + RANK * RANK * 16 * 32
        }

        /// The size of the encaps state in bytes.
        pub const fn encaps_state_len() -> usize {
            // Because const generics are too limited, we compute it here from scratch.

            // r_as_ntt
            RANK * 16 * 32
            // error2
            + 16 * 32
            // randomness
            + 32
        }

        /// Functions in this module require an allocator to use [`Box`].
        ///
        /// Instead of serializing keys and state, the functions in this module return
        /// the platform dependent keys and state types for immediate use.
        #[cfg(feature = "alloc")]
        pub mod alloc {
            use super::*;

            use ::alloc::boxed::Box;

            /// Generate a new key pair for incremental encapsulation.
            pub fn generate_key_pair(randomness: [u8; KEY_GENERATION_SEED_SIZE]) -> Box<dyn Keys> {
                multiplexing::alloc::generate_keypair::<
                    RANK,
                    CPA_PKE_SECRET_KEY_SIZE,
                    SECRET_KEY_SIZE,
                    CPA_PKE_PUBLIC_KEY_SIZE,
                    RANKED_BYTES_PER_RING_ELEMENT,
                    ETA1,
                    ETA1_RANDOMNESS_SIZE,
                >(randomness)
            }

            /// Encapsulate the first part of the ciphertext.
            pub fn encapsulate1(
                public_key_part: &PublicKey1,
                randomness: [u8; SHARED_SECRET_SIZE],
            ) -> (Ciphertext1, Box<dyn State>, [u8; SHARED_SECRET_SIZE]) {
                multiplexing::alloc::encapsulate1::<
                    RANK,
                    CPA_PKE_CIPHERTEXT_SIZE,
                    C1_SIZE,
                    VECTOR_U_COMPRESSION_FACTOR,
                    C1_BLOCK_SIZE,
                    ETA1,
                    ETA1_RANDOMNESS_SIZE,
                    ETA2,
                    ETA2_RANDOMNESS_SIZE,
                >(public_key_part, randomness)
            }

            /// Encapsulate the second part of the ciphertext.
            ///
            /// The second part of the public key is passed in as byte slice.
            /// [`Error::InvalidInputLength`] is returned if `public_key_part` is too
            /// short.
            pub fn encapsulate2(state: &dyn State, public_key_part: &[u8]) -> Result<Ciphertext2, Error> {
                multiplexing::alloc::encapsulate2::<RANK, RANKED_BYTES_PER_RING_ELEMENT, C2_SIZE, VECTOR_V_COMPRESSION_FACTOR>(
                    state,
                    public_key_part,
                )
            }

            /// Decapsulate incremental ciphertexts.
            pub fn decapsulate(
                private_key: &dyn Keys,
                ciphertext1: &Ciphertext1,
                ciphertext2: &Ciphertext2,
            ) -> MlKemSharedSecret {
                multiplexing::alloc::decapsulate::<
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
                >(private_key, ciphertext1, ciphertext2)
            }
        }

        /// Generate a key pair and write it into `key_pair`.
        ///
        /// `key_pair.len()` must be of size `key_pair_len()`.
        pub fn generate_key_pair(randomness: [u8; KEY_GENERATION_SEED_SIZE], key_pair: &mut [u8]) -> Result<(), Error> {
            multiplexing::generate_keypair::<
                RANK,
                RANKED_BYTES_PER_RING_ELEMENT,
                CPA_PKE_SECRET_KEY_SIZE,
                SECRET_KEY_SIZE,
                CPA_PKE_PUBLIC_KEY_SIZE,
                RANKED_BYTES_PER_RING_ELEMENT,
                ETA1,
                ETA1_RANDOMNESS_SIZE,
            >(randomness, key_pair)
        }

        /// Validate that the two parts `pk1` and `pk2` are consistent.
        pub fn validate_pk(
            pk1: &PublicKey1,
            pk2: &[u8],
        ) -> Result<(), Error> {
            multiplexing::validate_pk::<RANK,  CPA_PKE_PUBLIC_KEY_SIZE>(pk1, pk2)
        }

        /// Encapsulate the first part of the ciphertext.
        ///
        /// Returns an [`Error`] if the provided input or output don't have
        /// the appropriate sizes.
        pub fn encapsulate1(
            pk1: &[u8],
            randomness: [u8; SHARED_SECRET_SIZE],
            state: &mut [u8],
            shared_secret: &mut [u8],
        ) -> Result<Ciphertext1, Error> {
            let public_key_part = PublicKey1::try_from(&pk1 as &[u8])?;

            multiplexing::encapsulate1::<
                RANK,
                CPA_PKE_CIPHERTEXT_SIZE,
                C1_SIZE,
                VECTOR_U_COMPRESSION_FACTOR,
                C1_BLOCK_SIZE,
                ETA1,
                ETA1_RANDOMNESS_SIZE,
                ETA2,
                ETA2_RANDOMNESS_SIZE,
            >(&public_key_part, randomness, state, shared_secret)
        }

        /// Encapsulate the second part of the ciphertext.
        ///
        /// The second part of the public key is passed in as byte slice.
        /// [`Error::InvalidInputLength`] is returned if `public_key_part` is too
        /// short.
        pub fn encapsulate2(state: &[u8], public_key_part: &[u8]) -> Result<Ciphertext2, Error> {
            multiplexing::encapsulate2::<RANK, RANKED_BYTES_PER_RING_ELEMENT, C2_SIZE, VECTOR_V_COMPRESSION_FACTOR>(state, public_key_part)
        }

        /// Decapsulate incremental ciphertexts.
        pub fn decapsulate_incremental_key(
            private_key: &[u8],
            ciphertext1: &Ciphertext1,
            ciphertext2: &Ciphertext2,
        ) -> Result<MlKemSharedSecret, Error> {
            multiplexing::decapsulate::<
                RANK,
                RANKED_BYTES_PER_RING_ELEMENT,
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
            >(private_key, ciphertext1, ciphertext2)
        }

    };
}
pub(crate) use impl_incr_key_size;

macro_rules! impl_incr_platform {
    ($vector:path, $hash:path) => {
        /// Downcast [`Keys`] to a platform dependent [`MlKemKeyPairUnpacked`].
        ///
        /// **PANICS** is the cast fails
        pub(super) fn as_keypair<const K: usize>(k: &dyn Any) -> &MlKemKeyPairUnpacked<K, $vector> {
            k.downcast_ref().unwrap()
        }

        /// Downcast [`State`] to a  platform dependent [`EncapsState`].
        ///
        /// **PANICS** is the cast fails
        pub(super) fn as_state<const K: usize>(s: &dyn Any) -> &EncapsState<K, $vector> {
            s.downcast_ref().unwrap()
        }

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
        ) -> MlKemKeyPairUnpacked<K, $vector> {
            super::generate_keypair::<
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

        pub(crate) fn generate_keypair_serialized<
            const K: usize,
            const PK2_LEN: usize,
            const CPA_PRIVATE_KEY_SIZE: usize,
            const PRIVATE_KEY_SIZE: usize,
            const PUBLIC_KEY_SIZE: usize,
            const BYTES_PER_RING_ELEMENT: usize,
            const ETA1: usize,
            const ETA1_RANDOMNESS_SIZE: usize,
        >(
            randomness: [u8; KEY_GENERATION_SEED_SIZE],
            key_pair: &mut [u8],
        ) -> Result<(), Error> {
            if key_pair.len() < KeyPair::<K, PK2_LEN, $vector>::num_bytes() {
                return Err(Error::InvalidOutputLength);
            }

            super::generate_keypair_serialized::<
                K,
                PK2_LEN,
                CPA_PRIVATE_KEY_SIZE,
                PRIVATE_KEY_SIZE,
                PUBLIC_KEY_SIZE,
                BYTES_PER_RING_ELEMENT,
                ETA1,
                ETA1_RANDOMNESS_SIZE,
                $vector,
                $hash,
            >(randomness, key_pair)
        }

        pub(crate) fn validate_pk<const K: usize, const PK_LEN: usize>(
            pk1: &PublicKey1,
            pk2: &[u8],
        ) -> Result<(), Error> {
            super::validate_pk::<K, PK_LEN, $hash>(pk1, pk2)
        }

        pub(crate) fn encapsulate1<
            const K: usize,
            const CIPHERTEXT_SIZE: usize,
            const C1_SIZE: usize,
            const VECTOR_U_COMPRESSION_FACTOR: usize,
            const VECTOR_U_BLOCK_LEN: usize,
            const ETA1: usize,
            const ETA1_RANDOMNESS_SIZE: usize,
            const ETA2: usize,
            const ETA2_RANDOMNESS_SIZE: usize,
        >(
            public_key_part: &PublicKey1,
            randomness: [u8; SHARED_SECRET_SIZE],
        ) -> (
            Ciphertext1<C1_SIZE>,
            EncapsState<K, $vector>,
            [u8; SHARED_SECRET_SIZE],
        ) {
            super::encapsulate1::<
                K,
                CIPHERTEXT_SIZE,
                C1_SIZE,
                VECTOR_U_COMPRESSION_FACTOR,
                VECTOR_U_BLOCK_LEN,
                ETA1,
                ETA1_RANDOMNESS_SIZE,
                ETA2,
                ETA2_RANDOMNESS_SIZE,
                $vector,
                $hash,
            >(public_key_part, randomness)
        }

        pub(crate) fn encapsulate1_serialized<
            const K: usize,
            const CIPHERTEXT_SIZE: usize,
            const C1_SIZE: usize,
            const VECTOR_U_COMPRESSION_FACTOR: usize,
            const VECTOR_U_BLOCK_LEN: usize,
            const ETA1: usize,
            const ETA1_RANDOMNESS_SIZE: usize,
            const ETA2: usize,
            const ETA2_RANDOMNESS_SIZE: usize,
        >(
            public_key_part: &PublicKey1,
            randomness: [u8; SHARED_SECRET_SIZE],
            state: &mut [u8],
            shared_secret: &mut [u8],
        ) -> Result<Ciphertext1<C1_SIZE>, Error> {
            super::encapsulate1_serialized::<
                K,
                CIPHERTEXT_SIZE,
                C1_SIZE,
                VECTOR_U_COMPRESSION_FACTOR,
                VECTOR_U_BLOCK_LEN,
                ETA1,
                ETA1_RANDOMNESS_SIZE,
                ETA2,
                ETA2_RANDOMNESS_SIZE,
                $vector,
                $hash,
            >(public_key_part, randomness, state, shared_secret)
        }

        pub(crate) fn encapsulate2<
            const K: usize,
            const PK2_LEN: usize,
            const C2_SIZE: usize,
            const VECTOR_V_COMPRESSION_FACTOR: usize,
        >(
            state: &EncapsState<K, $vector>,
            public_key_part: &PublicKey2<PK2_LEN>,
        ) -> Ciphertext2<C2_SIZE> {
            super::encapsulate2::<K, PK2_LEN, C2_SIZE, VECTOR_V_COMPRESSION_FACTOR, $vector>(
                state,
                public_key_part,
            )
        }

        pub(crate) fn encapsulate2_serialized<
            const K: usize,
            const PK2_LEN: usize,
            const C2_SIZE: usize,
            const VECTOR_V_COMPRESSION_FACTOR: usize,
        >(
            state: &[u8],
            public_key_part: &PublicKey2<PK2_LEN>,
        ) -> Result<Ciphertext2<C2_SIZE>, Error> {
            super::encapsulate2_serialized::<
                K,
                PK2_LEN,
                C2_SIZE,
                VECTOR_V_COMPRESSION_FACTOR,
                $vector,
            >(state, public_key_part)
        }

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
            private_key: &MlKemKeyPairUnpacked<K, $vector>,
            ciphertext1: &Ciphertext1<C1_SIZE>,
            ciphertext2: &Ciphertext2<C2_SIZE>,
        ) -> MlKemSharedSecret {
            super::decapsulate::<
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
            >(private_key, ciphertext1, ciphertext2)
        }

        pub(crate) fn decapsulate_incremental_key<
            const K: usize,
            const PK2_LEN: usize,
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
            private_key: &[u8],
            ciphertext1: &Ciphertext1<C1_SIZE>,
            ciphertext2: &Ciphertext2<C2_SIZE>,
        ) -> Result<MlKemSharedSecret, Error> {
            super::decapsulate_incremental_key::<
                K,
                PK2_LEN,
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
            >(private_key, ciphertext1, ciphertext2)
        }
    };
}
pub(crate) use impl_incr_platform;
