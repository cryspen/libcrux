//! Top level entry points for ML-KEM

// This should be replaced with a nicer proc macro later.

macro_rules! impl_key_size {
    () => {
        use crate::ind_cca::incremental::multiplexing;

        use self::incremental::types::{self, Error, State};
        pub use self::incremental::types::PublicKey1;

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
            RANK * 16 * 32
        }

        /// The size of the key pair in bytes.
        pub const fn key_pair_len() -> usize {
            // Because const generics are too limited, we compute it here from scratch.

            // PK1
            64
            // PK2
            + RANK * 16 * 32
            // SK
            + RANK * 16 * 32 + 32
            // Matrix
            + RANK * RANK * 16 * 32
        }

        /// The size of the encaps state in bytes.
        pub const fn encaps_state_len() -> usize {
            // Because const generics are too limited, we compute it here from scratch.

            // shared secret
            SHARED_SECRET_SIZE
            // r_as_ntt
            + RANK * 16 * 32
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
            ) -> (Ciphertext1, Box<dyn State>) {
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
                multiplexing::alloc::encapsulate2::<RANK, C2_SIZE, VECTOR_V_COMPRESSION_FACTOR>(
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
        pub fn generate_key_pair(randomness: [u8; KEY_GENERATION_SEED_SIZE], key_pair: &mut [u8]) {
            multiplexing::generate_keypair::<
                RANK,
                CPA_PKE_SECRET_KEY_SIZE,
                SECRET_KEY_SIZE,
                CPA_PKE_PUBLIC_KEY_SIZE,
                RANKED_BYTES_PER_RING_ELEMENT,
                ETA1,
                ETA1_RANDOMNESS_SIZE,
            >(randomness, key_pair)
        }

        /// Encapsulate the first part of the ciphertext.
        ///
        /// Returns an [`Error`] if the provided input or output don't have
        /// the appropriate sizes.
        pub fn encapsulate1(
            pk1: &[u8],
            randomness: [u8; SHARED_SECRET_SIZE],
            state: &mut [u8],
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
            >(&public_key_part, randomness, state)
        }

        /// Encapsulate the second part of the ciphertext.
        ///
        /// The second part of the public key is passed in as byte slice.
        /// [`Error::InvalidInputLength`] is returned if `public_key_part` is too
        /// short.
        pub fn encapsulate2(state: &[u8], public_key_part: &[u8]) -> Result<Ciphertext2, Error> {
            multiplexing::encapsulate2::<RANK, C2_SIZE, VECTOR_V_COMPRESSION_FACTOR>(state, public_key_part)
        }

        /// Decapsulate incremental ciphertexts.
        pub fn decapsulate_incremental_key(
            private_key: &[u8],
            ciphertext1: &Ciphertext1,
            ciphertext2: &Ciphertext2,
        ) -> Result<MlKemSharedSecret, Error> {
            multiplexing::decapsulate::<
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

    };
}
pub(crate) use impl_key_size;
