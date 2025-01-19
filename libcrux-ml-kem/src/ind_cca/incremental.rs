//! Incremental API.
//!
//! **WARNING:** This API is not standard compliant and may lead to insecure
//! usage. Use at your own risk.

use crate::{
    hash_functions::Hash,
    ind_cpa::{self, deserialize_secret_key, serialize_secret_key},
    matrix::sample_matrix_A,
    polynomial::PolynomialRingElement,
    utils::into_padded_array,
    variant, SHARED_SECRET_SIZE,
};

use super::{
    unpacked::{encaps_prepare, MlKemKeyPairUnpacked, MlKemPublicKeyUnpacked},
    MlKemSharedSecret, Operations, KEY_GENERATION_SEED_SIZE,
};

pub mod types {
    use core::any::Any;

    use super::*;
    use crate::ind_cca::unpacked::MlKemKeyPairUnpacked;

    /// Errors
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub enum Error {
        /// Invalid input byte length
        InvalidInputLength,

        /// Invalid output byte length
        InvalidOutputLength,
    }

    /// Incremental trait for unpacked key pairs.
    //<const K: usize, Vector: Operations>
    pub trait IncrementalKeyPair {
        /// Get the [`PublicKey1`] from this key pair as bytes.
        ///
        /// The output `bytes` have to be at least 64 bytes long.
        ///
        /// **PANICS:** if the output `bytes` are too short.
        fn pk1_bytes(&self, bytes: &mut [u8]);

        /// Get the [`PublicKey2`] from this key pair as bytes.
        ///
        /// The output `bytes` have to be at least K * 16 * 32 bytes long.
        ///
        /// **PANICS:** if the output `bytes` are too short.
        fn pk2_bytes(&self, bytes: &mut [u8]);
    }

    impl<const K: usize, Vector: Operations> IncrementalKeyPair for MlKemKeyPairUnpacked<K, Vector> {
        fn pk1_bytes(&self, bytes: &mut [u8]) {
            bytes[0..32].copy_from_slice(&self.public_key().ind_cpa_public_key.seed_for_A);
            bytes[32..64].copy_from_slice(&self.public_key().public_key_hash);
        }

        fn pk2_bytes(&self, bytes: &mut [u8]) {
            let len = K * 16 * 32;
            serialize_secret_key(
                &self.public_key.ind_cpa_public_key.t_as_ntt,
                &mut bytes[0..len],
            )
        }
    }

    /// The incremental public key that allows generating [`Ciphertext1`].
    #[derive(Default)]
    pub struct PublicKey1 {
        pub(super) seed: [u8; 32],
        pub(super) hash: [u8; 32],
    }

    impl TryFrom<&[u8]> for PublicKey1 {
        type Error = Error;

        fn try_from(value: &[u8]) -> Result<Self, Self::Error> {
            if value.len() < 64 {
                return Err(Error::InvalidInputLength);
            }

            let mut seed = [0u8; 32];
            seed.copy_from_slice(&value[0..32]);
            let mut hash = [0u8; 32];
            hash.copy_from_slice(&value[32..64]);
            Ok(Self { seed, hash })
        }
    }

    impl From<&[u8; 64]> for PublicKey1 {
        fn from(value: &[u8; 64]) -> Self {
            let mut seed = [0u8; 32];
            seed.copy_from_slice(&value[0..32]);
            let mut hash = [0u8; 32];
            hash.copy_from_slice(&value[32..64]);
            Self { seed, hash }
        }
    }

    /// The incremental public key that allows generating [`Ciphertext2`].
    #[repr(transparent)]
    pub struct PublicKey2<const K: usize, Vector: Operations> {
        pub(super) t_as_ntt: [PolynomialRingElement<Vector>; K],
    }

    /// Trait container for multiplexing over platform dependent [`MlKemKeyPairUnpacked`].
    pub trait Keys: IncrementalKeyPair {
        fn as_any(&self) -> &dyn Any;
    }
    impl<const K: usize, Vector: Operations + 'static> Keys for MlKemKeyPairUnpacked<K, Vector> {
        fn as_any(&self) -> &dyn Any {
            self
        }
    }

    /// The partial ciphertext c1 - first part.
    #[repr(transparent)]
    pub struct Ciphertext1<const LEN: usize> {
        pub value: [u8; LEN],
    }

    /// The partial ciphertext c2 - second part.
    #[repr(transparent)]
    pub struct Ciphertext2<const LEN: usize> {
        pub value: [u8; LEN],
    }

    /// The incremental state for encapsulate.
    pub struct EncapsState<const K: usize, Vector: Operations> {
        pub(super) shared_secret: MlKemSharedSecret,
        pub(super) r_as_ntt: [PolynomialRingElement<Vector>; K],
        pub(super) error2: PolynomialRingElement<Vector>,
        pub(super) randomness: [u8; 32],
    }

    /// Trait container for multiplexing over platform dependent [`EncapsState`].
    pub trait State {
        fn as_any(&self) -> &dyn Any;

        /// Get the shared secret.
        fn shared_secret(&self) -> &[u8];
    }
    impl<const K: usize, Vector: Operations + 'static> State for EncapsState<K, Vector> {
        fn as_any(&self) -> &dyn Any {
            self
        }

        fn shared_secret(&self) -> &[u8] {
            &self.shared_secret
        }
    }

    // === Implementations

    /// Convert [`MlKemPublicKeyUnpacked`] to a [`PublicKey1`]
    impl<const K: usize, Vector: Operations> From<&MlKemPublicKeyUnpacked<K, Vector>> for PublicKey1 {
        fn from(pk: &MlKemPublicKeyUnpacked<K, Vector>) -> Self {
            Self {
                seed: pk.ind_cpa_public_key.seed_for_A,
                hash: pk.public_key_hash,
            }
        }
    }

    /// Convert [`MlKemPublicKeyUnpacked`] to a [`PublicKey2`].
    impl<const K: usize, Vector: Operations> From<&MlKemPublicKeyUnpacked<K, Vector>>
        for PublicKey2<K, Vector>
    {
        fn from(pk: &MlKemPublicKeyUnpacked<K, Vector>) -> Self {
            Self {
                t_as_ntt: pk.ind_cpa_public_key.t_as_ntt,
            }
        }
    }

    /// Convert a byte slice `&[u8]` to a [`PublicKey2`].
    impl<const K: usize, Vector: Operations> TryFrom<&[u8]> for PublicKey2<K, Vector> {
        type Error = Error;

        fn try_from(value: &[u8]) -> Result<Self, Self::Error> {
            if value.len() < K * 15 * 32 {
                return Err(Error::InvalidInputLength);
            }

            Ok(Self {
                t_as_ntt: deserialize_secret_key(value),
            })
        }
    }
}

use types::*;

pub(crate) mod portable {
    use core::any::Any;

    use super::*;
    type Vector = crate::vector::portable::PortableVector;
    type Hash<const K: usize> = crate::hash_functions::portable::PortableHash<K>;

    /// Downcast [`Keys`] to a portable [`MlKemKeyPairUnpacked`].
    ///
    /// **PANICS** is the cast fails
    pub(super) fn as_portable_keypair<const K: usize>(
        k: &dyn Any,
    ) -> &MlKemKeyPairUnpacked<K, Vector> {
        k.downcast_ref().unwrap()
    }

    /// Downcast [`State`] to a portable [`EncapsState`].
    ///
    /// **PANICS** is the cast fails
    pub(super) fn as_portable_state<const K: usize>(s: &dyn Any) -> &EncapsState<K, Vector> {
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
    ) -> MlKemKeyPairUnpacked<K, Vector> {
        super::generate_keypair::<
            K,
            CPA_PRIVATE_KEY_SIZE,
            PRIVATE_KEY_SIZE,
            PUBLIC_KEY_SIZE,
            BYTES_PER_RING_ELEMENT,
            ETA1,
            ETA1_RANDOMNESS_SIZE,
            Vector,
            Hash<K>,
        >(randomness)
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
    ) -> (Ciphertext1<C1_SIZE>, EncapsState<K, Vector>) {
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
            Vector,
            Hash<K>,
        >(public_key_part, randomness)
    }

    pub(crate) fn encapsulate2<
        const K: usize,
        const C2_SIZE: usize,
        const VECTOR_V_COMPRESSION_FACTOR: usize,
    >(
        state: &EncapsState<K, Vector>,
        public_key_part: &PublicKey2<K, Vector>,
    ) -> Ciphertext2<C2_SIZE> {
        super::encapsulate2::<K, C2_SIZE, VECTOR_V_COMPRESSION_FACTOR, Vector>(
            state,
            public_key_part,
        )
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
        private_key: &MlKemKeyPairUnpacked<K, Vector>,
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
            Vector,
            Hash<K>,
        >(private_key, ciphertext1, ciphertext2)
    }
}

#[cfg(feature = "simd128")]
pub(crate) mod neon {
    use super::*;
    type Vector = crate::vector::SIMD128Vector;
    type Hash = crate::hash_functions::neon::Simd128Hash;

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
    ) -> (Ciphertext1<C1_SIZE>, EncapsState<K, Vector>) {
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
            Vector,
            Hash,
        >(public_key_part, randomness)
    }
}

#[cfg(feature = "simd256")]
pub(crate) mod avx2 {
    use core::any::Any;

    use super::*;
    type Vector = crate::vector::SIMD256Vector;
    type Hash = crate::hash_functions::avx2::Simd256Hash;

    /// Downcast [`Keys`] to an AVX2 [`MlKemKeyPairUnpacked`].
    ///
    /// **PANICS** is the cast fails
    pub(super) fn as_avx2_keypair<const K: usize>(k: &dyn Any) -> &MlKemKeyPairUnpacked<K, Vector> {
        k.downcast_ref().unwrap()
    }

    /// Downcast [`State`] to an AVX2 [`EncapsState`].
    ///
    /// **PANICS** is the cast fails
    pub(super) fn as_avx2_state<const K: usize>(s: &dyn Any) -> &EncapsState<K, Vector> {
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
    ) -> MlKemKeyPairUnpacked<K, Vector> {
        super::generate_keypair::<
            K,
            CPA_PRIVATE_KEY_SIZE,
            PRIVATE_KEY_SIZE,
            PUBLIC_KEY_SIZE,
            BYTES_PER_RING_ELEMENT,
            ETA1,
            ETA1_RANDOMNESS_SIZE,
            Vector,
            Hash,
        >(randomness)
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
    ) -> (Ciphertext1<C1_SIZE>, EncapsState<K, Vector>) {
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
            Vector,
            Hash,
        >(public_key_part, randomness)
    }

    pub(crate) fn encapsulate2<
        const K: usize,
        const C2_SIZE: usize,
        const VECTOR_V_COMPRESSION_FACTOR: usize,
    >(
        state: &EncapsState<K, Vector>,
        public_key_part: &PublicKey2<K, Vector>,
    ) -> Ciphertext2<C2_SIZE> {
        super::encapsulate2::<K, C2_SIZE, VECTOR_V_COMPRESSION_FACTOR, Vector>(
            state,
            public_key_part,
        )
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
        private_key: &MlKemKeyPairUnpacked<K, Vector>,
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
            Vector,
            Hash,
        >(private_key, ciphertext1, ciphertext2)
    }
}

/// Multiplexing incremental API.
///
/// Note that this requires alloc support and is not `no_std` compatible
#[cfg(feature = "alloc")]
pub(crate) mod multiplexing {
    use super::*;

    extern crate alloc;
    use alloc::boxed::Box;

    #[cfg(feature = "simd256")]
    use avx2::{
        as_avx2_keypair, as_avx2_state, decapsulate as decapsulate_avx2,
        encapsulate1 as encapsulate1_avx2, encapsulate2 as encapsulate2_avx2,
        generate_keypair as generate_keypair_avx2,
    };

    // #[cfg(feature = "simd128")]
    // use neon::{
    //     decapsulate as decapsulate_neon, encapsulate as encapsulate_neon,
    //     generate_keypair as generate_keypair_neon,
    // };

    // #[cfg(not(feature = "simd256"))]
    // use portable::{
    //     decapsulate as decapsulate_avx2, encapsulate as encapsulate_avx2,
    //     generate_keypair as generate_keypair_avx2,
    // };

    #[cfg(not(feature = "simd128"))]
    use portable::{
        as_portable_keypair as as_neon_keypair, as_portable_state as as_neon_state,
        decapsulate as decapsulate_neon, encapsulate1 as encapsulate1_neon,
        encapsulate2 as encapsulate2_neon, generate_keypair as generate_keypair_neon,
    };

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
    ) -> Box<dyn Keys> {
        if libcrux_platform::simd256_support() {
            Box::new(generate_keypair_avx2::<
                K,
                CPA_PRIVATE_KEY_SIZE,
                PRIVATE_KEY_SIZE,
                PUBLIC_KEY_SIZE,
                BYTES_PER_RING_ELEMENT,
                ETA1,
                ETA1_RANDOMNESS_SIZE,
            >(randomness))
        } else if libcrux_platform::simd128_support() {
            Box::new(generate_keypair_neon::<
                K,
                CPA_PRIVATE_KEY_SIZE,
                PRIVATE_KEY_SIZE,
                PUBLIC_KEY_SIZE,
                BYTES_PER_RING_ELEMENT,
                ETA1,
                ETA1_RANDOMNESS_SIZE,
            >(randomness))
        } else {
            Box::new(portable::generate_keypair::<
                K,
                CPA_PRIVATE_KEY_SIZE,
                PRIVATE_KEY_SIZE,
                PUBLIC_KEY_SIZE,
                BYTES_PER_RING_ELEMENT,
                ETA1,
                ETA1_RANDOMNESS_SIZE,
            >(randomness))
        }
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
    ) -> (Ciphertext1<C1_SIZE>, Box<dyn State>) {
        if libcrux_platform::simd256_support() {
            let (c, s) = encapsulate1_avx2::<
                K,
                CIPHERTEXT_SIZE,
                C1_SIZE,
                VECTOR_U_COMPRESSION_FACTOR,
                VECTOR_U_BLOCK_LEN,
                ETA1,
                ETA1_RANDOMNESS_SIZE,
                ETA2,
                ETA2_RANDOMNESS_SIZE,
            >(public_key_part, randomness);
            (c, Box::new(s))
        } else if libcrux_platform::simd128_support() {
            let (c, s) = encapsulate1_neon::<
                K,
                CIPHERTEXT_SIZE,
                C1_SIZE,
                VECTOR_U_COMPRESSION_FACTOR,
                VECTOR_U_BLOCK_LEN,
                ETA1,
                ETA1_RANDOMNESS_SIZE,
                ETA2,
                ETA2_RANDOMNESS_SIZE,
            >(public_key_part, randomness);
            (c, Box::new(s))
        } else {
            let (c, s) = portable::encapsulate1::<
                K,
                CIPHERTEXT_SIZE,
                C1_SIZE,
                VECTOR_U_COMPRESSION_FACTOR,
                VECTOR_U_BLOCK_LEN,
                ETA1,
                ETA1_RANDOMNESS_SIZE,
                ETA2,
                ETA2_RANDOMNESS_SIZE,
            >(public_key_part, randomness);
            (c, Box::new(s))
        }
    }

    pub(crate) fn encapsulate2<
        const K: usize,
        const C2_SIZE: usize,
        const VECTOR_V_COMPRESSION_FACTOR: usize,
    >(
        state: &dyn State,
        public_key_part: &[u8],
    ) -> Result<Ciphertext2<C2_SIZE>, Error> {
        if libcrux_platform::simd256_support() {
            let state = as_avx2_state(state.as_any());
            let pk2 = PublicKey2::try_from(public_key_part)?;
            Ok(encapsulate2_avx2::<K, C2_SIZE, VECTOR_V_COMPRESSION_FACTOR>(state, &pk2))
        } else if libcrux_platform::simd128_support() {
            let state = as_neon_state(state.as_any());
            let pk2 = PublicKey2::try_from(public_key_part)?;
            Ok(encapsulate2_neon::<K, C2_SIZE, VECTOR_V_COMPRESSION_FACTOR>(state, &pk2))
        } else {
            let state = portable::as_portable_state(state.as_any());
            let pk2 = PublicKey2::try_from(public_key_part)?;
            Ok(portable::encapsulate2::<
                K,
                C2_SIZE,
                VECTOR_V_COMPRESSION_FACTOR,
            >(state, &pk2))
        }
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
        private_key: &dyn Keys,
        ciphertext1: &Ciphertext1<C1_SIZE>,
        ciphertext2: &Ciphertext2<C2_SIZE>,
    ) -> MlKemSharedSecret {
        if libcrux_platform::simd256_support() {
            let private_key = as_avx2_keypair(private_key.as_any());
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
            >(private_key, ciphertext1, ciphertext2)
        } else if libcrux_platform::simd128_support() {
            let private_key = as_neon_keypair(private_key.as_any());
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
            >(private_key, ciphertext1, ciphertext2)
        } else {
            let private_key = portable::as_portable_keypair(private_key.as_any());
            portable::decapsulate::<
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
            >(private_key, ciphertext1, ciphertext2)
        }
    }
}

/// Generate a key pair for incremental encapsulation.
///
/// This generates a regular unpacked key pair [`MlKemKeyPairUnpacked`].
/// The two parts of the public key can be extracted with [`pk1`] and [`pk2`].
///
/// To [`decapsulate`], the entire key pair is used again.
pub(crate) fn generate_keypair<
    const K: usize,
    const CPA_PRIVATE_KEY_SIZE: usize,
    const PRIVATE_KEY_SIZE: usize,
    const PUBLIC_KEY_SIZE: usize,
    const BYTES_PER_RING_ELEMENT: usize,
    const ETA1: usize,
    const ETA1_RANDOMNESS_SIZE: usize,
    Vector: Operations,
    Hasher: Hash<K>,
>(
    randomness: [u8; KEY_GENERATION_SEED_SIZE],
) -> MlKemKeyPairUnpacked<K, Vector> {
    // Generate unpacked key pair.
    let mut kp = MlKemKeyPairUnpacked::new();
    super::unpacked::generate_keypair::<
        K,
        CPA_PRIVATE_KEY_SIZE,
        PRIVATE_KEY_SIZE,
        PUBLIC_KEY_SIZE,
        BYTES_PER_RING_ELEMENT,
        ETA1,
        ETA1_RANDOMNESS_SIZE,
        Vector,
        Hasher,
        variant::MlKem,
    >(randomness, &mut kp);
    kp

    // KeyPair {
    //     pk1: PublicKey1::from(kp.public_key()),
    //     pk2: PublicKey2::from(kp.public_key()),
    //     sk: kp.private_key,
    // }
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
    Vector: Operations,
    Hasher: Hash<K>,
>(
    public_key_part: &PublicKey1,
    randomness: [u8; SHARED_SECRET_SIZE],
) -> (Ciphertext1<C1_SIZE>, EncapsState<K, Vector>) {
    let hashed = encaps_prepare::<K, Hasher>(&randomness, &public_key_part.hash);
    let (shared_secret, pseudorandomness) = hashed.split_at(SHARED_SECRET_SIZE);

    // Rebuild the matrix A from the seed
    let mut matrix = [[PolynomialRingElement::<Vector>::ZERO(); K]; K];
    sample_matrix_A::<K, Vector, Hasher>(
        &mut matrix,
        into_padded_array(&public_key_part.seed),
        false,
    );

    let mut ciphertext = [0u8; C1_SIZE];
    let (r_as_ntt, error2) = ind_cpa::encrypt_c1::<
        K,
        C1_SIZE,
        VECTOR_U_COMPRESSION_FACTOR,
        VECTOR_U_BLOCK_LEN,
        ETA1,
        ETA1_RANDOMNESS_SIZE,
        ETA2,
        ETA2_RANDOMNESS_SIZE,
        Vector,
        Hasher,
    >(&pseudorandomness, &matrix, &mut ciphertext);

    let state = EncapsState {
        randomness,
        shared_secret: shared_secret.try_into().unwrap(),
        r_as_ntt,
        error2,
    };
    (Ciphertext1 { value: ciphertext }, state)
}

pub(crate) fn encapsulate2<
    const K: usize,
    const C2_SIZE: usize,
    const VECTOR_V_COMPRESSION_FACTOR: usize,
    Vector: Operations,
>(
    state: &EncapsState<K, Vector>,
    public_key_part: &PublicKey2<K, Vector>,
) -> Ciphertext2<C2_SIZE> {
    let mut ciphertext = [0u8; C2_SIZE];
    ind_cpa::encrypt_c2::<K, VECTOR_V_COMPRESSION_FACTOR, C2_SIZE, Vector>(
        &public_key_part.t_as_ntt,
        &state.r_as_ntt,
        &state.error2,
        state.randomness,
        &mut ciphertext,
    );

    Ciphertext2 { value: ciphertext }
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
    Vector: Operations,
    Hasher: Hash<K>,
>(
    private_key: &MlKemKeyPairUnpacked<K, Vector>,
    ciphertext1: &Ciphertext1<C1_SIZE>,
    ciphertext2: &Ciphertext2<C2_SIZE>,
) -> MlKemSharedSecret {
    let mut ciphertext = [0u8; CIPHERTEXT_SIZE];
    ciphertext[..C1_SIZE].copy_from_slice(&ciphertext1.value);
    ciphertext[C1_SIZE..].copy_from_slice(&ciphertext2.value);
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
        Vector,
        Hasher,
    >(private_key, &ciphertext.into())
}
