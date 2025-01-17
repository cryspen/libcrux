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
    SHARED_SECRET_SIZE,
};

use super::{
    unpacked::{encaps_prepare, MlKemPrivateKeyUnpacked, MlKemPublicKeyUnpacked},
    MlKemPrivateKey, MlKemSharedSecret, Operations, Variant,
};

mod types {
    use crate::constants::BITS_PER_RING_ELEMENT;

    use super::*;

    /// The incremental public key that allows generating [`Ciphertext1`].
    pub struct PublicKey1 {
        pub(super) seed: [u8; 32],
        pub(super) hash: [u8; 32],
    }

    /// The incremental public key that allows generating [`Ciphertext2`].
    #[repr(transparent)]
    pub struct PublicKey2<const K: usize, Vector: Operations> {
        pub(super) t_as_ntt: [PolynomialRingElement<Vector>; K],
    }

    /// A key pair for incremental encapsulation.
    pub struct KeyPair<const K: usize, Vector: Operations> {
        pub(super) pk1: PublicKey1,
        pub(super) pk2: PublicKey2<K, Vector>,
        pub(super) sk: MlKemPrivateKeyUnpacked<K, Vector>,
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
        pub(super) rho: [u8; 32],
        pub(super) r_as_ntt: [PolynomialRingElement<Vector>; K],
        pub(super) error2: PolynomialRingElement<Vector>,
        pub(super) randomness: [u8; 32],
    }

    /// A flat version of platform dependent types.
    #[repr(transparent)]
    pub struct FlatBytes<const LEN: usize> {
        // LEN = K * 512
        pub bytes: [u8; LEN],
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

    /// Convert [`FlatBytes`] to a [`PublicKey2`].
    impl<const LEN: usize, const K: usize, Vector: Operations> From<&FlatBytes<LEN>>
        for PublicKey2<K, Vector>
    {
        fn from(pk: &FlatBytes<LEN>) -> Self {
            Self {
                t_as_ntt: deserialize_secret_key(&pk.bytes),
            }
        }
    }

    /// Convert [`MlKemPublicKeyUnpacked`] to [`FlatBytes`].
    impl<const LEN: usize, const K: usize, Vector: Operations>
        From<&MlKemPublicKeyUnpacked<K, Vector>> for FlatBytes<LEN>
    {
        fn from(pk: &MlKemPublicKeyUnpacked<K, Vector>) -> Self {
            let mut bytes = [0u8; LEN];

            bytes[0..32].copy_from_slice(&pk.ind_cpa_public_key.seed_for_A);
            bytes[32..64].copy_from_slice(&pk.public_key_hash);
            bytes[64..64 + (K * BITS_PER_RING_ELEMENT / 8)]
                .copy_from_slice(&serialize_secret_key(&pk.ind_cpa_public_key.t_as_ntt));

            Self { bytes }
        }
    }
}

use types::*;

// /// The incremental public key that allows generating [`Ciphertext2`].
// #[repr(transparent)]
// pub struct PublicKey2Flat<const LEN: usize> {
//     bytes: [u8; LEN],
// }

// impl<const LEN: usize> FlatBytes<LEN> {
//     pub fn from_unpacked<const K: usize, Vector: Operations>(
//         pk: &MlKemPublicKeyUnpacked<K, Vector>,
//     ) -> Self {
//         Self {
//             bytes: serialize_secret_key(&pk.ind_cpa_public_key.t_as_ntt),
//         }
//     }
// }

// /// A flat byte representation of rht [`EncapsState`].
// pub struct EncapsStateFlat<const LEN: usize> {
//     bytes: [u8; LEN],
// }

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
        rho: pseudorandomness.try_into().unwrap(),
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
    Scheme: Variant,
>(
    private_key: &MlKemPrivateKey<SECRET_KEY_SIZE>,
    ciphertext1: &Ciphertext1<C1_SIZE>,
    ciphertext2: &Ciphertext2<C2_SIZE>,
) -> MlKemSharedSecret {
    let mut ciphertext = [0u8; CIPHERTEXT_SIZE];
    ciphertext[..C1_SIZE].copy_from_slice(&ciphertext1.value);
    ciphertext[C1_SIZE..].copy_from_slice(&ciphertext2.value);
    crate::ind_cca::decapsulate::<
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
        Scheme,
    >(private_key, &ciphertext.into())
}
