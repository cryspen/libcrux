use crate::{
    constant_time_ops::compare_ciphertexts_select_shared_secret_in_constant_time,
    constants::{CPA_PKE_KEY_GENERATION_SEED_SIZE, H_DIGEST_SIZE, SHARED_SECRET_SIZE},
    hash_functions::Hash,
    ind_cpa::serialize_public_key,
    serialize::deserialize_ring_elements_reduced_out,
    types::*,
    utils::into_padded_array,
    variant::*,
    vector::Operations,
};

/// Seed size for key generation
pub const KEY_GENERATION_SEED_SIZE: usize = CPA_PKE_KEY_GENERATION_SEED_SIZE + SHARED_SECRET_SIZE;

/// Seed size for encapsulation
pub const ENCAPS_SEED_SIZE: usize = SHARED_SECRET_SIZE;

// TODO: We should make this an actual type as opposed to alias so we can enforce
// some checks at the type level. This is being tracked in:
// https://github.com/cryspen/libcrux/issues/123
/// An ML-KEM shared secret.
///
/// A byte array of size [`SHARED_SECRET_SIZE`].
pub type MlKemSharedSecret = [u8; SHARED_SECRET_SIZE];

/// This module instantiates the functions in this file and multiplexes between
/// different implementations at runtime.
#[cfg(not(eurydice))]
pub(crate) mod multiplexing;

/// This module instantiates the functions in this file for each platform.
/// To use these, runtime checks must be performed before calling them.
pub(crate) mod instantiations;

/// Serialize the secret key.
#[inline(always)]
fn serialize_kem_secret_key<const K: usize, const SERIALIZED_KEY_LEN: usize, Hasher: Hash<K>>(
    private_key: &[u8],
    public_key: &[u8],
    implicit_rejection_value: &[u8],
) -> [u8; SERIALIZED_KEY_LEN] {
    let mut out = [0u8; SERIALIZED_KEY_LEN];
    let mut pointer = 0;
    out[pointer..pointer + private_key.len()].copy_from_slice(private_key);
    pointer += private_key.len();
    out[pointer..pointer + public_key.len()].copy_from_slice(public_key);
    pointer += public_key.len();
    out[pointer..pointer + H_DIGEST_SIZE].copy_from_slice(&Hasher::H(public_key));
    pointer += H_DIGEST_SIZE;
    out[pointer..pointer + implicit_rejection_value.len()]
        .copy_from_slice(implicit_rejection_value);
    out
}

/// Validate an ML-KEM public key.
///
/// This implements the Modulus check in 7.2 2.
/// Note that the size check in 7.2 1 is covered by the `PUBLIC_KEY_SIZE` in the
/// `public_key` type.
#[inline(always)]
fn validate_public_key<
    const K: usize,
    const RANKED_BYTES_PER_RING_ELEMENT: usize,
    const PUBLIC_KEY_SIZE: usize,
    Vector: Operations,
>(
    public_key: &[u8; PUBLIC_KEY_SIZE],
) -> bool {
    let deserialized_pk = deserialize_ring_elements_reduced_out::<PUBLIC_KEY_SIZE, K, Vector>(
        &public_key[..RANKED_BYTES_PER_RING_ELEMENT],
    );
    let public_key_serialized =
        serialize_public_key::<K, RANKED_BYTES_PER_RING_ELEMENT, PUBLIC_KEY_SIZE, Vector>(
            &deserialized_pk,
            &public_key[RANKED_BYTES_PER_RING_ELEMENT..],
        );

    *public_key == public_key_serialized
}

/// Validate an ML-KEM private key.
///
/// This implements the Hash check in 7.3 3.
/// Note that the size checks in 7.2 1 and 2 are covered by the `SECRET_KEY_SIZE`
/// and `CIPHERTEXT_SIZE` in the `private_key` and `ciphertext` types.
#[inline(always)]
fn validate_private_key<
    const K: usize,
    const SECRET_KEY_SIZE: usize,
    const CIPHERTEXT_SIZE: usize,
    Hasher: Hash<K>,
>(
    private_key: &MlKemPrivateKey<SECRET_KEY_SIZE>,
    _ciphertext: &MlKemCiphertext<CIPHERTEXT_SIZE>,
) -> bool {
    // Eurydice can't access values directly on the types. We need to go to the
    // `value` directly.

    let t = Hasher::H(&private_key.value[384 * K..768 * K + 32]);
    let expected = &private_key.value[768 * K + 32..768 * K + 64];
    t == expected
}

/// Packed API
///
/// Generate a key pair.
///
/// Depending on the `Vector` and `Hasher` used, this requires different hardware
/// features
fn generate_keypair<
    const K: usize,
    const CPA_PRIVATE_KEY_SIZE: usize,
    const PRIVATE_KEY_SIZE: usize,
    const PUBLIC_KEY_SIZE: usize,
    const BYTES_PER_RING_ELEMENT: usize,
    const ETA1: usize,
    const ETA1_RANDOMNESS_SIZE: usize,
    Vector: Operations,
    Hasher: Hash<K>,
    Scheme: Variant,
>(
    randomness: [u8; KEY_GENERATION_SEED_SIZE],
) -> MlKemKeyPair<PRIVATE_KEY_SIZE, PUBLIC_KEY_SIZE> {
    let ind_cpa_keypair_randomness = &randomness[0..CPA_PKE_KEY_GENERATION_SEED_SIZE];
    let implicit_rejection_value = &randomness[CPA_PKE_KEY_GENERATION_SEED_SIZE..];

    let (ind_cpa_private_key, public_key) = crate::ind_cpa::generate_keypair::<
        K,
        CPA_PRIVATE_KEY_SIZE,
        PUBLIC_KEY_SIZE,
        BYTES_PER_RING_ELEMENT,
        ETA1,
        ETA1_RANDOMNESS_SIZE,
        Vector,
        Hasher,
        Scheme,
    >(ind_cpa_keypair_randomness);

    let secret_key_serialized = serialize_kem_secret_key::<K, PRIVATE_KEY_SIZE, Hasher>(
        &ind_cpa_private_key,
        &public_key,
        implicit_rejection_value,
    );
    let private_key: MlKemPrivateKey<PRIVATE_KEY_SIZE> =
        MlKemPrivateKey::from(secret_key_serialized);

    MlKemKeyPair::from(private_key, MlKemPublicKey::from(public_key))
}

fn encapsulate<
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
    Vector: Operations,
    Hasher: Hash<K>,
    Scheme: Variant,
>(
    public_key: &MlKemPublicKey<PUBLIC_KEY_SIZE>,
    randomness: [u8; SHARED_SECRET_SIZE],
) -> (MlKemCiphertext<CIPHERTEXT_SIZE>, MlKemSharedSecret) {
    let randomness = Scheme::entropy_preprocess::<K, Hasher>(&randomness);
    let mut to_hash: [u8; 2 * H_DIGEST_SIZE] = into_padded_array(&randomness);
    to_hash[H_DIGEST_SIZE..].copy_from_slice(&Hasher::H(public_key.as_slice()));

    let hashed = Hasher::G(&to_hash);
    let (shared_secret, pseudorandomness) = hashed.split_at(SHARED_SECRET_SIZE);

    let ciphertext = crate::ind_cpa::encrypt::<
        K,
        CIPHERTEXT_SIZE,
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
        Vector,
        Hasher,
    >(public_key.as_slice(), randomness, pseudorandomness);

    let ciphertext = MlKemCiphertext::from(ciphertext);
    let shared_secret_array = Scheme::kdf::<K, CIPHERTEXT_SIZE, Hasher>(shared_secret, &ciphertext);

    (ciphertext, shared_secret_array)
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
    ciphertext: &MlKemCiphertext<CIPHERTEXT_SIZE>,
) -> MlKemSharedSecret {
    let (ind_cpa_secret_key, secret_key) = private_key.value.split_at(CPA_SECRET_KEY_SIZE);
    let (ind_cpa_public_key, secret_key) = secret_key.split_at(PUBLIC_KEY_SIZE);
    let (ind_cpa_public_key_hash, implicit_rejection_value) = secret_key.split_at(H_DIGEST_SIZE);

    let decrypted = crate::ind_cpa::decrypt::<
        K,
        CIPHERTEXT_SIZE,
        C1_SIZE,
        VECTOR_U_COMPRESSION_FACTOR,
        VECTOR_V_COMPRESSION_FACTOR,
        Vector,
    >(ind_cpa_secret_key, &ciphertext.value);

    let mut to_hash: [u8; SHARED_SECRET_SIZE + H_DIGEST_SIZE] = into_padded_array(&decrypted);
    to_hash[SHARED_SECRET_SIZE..].copy_from_slice(ind_cpa_public_key_hash);

    let hashed = Hasher::G(&to_hash);
    let (shared_secret, pseudorandomness) = hashed.split_at(SHARED_SECRET_SIZE);

    let mut to_hash: [u8; IMPLICIT_REJECTION_HASH_INPUT_SIZE] =
        into_padded_array(implicit_rejection_value);
    to_hash[SHARED_SECRET_SIZE..].copy_from_slice(ciphertext.as_ref());
    let implicit_rejection_shared_secret: [u8; SHARED_SECRET_SIZE] = Hasher::PRF(&to_hash);

    let expected_ciphertext = crate::ind_cpa::encrypt::<
        K,
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
        Vector,
        Hasher,
    >(ind_cpa_public_key, decrypted, pseudorandomness);

    let implicit_rejection_shared_secret =
        Scheme::kdf::<K, CIPHERTEXT_SIZE, Hasher>(&implicit_rejection_shared_secret, ciphertext);
    let shared_secret = Scheme::kdf::<K, CIPHERTEXT_SIZE, Hasher>(shared_secret, ciphertext);

    compare_ciphertexts_select_shared_secret_in_constant_time(
        ciphertext.as_ref(),
        &expected_ciphertext,
        &shared_secret,
        &implicit_rejection_shared_secret,
    )
}

/// Types for the unpacked API.
pub(crate) mod unpacked {
    use core::array::from_fn;

    use super::*;
    use crate::{
        constant_time_ops::{
            compare_ciphertexts_in_constant_time, select_shared_secret_in_constant_time,
        },
        ind_cpa::{generate_keypair_unpacked, serialize_public_key_mut, unpacked::*},
        matrix::sample_matrix_A,
        polynomial::PolynomialRingElement,
        serialize::deserialize_ring_elements_reduced,
        vector::traits::Operations,
    };

    /// An unpacked ML-KEM IND-CCA Private Key
    pub struct MlKemPrivateKeyUnpacked<const K: usize, Vector: Operations> {
        pub(crate) ind_cpa_private_key: IndCpaPrivateKeyUnpacked<K, Vector>,
        pub(crate) implicit_rejection_value: [u8; 32],
    }

    /// An unpacked ML-KEM IND-CCA Private Key
    #[derive(Clone)]
    pub struct MlKemPublicKeyUnpacked<const K: usize, Vector: Operations> {
        pub(crate) ind_cpa_public_key: IndCpaPublicKeyUnpacked<K, Vector>,
        pub(crate) public_key_hash: [u8; 32],
    }

    /// An unpacked ML-KEM KeyPair
    pub struct MlKemKeyPairUnpacked<const K: usize, Vector: Operations> {
        pub private_key: MlKemPrivateKeyUnpacked<K, Vector>,
        pub public_key: MlKemPublicKeyUnpacked<K, Vector>,
    }

    /// Generate an unpacked key from a serialized key.
    #[inline(always)]
    pub(crate) fn unpack_public_key<
        const K: usize,
        const T_AS_NTT_ENCODED_SIZE: usize,
        const RANKED_BYTES_PER_RING_ELEMENT: usize,
        const PUBLIC_KEY_SIZE: usize,
        Hasher: Hash<K>,
        Vector: Operations,
    >(
        public_key: &MlKemPublicKey<PUBLIC_KEY_SIZE>,
        unpacked_public_key: &mut MlKemPublicKeyUnpacked<K, Vector>,
    ) {
        deserialize_ring_elements_reduced::<T_AS_NTT_ENCODED_SIZE, K, Vector>(
            &public_key.value[..T_AS_NTT_ENCODED_SIZE],
            &mut unpacked_public_key.ind_cpa_public_key.t_as_ntt,
        );
        unpacked_public_key.ind_cpa_public_key.seed_for_A =
            into_padded_array(&public_key.value[T_AS_NTT_ENCODED_SIZE..]);
        sample_matrix_A::<K, Vector, Hasher>(
            &mut unpacked_public_key.ind_cpa_public_key.A,
            into_padded_array(&public_key.value[T_AS_NTT_ENCODED_SIZE..]),
            false,
        );
        unpacked_public_key.public_key_hash = Hasher::H(public_key.as_slice());
    }

    impl<const K: usize, Vector: Operations> MlKemPublicKeyUnpacked<K, Vector> {
        /// Get the serialized public key.
        #[inline(always)]
        pub fn serialized_public_key_mut<
            const RANKED_BYTES_PER_RING_ELEMENT: usize,
            const PUBLIC_KEY_SIZE: usize,
        >(
            &self,
            serialized: &mut MlKemPublicKey<PUBLIC_KEY_SIZE>,
        ) {
            serialize_public_key_mut::<K, RANKED_BYTES_PER_RING_ELEMENT, PUBLIC_KEY_SIZE, Vector>(
                &self.ind_cpa_public_key.t_as_ntt,
                &self.ind_cpa_public_key.seed_for_A,
                &mut serialized.value,
            );
        }

        /// Get the serialized public key.
        #[inline(always)]
        pub fn serialized_public_key<
            const RANKED_BYTES_PER_RING_ELEMENT: usize,
            const PUBLIC_KEY_SIZE: usize,
        >(
            &self,
        ) -> MlKemPublicKey<PUBLIC_KEY_SIZE> {
            serialize_public_key::<K, RANKED_BYTES_PER_RING_ELEMENT, PUBLIC_KEY_SIZE, Vector>(
                &self.ind_cpa_public_key.t_as_ntt,
                &self.ind_cpa_public_key.seed_for_A,
            )
            .into()
        }
    }

    impl<const K: usize, Vector: Operations> Default for MlKemPublicKeyUnpacked<K, Vector> {
        #[inline(always)]
        fn default() -> Self {
            Self {
                ind_cpa_public_key: IndCpaPublicKeyUnpacked::default(),
                public_key_hash: [0u8; 32],
            }
        }
    }

    impl<const K: usize, Vector: Operations> MlKemKeyPairUnpacked<K, Vector> {
        /// Create a new empty unpacked key pair.
        #[inline(always)]
        pub fn new() -> Self {
            Self::default()
        }

        /// Get the serialized public key.
        #[inline(always)]
        pub fn serialized_public_key_mut<
            const RANKED_BYTES_PER_RING_ELEMENT: usize,
            const PUBLIC_KEY_SIZE: usize,
        >(
            &self,
            serialized: &mut MlKemPublicKey<PUBLIC_KEY_SIZE>,
        ) {
            self.public_key
                .serialized_public_key_mut::<RANKED_BYTES_PER_RING_ELEMENT, PUBLIC_KEY_SIZE>(
                    serialized,
                )
        }

        /// Get the serialized public key.
        #[inline(always)]
        pub fn serialized_public_key<
            const RANKED_BYTES_PER_RING_ELEMENT: usize,
            const PUBLIC_KEY_SIZE: usize,
        >(
            &self,
        ) -> MlKemPublicKey<PUBLIC_KEY_SIZE> {
            self.public_key
                .serialized_public_key::<RANKED_BYTES_PER_RING_ELEMENT, PUBLIC_KEY_SIZE>()
        }

        /// Get the serialized public key.
        #[inline(always)]
        pub fn public_key(&self) -> &MlKemPublicKeyUnpacked<K, Vector> {
            &self.public_key
        }

        /// Get the serialized public key.
        #[inline(always)]
        pub fn private_key(&self) -> &MlKemPrivateKeyUnpacked<K, Vector> {
            &self.private_key
        }

        /// Get the serialized private key.
        pub fn serialized_private_key(&self) -> MlKemPrivateKey<K> {
            todo!()
        }
    }

    impl<const K: usize, Vector: Operations> Default for MlKemKeyPairUnpacked<K, Vector> {
        #[inline(always)]
        fn default() -> Self {
            Self {
                private_key: MlKemPrivateKeyUnpacked {
                    ind_cpa_private_key: IndCpaPrivateKeyUnpacked::default(),
                    implicit_rejection_value: [0u8; 32],
                },
                public_key: MlKemPublicKeyUnpacked::default(),
            }
        }
    }

    /// Generate Unpacked Keys
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
        Scheme: Variant,
    >(
        randomness: [u8; KEY_GENERATION_SEED_SIZE],
        out: &mut MlKemKeyPairUnpacked<K, Vector>,
    ) {
        let ind_cpa_keypair_randomness = &randomness[0..CPA_PKE_KEY_GENERATION_SEED_SIZE];
        let implicit_rejection_value = &randomness[CPA_PKE_KEY_GENERATION_SEED_SIZE..];

        generate_keypair_unpacked::<K, ETA1, ETA1_RANDOMNESS_SIZE, Vector, Hasher, Scheme>(
            ind_cpa_keypair_randomness,
            &mut out.private_key.ind_cpa_private_key,
            &mut out.public_key.ind_cpa_public_key,
        );

        // We need to un-transpose the A_transpose matrix provided by IND-CPA
        //  We would like to write the following but it is not supported by Eurydice yet.
        //  https://github.com/AeneasVerif/eurydice/issues/39
        //
        //    let A = from_fn(|i| {
        //        from_fn(|j| A_transpose[j][i])
        //    });

        #[allow(non_snake_case)]
        let mut A = from_fn(|_i| from_fn(|_j| PolynomialRingElement::<Vector>::ZERO()));
        for i in 0..K {
            for j in 0..K {
                A[i][j] = out.public_key.ind_cpa_public_key.A[j][i].clone();
            }
        }
        out.public_key.ind_cpa_public_key.A = A;

        let pk_serialized =
            serialize_public_key::<K, BYTES_PER_RING_ELEMENT, PUBLIC_KEY_SIZE, Vector>(
                &out.public_key.ind_cpa_public_key.t_as_ntt,
                &out.public_key.ind_cpa_public_key.seed_for_A,
            );
        out.public_key.public_key_hash = Hasher::H(&pk_serialized);
        out.private_key.implicit_rejection_value = implicit_rejection_value.try_into().unwrap();
    }

    // Encapsulate with Unpacked Public Key
    pub(crate) fn encapsulate<
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
        Vector: Operations,
        Hasher: Hash<K>,
    >(
        public_key: &MlKemPublicKeyUnpacked<K, Vector>,
        randomness: [u8; SHARED_SECRET_SIZE],
    ) -> (MlKemCiphertext<CIPHERTEXT_SIZE>, MlKemSharedSecret) {
        let mut to_hash: [u8; 2 * H_DIGEST_SIZE] = into_padded_array(&randomness);
        to_hash[H_DIGEST_SIZE..].copy_from_slice(&public_key.public_key_hash);

        let hashed = Hasher::G(&to_hash);
        let (shared_secret, pseudorandomness) = hashed.split_at(SHARED_SECRET_SIZE);

        let ciphertext = crate::ind_cpa::encrypt_unpacked::<
            K,
            CIPHERTEXT_SIZE,
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
            Vector,
            Hasher,
        >(&public_key.ind_cpa_public_key, randomness, pseudorandomness);
        let mut shared_secret_array = [0u8; SHARED_SECRET_SIZE];
        shared_secret_array.copy_from_slice(shared_secret);
        (MlKemCiphertext::from(ciphertext), shared_secret_array)
    }

    // Decapsulate with Unpacked Private Key
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
        key_pair: &MlKemKeyPairUnpacked<K, Vector>,
        ciphertext: &MlKemCiphertext<CIPHERTEXT_SIZE>,
    ) -> MlKemSharedSecret {
        let decrypted = crate::ind_cpa::decrypt_unpacked::<
            K,
            CIPHERTEXT_SIZE,
            C1_SIZE,
            VECTOR_U_COMPRESSION_FACTOR,
            VECTOR_V_COMPRESSION_FACTOR,
            Vector,
        >(&key_pair.private_key.ind_cpa_private_key, &ciphertext.value);

        let mut to_hash: [u8; SHARED_SECRET_SIZE + H_DIGEST_SIZE] = into_padded_array(&decrypted);
        to_hash[SHARED_SECRET_SIZE..].copy_from_slice(&key_pair.public_key.public_key_hash);

        let hashed = Hasher::G(&to_hash);
        let (shared_secret, pseudorandomness) = hashed.split_at(SHARED_SECRET_SIZE);

        let mut to_hash: [u8; IMPLICIT_REJECTION_HASH_INPUT_SIZE] =
            into_padded_array(&key_pair.private_key.implicit_rejection_value);
        to_hash[SHARED_SECRET_SIZE..].copy_from_slice(ciphertext.as_ref());
        let implicit_rejection_shared_secret: [u8; SHARED_SECRET_SIZE] = Hasher::PRF(&to_hash);

        let expected_ciphertext = crate::ind_cpa::encrypt_unpacked::<
            K,
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
            Vector,
            Hasher,
        >(
            &key_pair.public_key.ind_cpa_public_key,
            decrypted,
            pseudorandomness,
        );

        let selector =
            compare_ciphertexts_in_constant_time(ciphertext.as_ref(), &expected_ciphertext);

        select_shared_secret_in_constant_time(
            shared_secret,
            &implicit_rejection_shared_secret,
            selector,
        )
    }
}
