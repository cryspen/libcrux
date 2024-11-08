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
#[hax_lib::requires(fstar!("Spec.MLKEM.is_rank $K /\\
    $CPA_PRIVATE_KEY_SIZE == Spec.MLKEM.v_CPA_PRIVATE_KEY_SIZE $K /\\
    $PRIVATE_KEY_SIZE == Spec.MLKEM.v_CCA_PRIVATE_KEY_SIZE $K /\\
    $PUBLIC_KEY_SIZE == Spec.MLKEM.v_CPA_PUBLIC_KEY_SIZE $K /\\
    $RANKED_BYTES_PER_RING_ELEMENT == Spec.MLKEM.v_RANKED_BYTES_PER_RING_ELEMENT $K /\\
    $ETA1 == Spec.MLKEM.v_ETA1 $K /\\
    $ETA1_RANDOMNESS_SIZE == Spec.MLKEM.v_ETA1_RANDOMNESS_SIZE $K"))]
#[hax_lib::ensures(|result| fstar!("let (expected, valid) = Spec.MLKEM.ind_cca_generate_keypair $K $randomness in
                                    valid ==> (${result}.f_sk.f_value, ${result}.f_pk.f_value) == expected"))] 
#[inline(always)]
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

#[hax_lib::fstar::options("--z3rlimit 150")]
#[hax_lib::requires(fstar!("Spec.MLKEM.is_rank $K /\\
    $CIPHERTEXT_SIZE == Spec.MLKEM.v_CPA_CIPHERTEXT_SIZE $K /\\
    $PUBLIC_KEY_SIZE == Spec.MLKEM.v_CPA_PUBLIC_KEY_SIZE $K /\\
    $T_AS_NTT_ENCODED_SIZE == Spec.MLKEM.v_T_AS_NTT_ENCODED_SIZE $K /\\
    $C1_SIZE == Spec.MLKEM.v_C1_SIZE $K /\\
    $C2_SIZE == Spec.MLKEM.v_C2_SIZE $K /\\
    $VECTOR_U_COMPRESSION_FACTOR == Spec.MLKEM.v_VECTOR_U_COMPRESSION_FACTOR  $K /\\
    $VECTOR_V_COMPRESSION_FACTOR == Spec.MLKEM.v_VECTOR_V_COMPRESSION_FACTOR  $K /\\
    $C1_BLOCK_SIZE == Spec.MLKEM.v_C1_BLOCK_SIZE $K /\\
    $ETA1 == Spec.MLKEM.v_ETA1 $K /\\
    $ETA1_RANDOMNESS_SIZE == Spec.MLKEM.v_ETA1_RANDOMNESS_SIZE $K /\\
    $ETA2 == Spec.MLKEM.v_ETA2 $K /\\
    $ETA2_RANDOMNESS_SIZE == Spec.MLKEM.v_ETA2_RANDOMNESS_SIZE $K"))]
#[hax_lib::ensures(|result| fstar!("let (expected, valid) = Spec.MLKEM.ind_cca_encapsulate $K ${public_key}.f_value $randomness in
                                    valid ==> (${result}._1.f_value, ${result}._2) == expected"))] 
#[inline(always)]
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

/// This code verifies on some machines, runs out of memory on others
#[hax_lib::fstar::options("--z3rlimit 500")]
#[hax_lib::requires(fstar!("Spec.MLKEM.is_rank $K /\\
    $SECRET_KEY_SIZE == Spec.MLKEM.v_CCA_PRIVATE_KEY_SIZE $K /\\
    $CPA_SECRET_KEY_SIZE == Spec.MLKEM.v_CPA_PRIVATE_KEY_SIZE $K /\\
    $PUBLIC_KEY_SIZE == Spec.MLKEM.v_CPA_PUBLIC_KEY_SIZE $K /\\
    $CIPHERTEXT_SIZE == Spec.MLKEM.v_CPA_CIPHERTEXT_SIZE $K /\\
    $T_AS_NTT_ENCODED_SIZE == Spec.MLKEM.v_T_AS_NTT_ENCODED_SIZE $K /\\
    $C1_SIZE == Spec.MLKEM.v_C1_SIZE $K /\\
    $C2_SIZE == Spec.MLKEM.v_C2_SIZE $K /\\
    $VECTOR_U_COMPRESSION_FACTOR == Spec.MLKEM.v_VECTOR_U_COMPRESSION_FACTOR  $K /\\
    $VECTOR_V_COMPRESSION_FACTOR == Spec.MLKEM.v_VECTOR_V_COMPRESSION_FACTOR  $K /\\
    $C1_BLOCK_SIZE == Spec.MLKEM.v_C1_BLOCK_SIZE $K /\\
    $ETA1 == Spec.MLKEM.v_ETA1 $K /\\
    $ETA1_RANDOMNESS_SIZE == Spec.MLKEM.v_ETA1_RANDOMNESS_SIZE $K /\\
    $ETA2 == Spec.MLKEM.v_ETA2 $K /\\
    $ETA2_RANDOMNESS_SIZE == Spec.MLKEM.v_ETA2_RANDOMNESS_SIZE $K /\\
    $IMPLICIT_REJECTION_HASH_INPUT_SIZE == Spec.MLKEM.v_IMPLICIT_REJECTION_HASH_INPUT_SIZE $K"))]
#[hax_lib::ensures(|result| fstar!("let (expected, valid) = Spec.MLKEM.ind_cca_decapsulate $K ${private_key}.f_value ${ciphertext}.f_value in
                                    valid ==> $result == expected"))] 
#[inline(always)]
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
    #[hax_lib::requires(
        fstar!("Spec.MLKEM.is_rank $K /\\
        $PUBLIC_KEY_SIZE == Spec.MLKEM.v_CPA_PUBLIC_KEY_SIZE $K /\\
        $T_AS_NTT_ENCODED_SIZE == Spec.MLKEM.v_T_AS_NTT_ENCODED_SIZE $K")
    )]
    #[hax_lib::ensures(|result|
        fstar!("let (public_key_hash, (seed, (deserialized_pk, (matrix_A, valid)))) =
            Spec.MLKEM.ind_cca_unpack_public_key $K ${public_key}.f_value in (valid ==>
            Libcrux_ml_kem.Polynomial.to_spec_matrix_t #$K #$:Vector ${unpacked_public_key}_future.f_ind_cpa_public_key.f_A == matrix_A) /\\
        Libcrux_ml_kem.Polynomial.to_spec_vector_t #$K #$:Vector ${unpacked_public_key}_future.f_ind_cpa_public_key.f_t_as_ntt == deserialized_pk /\\
        ${unpacked_public_key}_future.f_ind_cpa_public_key.f_seed_for_A == seed /\\
        ${unpacked_public_key}_future.f_public_key_hash == public_key_hash"))
    ]
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
        hax_lib::fstar!("let (_, seed) = split ${public_key}.f_value (Spec.MLKEM.v_T_AS_NTT_ENCODED_SIZE $K) in
            Lib.Sequence.eq_intro #u8 #32 (Libcrux_ml_kem.Utils.into_padded_array (sz 32) seed) seed;
            Lib.Sequence.eq_intro #u8 #32
                (Seq.slice (Libcrux_ml_kem.Utils.into_padded_array (sz 34) seed) 0 32) seed");
        unpacked_public_key.ind_cpa_public_key.seed_for_A =
            into_padded_array(&public_key.value[T_AS_NTT_ENCODED_SIZE..]);
        sample_matrix_A::<K, Vector, Hasher>(
            &mut unpacked_public_key.ind_cpa_public_key.A,
            into_padded_array(&public_key.value[T_AS_NTT_ENCODED_SIZE..]),
            false,
        );
        unpacked_public_key.public_key_hash = Hasher::H(public_key.as_slice());
    }

    #[hax_lib::attributes]
    impl<const K: usize, Vector: Operations> MlKemPublicKeyUnpacked<K, Vector> {
        /// Get the serialized public key.
        #[inline(always)]
        #[requires(fstar!("Spec.MLKEM.is_rank $K /\\
            $RANKED_BYTES_PER_RING_ELEMENT == Spec.MLKEM.v_RANKED_BYTES_PER_RING_ELEMENT $K /\\
            $PUBLIC_KEY_SIZE == Spec.MLKEM.v_CPA_PUBLIC_KEY_SIZE $K /\\
            (forall (i:nat). i < v $K ==>
                Libcrux_ml_kem.Serialize.coefficients_field_modulus_range (Seq.index 
                    self.f_ind_cpa_public_key.f_t_as_ntt i))"))]
        #[ensures(|_|
            fstar!("${serialized}_future.f_value == 
                Seq.append (Spec.MLKEM.vector_encode_12 #$K
                    (Libcrux_ml_kem.Polynomial.to_spec_vector_t #$K #$:Vector
                        self.f_ind_cpa_public_key.f_t_as_ntt))
                self.f_ind_cpa_public_key.f_seed_for_A)")
        )]
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
        #[requires(fstar!("Spec.MLKEM.is_rank $K /\\
            $RANKED_BYTES_PER_RING_ELEMENT == Spec.MLKEM.v_RANKED_BYTES_PER_RING_ELEMENT $K /\\
            $PUBLIC_KEY_SIZE == Spec.MLKEM.v_CPA_PUBLIC_KEY_SIZE $K /\\
            (forall (i:nat). i < v $K ==>
                Libcrux_ml_kem.Serialize.coefficients_field_modulus_range (Seq.index
                    self.f_ind_cpa_public_key.f_t_as_ntt i))"))]
        #[ensures(|res|
            fstar!("${res}.f_value == Seq.append (Spec.MLKEM.vector_encode_12 #$K
                            (Libcrux_ml_kem.Polynomial.to_spec_vector_t #$K #$:Vector
                                self.f_ind_cpa_public_key.f_t_as_ntt))
                        self.f_ind_cpa_public_key.f_seed_for_A)")
        )]
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

    #[hax_lib::attributes]
    impl<const K: usize, Vector: Operations> MlKemKeyPairUnpacked<K, Vector> {
        /// Create a new empty unpacked key pair.
        #[inline(always)]
        pub fn new() -> Self {
            Self::default()
        }

        /// Get the serialized public key.
        #[inline(always)]
        #[requires(fstar!("Spec.MLKEM.is_rank $K /\\
            $RANKED_BYTES_PER_RING_ELEMENT == Spec.MLKEM.v_RANKED_BYTES_PER_RING_ELEMENT $K /\\
            $PUBLIC_KEY_SIZE == Spec.MLKEM.v_CPA_PUBLIC_KEY_SIZE $K /\\
            (forall (i:nat). i < v $K ==>
                Libcrux_ml_kem.Serialize.coefficients_field_modulus_range (Seq.index 
                    self.f_public_key.f_ind_cpa_public_key.f_t_as_ntt i))"))]
        #[ensures(|_|
            fstar!("${serialized}_future.f_value == 
                Seq.append (Spec.MLKEM.vector_encode_12 #$K
                    (Libcrux_ml_kem.Polynomial.to_spec_vector_t #$K #$:Vector
                        self.f_public_key.f_ind_cpa_public_key.f_t_as_ntt))
                self.f_public_key.f_ind_cpa_public_key.f_seed_for_A)")
        )]
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
        #[requires(fstar!("Spec.MLKEM.is_rank $K /\\
            $RANKED_BYTES_PER_RING_ELEMENT == Spec.MLKEM.v_RANKED_BYTES_PER_RING_ELEMENT $K /\\
            $PUBLIC_KEY_SIZE == Spec.MLKEM.v_CPA_PUBLIC_KEY_SIZE $K /\\
            (forall (i:nat). i < v $K ==>
                Libcrux_ml_kem.Serialize.coefficients_field_modulus_range (Seq.index
                    self.f_public_key.f_ind_cpa_public_key.f_t_as_ntt i))"))]
        #[ensures(|res|
            fstar!("${res}.f_value == Seq.append (Spec.MLKEM.vector_encode_12 #$K
                            (Libcrux_ml_kem.Polynomial.to_spec_vector_t #$K #$:Vector
                                self.f_public_key.f_ind_cpa_public_key.f_t_as_ntt))
                        self.f_public_key.f_ind_cpa_public_key.f_seed_for_A)")
        )]
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
            hax_lib::fstar!("admit()");
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

    #[hax_lib::ensures(|result|
        fstar!("forall (i: nat). i < v $K ==>
            (forall (j: nat). j < v $K ==>
                Seq.index (Seq.index $result i) j ==
                    Seq.index (Seq.index $ind_cpa_a j) i)"))
    ]
    pub(crate) fn transpose_a<
        const K: usize,
        Vector: Operations,
    >(
        ind_cpa_a: [[PolynomialRingElement<Vector>; K]; K],
    ) -> [[PolynomialRingElement<Vector>; K]; K] {
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
            hax_lib::loop_invariant!(|i: usize| { fstar!("forall (j: nat). j < v $i ==>
            (forall (k: nat). k < v $K ==>
                Seq.index (Seq.index $A j) k ==
                    Seq.index (Seq.index $ind_cpa_a k) j)") });
            let _a_i = A;
            for j in 0..K {
                hax_lib::loop_invariant!(|j: usize| { fstar!("(forall (k: nat). k < v $i ==>
                    Seq.index $A k == Seq.index $_a_i k) /\\
                (forall (k: nat). k < v $j ==>
                  Seq.index (Seq.index $A (v $i)) k ==
                    Seq.index (Seq.index $ind_cpa_a k) (v $i))") });
                A[i][j] = ind_cpa_a[j][i].clone();
            }
        };
        A
    }

    /// Generate Unpacked Keys
    #[inline(always)]
    #[hax_lib::fstar::options("--z3rlimit 200 --ext context_pruning")]
    #[hax_lib::requires(fstar!("Spec.MLKEM.is_rank $K /\\
        $ETA1_RANDOMNESS_SIZE == Spec.MLKEM.v_ETA1_RANDOMNESS_SIZE $K /\\
        $ETA1 == Spec.MLKEM.v_ETA1 $K /\\
        $BYTES_PER_RING_ELEMENT == Spec.MLKEM.v_RANKED_BYTES_PER_RING_ELEMENT $K /\\
        $PUBLIC_KEY_SIZE == Spec.MLKEM.v_CPA_PUBLIC_KEY_SIZE $K"))]
    #[hax_lib::ensures(|result|
        fstar!("let ((m_A, public_key_hash), implicit_rejection_value), valid =
            Spec.MLKEM.ind_cca_unpack_generate_keypair $K $randomness in
        valid ==> Libcrux_ml_kem.Polynomial.to_spec_matrix_t #$K #$:Vector
            ${out}_future.f_public_key.f_ind_cpa_public_key.f_A == m_A /\\
        ${out}_future.f_public_key.f_public_key_hash == public_key_hash /\\
        ${out}_future.f_private_key.f_implicit_rejection_value == implicit_rejection_value"))
    ]
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

        #[allow(non_snake_case)]
        let A = transpose_a::<K, Vector>(out.public_key.ind_cpa_public_key.A);
        hax_lib::fstar!("let (ind_cpa_keypair_randomness, _) = split $randomness Spec.MLKEM.v_CPA_KEY_GENERATION_SEED_SIZE in
        let ((((_, _), matrix_A_as_ntt), _), sufficient_randomness) =
            Spec.MLKEM.ind_cpa_generate_keypair_unpacked $K ind_cpa_keypair_randomness in
        let m_v_A = Libcrux_ml_kem.Polynomial.to_spec_matrix_t #$K #$:Vector $A in
        let m_f_A = Libcrux_ml_kem.Polynomial.to_spec_matrix_t #$K #$:Vector out.f_public_key.f_ind_cpa_public_key.f_A in
        let m_A:Spec.MLKEM.matrix $K = createi $K (Spec.MLKEM.matrix_A_as_ntt_i matrix_A_as_ntt) in
        assert (forall (i: nat). i < v $K ==>
            (forall (j: nat). j < v $K ==>
            Seq.index (Seq.index m_v_A i) j ==
                Seq.index (Seq.index m_f_A j) i));
        let lemma_aux (i: nat{ i < v $K }) : Lemma
            (sufficient_randomness ==> Seq.index m_v_A i == Seq.index m_A i) =
            if sufficient_randomness then
            Lib.Sequence.eq_intro #(Spec.MLKEM.polynomial) #(v $K)
                (Seq.index m_v_A i) (Seq.index m_A i)
        in
        Classical.forall_intro lemma_aux;
        if sufficient_randomness then
            Lib.Sequence.eq_intro #(Spec.MLKEM.vector $K) #(v $K) m_A m_v_A");
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
    #[inline(always)]
    #[hax_lib::requires(fstar!("Spec.MLKEM.is_rank $K /\\
        $ETA1 == Spec.MLKEM.v_ETA1 $K /\\
        $ETA1_RANDOMNESS_SIZE == Spec.MLKEM.v_ETA1_RANDOMNESS_SIZE $K /\\
        $ETA2 == Spec.MLKEM.v_ETA2 $K /\\
        $ETA2_RANDOMNESS_SIZE == Spec.MLKEM.v_ETA2_RANDOMNESS_SIZE $K /\\
        $C1_SIZE == Spec.MLKEM.v_C1_SIZE $K /\\
        $C2_SIZE == Spec.MLKEM.v_C2_SIZE $K /\\
        $VECTOR_U_COMPRESSION_FACTOR == Spec.MLKEM.v_VECTOR_U_COMPRESSION_FACTOR $K /\\
        $VECTOR_V_COMPRESSION_FACTOR == Spec.MLKEM.v_VECTOR_V_COMPRESSION_FACTOR $K /\\
        $VECTOR_U_BLOCK_LEN == Spec.MLKEM.v_C1_BLOCK_SIZE $K /\\
        $CIPHERTEXT_SIZE == Spec.MLKEM.v_CPA_CIPHERTEXT_SIZE $K"))]
    #[hax_lib::ensures(|(ciphertext_result, shared_secret_array)|
        fstar!("let (ciphertext, shared_secret) =
            Spec.MLKEM.ind_cca_unpack_encapsulate $K ${public_key}.f_public_key_hash
            (Libcrux_ml_kem.Polynomial.to_spec_vector_t #$K #$:Vector ${public_key}.f_ind_cpa_public_key.f_t_as_ntt)
            (Libcrux_ml_kem.Polynomial.to_spec_matrix_t #$K #$:Vector ${public_key}.f_ind_cpa_public_key.f_A)
            $randomness in
        ${ciphertext_result}.f_value == ciphertext /\\
        $shared_secret_array == shared_secret"))
    ]
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
        hax_lib::fstar!("Lib.Sequence.eq_intro #u8 #32 (Seq.slice (
            Libcrux_ml_kem.Utils.into_padded_array (sz 64) $randomness) 0 32) $randomness");
        let mut to_hash: [u8; 2 * H_DIGEST_SIZE] = into_padded_array(&randomness);
        to_hash[H_DIGEST_SIZE..].copy_from_slice(&public_key.public_key_hash);
        hax_lib::fstar!("Lib.Sequence.eq_intro #u8 #64 $to_hash (
            concat $randomness ${public_key}.f_public_key_hash)");

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
    #[inline(always)]
    #[hax_lib::fstar::options("--z3rlimit 200 --ext context_pruning --z3refresh")]
    #[hax_lib::requires(fstar!("Spec.MLKEM.is_rank $K /\\
        $ETA1 == Spec.MLKEM.v_ETA1 $K /\\
        $ETA1_RANDOMNESS_SIZE == Spec.MLKEM.v_ETA1_RANDOMNESS_SIZE $K /\\
        $ETA2 == Spec.MLKEM.v_ETA2 $K /\\
        $ETA2_RANDOMNESS_SIZE == Spec.MLKEM.v_ETA2_RANDOMNESS_SIZE $K /\\
        $C1_SIZE == Spec.MLKEM.v_C1_SIZE $K /\\
        $C2_SIZE == Spec.MLKEM.v_C2_SIZE $K /\\
        $VECTOR_U_COMPRESSION_FACTOR == Spec.MLKEM.v_VECTOR_U_COMPRESSION_FACTOR $K /\\
        $VECTOR_V_COMPRESSION_FACTOR == Spec.MLKEM.v_VECTOR_V_COMPRESSION_FACTOR $K /\\
        $C1_BLOCK_SIZE == Spec.MLKEM.v_C1_BLOCK_SIZE $K /\\
        $CIPHERTEXT_SIZE == Spec.MLKEM.v_CPA_CIPHERTEXT_SIZE $K /\\
        $IMPLICIT_REJECTION_HASH_INPUT_SIZE == Spec.MLKEM.v_IMPLICIT_REJECTION_HASH_INPUT_SIZE $K"))]
    #[hax_lib::ensures(|result|
        fstar!("$result ==
            Spec.MLKEM.ind_cca_unpack_decapsulate $K ${key_pair}.f_public_key.f_public_key_hash
            ${key_pair}.f_private_key.f_implicit_rejection_value
            ${ciphertext}.f_value
            (Libcrux_ml_kem.Polynomial.to_spec_vector_t #$K #$:Vector ${key_pair}.f_private_key.f_ind_cpa_private_key.f_secret_as_ntt)
            (Libcrux_ml_kem.Polynomial.to_spec_vector_t #$K #$:Vector ${key_pair}.f_public_key.f_ind_cpa_public_key.f_t_as_ntt)
            (Libcrux_ml_kem.Polynomial.to_spec_matrix_t #$K #$:Vector ${key_pair}.f_public_key.f_ind_cpa_public_key.f_A)"))
    ]
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
        hax_lib::fstar!("assert (v $IMPLICIT_REJECTION_HASH_INPUT_SIZE == 32 + v (Spec.MLKEM.v_CPA_CIPHERTEXT_SIZE $K));
        assert (v (Spec.MLKEM.v_C1_SIZE $K +! Spec.MLKEM.v_C2_SIZE $K) == v (Spec.MLKEM.v_C1_SIZE $K) + v (Spec.MLKEM.v_C2_SIZE $K));
        assert (v (Spec.MLKEM.v_C1_SIZE $K) == v (Spec.MLKEM.v_C1_BLOCK_SIZE $K) * v $K);
        assert (v (Spec.MLKEM.v_C1_BLOCK_SIZE $K)  == 32 * v (Spec.MLKEM.v_VECTOR_U_COMPRESSION_FACTOR $K));
        assert (v (Spec.MLKEM.v_C2_SIZE $K) == 32 * v (Spec.MLKEM.v_VECTOR_V_COMPRESSION_FACTOR $K))");
        let decrypted = crate::ind_cpa::decrypt_unpacked::<
            K,
            CIPHERTEXT_SIZE,
            C1_SIZE,
            VECTOR_U_COMPRESSION_FACTOR,
            VECTOR_V_COMPRESSION_FACTOR,
            Vector,
        >(&key_pair.private_key.ind_cpa_private_key, &ciphertext.value);

        let mut to_hash: [u8; SHARED_SECRET_SIZE + H_DIGEST_SIZE] = into_padded_array(&decrypted);
        hax_lib::fstar!("Lib.Sequence.eq_intro #u8 #32 (Seq.slice $to_hash 0 32) $decrypted");
        to_hash[SHARED_SECRET_SIZE..].copy_from_slice(&key_pair.public_key.public_key_hash);
        hax_lib::fstar!("Lib.Sequence.lemma_concat2 32 $decrypted 32 ${key_pair}.f_public_key.f_public_key_hash $to_hash");

        let hashed = Hasher::G(&to_hash);
        let (shared_secret, pseudorandomness) = hashed.split_at(SHARED_SECRET_SIZE);

        let mut to_hash: [u8; IMPLICIT_REJECTION_HASH_INPUT_SIZE] =
            into_padded_array(&key_pair.private_key.implicit_rejection_value);
        hax_lib::fstar!("Lib.Sequence.eq_intro #u8 #32
            (Seq.slice $to_hash 0 32) ${key_pair}.f_private_key.f_implicit_rejection_value");
        to_hash[SHARED_SECRET_SIZE..].copy_from_slice(ciphertext.as_ref());
        hax_lib::fstar!("Lib.Sequence.lemma_concat2 32 ${key_pair}.f_private_key.f_implicit_rejection_value
            (v (Spec.MLKEM.v_CPA_CIPHERTEXT_SIZE $K)) ${ciphertext}.f_value $to_hash");
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
