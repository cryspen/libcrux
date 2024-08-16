use crate::{
    constant_time_ops::{
        compare_ciphertexts_in_constant_time, select_shared_secret_in_constant_time,
        compare_ciphertexts_select_shared_secret_in_constant_time,
    },
    constants::{CPA_PKE_KEY_GENERATION_SEED_SIZE, H_DIGEST_SIZE, SHARED_SECRET_SIZE},
    hash_functions::Hash,
    ind_cpa::serialize_public_key,
    polynomial::PolynomialRingElement,
    serialize::deserialize_ring_elements_reduced,
    types::*,
    utils::into_padded_array,
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
#[hax_lib::requires(fstar!("Spec.MLKEM.is_rank $K /\\
    $SERIALIZED_KEY_LEN == Spec.MLKEM.v_CCA_PRIVATE_KEY_SIZE $K /\\
    ${private_key.len()} == Spec.MLKEM.v_CPA_PRIVATE_KEY_SIZE $K /\\
    ${public_key.len()} == Spec.MLKEM.v_CPA_PUBLIC_KEY_SIZE $K /\\
    ${implicit_rejection_value.len()} == Spec.MLKEM.v_SHARED_SECRET_SIZE"))]
#[hax_lib::ensures(|result| fstar!("$result == Seq.append $private_key (
                                              Seq.append $public_key (
                                              Seq.append (Spec.Utils.v_H $public_key) 
                                                  $implicit_rejection_value))"))]
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
    hax_lib::fstar!("let open Spec.Utils in
        assert (Seq.slice $out 0 (v #usize_inttype (Spec.MLKEM.v_CPA_PRIVATE_KEY_SIZE $K)) `Seq.equal` $private_key);
        assert (Seq.slice $out (v #usize_inttype (Spec.MLKEM.v_CPA_PRIVATE_KEY_SIZE $K))
                                (v #usize_inttype (Spec.MLKEM.v_CPA_PRIVATE_KEY_SIZE $K +! Spec.MLKEM.v_CPA_PUBLIC_KEY_SIZE $K)) `Seq.equal` $public_key);
        assert (Seq.slice $out (v #usize_inttype (Spec.MLKEM.v_CPA_PRIVATE_KEY_SIZE $K +!
                                                Spec.MLKEM.v_CPA_PUBLIC_KEY_SIZE $K))
                                (v #usize_inttype (Spec.MLKEM.v_CPA_PRIVATE_KEY_SIZE $K +!
                                                Spec.MLKEM.v_CPA_PUBLIC_KEY_SIZE $K +!
                                                Libcrux_ml_kem.Constants.v_H_DIGEST_SIZE))
                `Seq.equal` Libcrux_ml_kem.Hash_functions.f_H #$:Hasher #$K $public_key);
        assert (Seq.slice $out (v #usize_inttype (Spec.MLKEM.v_CPA_PRIVATE_KEY_SIZE $K +!
                                                Spec.MLKEM.v_CPA_PUBLIC_KEY_SIZE $K +!
                                                Libcrux_ml_kem.Constants.v_H_DIGEST_SIZE))
                                (v #usize_inttype (Spec.MLKEM.v_CPA_PRIVATE_KEY_SIZE $K +!
                                                Spec.MLKEM.v_CPA_PUBLIC_KEY_SIZE $K +!
                                                Libcrux_ml_kem.Constants.v_H_DIGEST_SIZE +!
                                                Spec.MLKEM.v_SHARED_SECRET_SIZE))
                == $implicit_rejection_value);
        lemma_slice_append_4 $out $private_key $public_key (Libcrux_ml_kem.Hash_functions.f_H #$:Hasher #$K $public_key) $implicit_rejection_value");
    out
}

#[inline(always)]
#[hax_lib::requires(fstar!("Spec.MLKEM.is_rank $K /\\
    $RANKED_BYTES_PER_RING_ELEMENT == Spec.MLKEM.v_RANKED_BYTES_PER_RING_ELEMENT $K /\\
    $PUBLIC_KEY_SIZE == Spec.MLKEM.v_CCA_PUBLIC_KEY_SIZE $K"))]
fn validate_public_key<
    const K: usize,
    const RANKED_BYTES_PER_RING_ELEMENT: usize,
    const PUBLIC_KEY_SIZE: usize,
    Vector: Operations,
>(
    public_key: &[u8; PUBLIC_KEY_SIZE],
) -> bool {
    let deserialized_pk = deserialize_ring_elements_reduced::<PUBLIC_KEY_SIZE, K, Vector>(
        &public_key[..RANKED_BYTES_PER_RING_ELEMENT],
    );
    let public_key_serialized =
        serialize_public_key::<K, RANKED_BYTES_PER_RING_ELEMENT, PUBLIC_KEY_SIZE, Vector>(
            &deserialized_pk,
            &public_key[RANKED_BYTES_PER_RING_ELEMENT..],
        );

    *public_key == public_key_serialized
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
fn generate_keypair<
    const K: usize,
    const CPA_PRIVATE_KEY_SIZE: usize,
    const PRIVATE_KEY_SIZE: usize,
    const PUBLIC_KEY_SIZE: usize,
    const RANKED_BYTES_PER_RING_ELEMENT: usize,
    const ETA1: usize,
    const ETA1_RANDOMNESS_SIZE: usize,
    Vector: Operations,
    Hasher: Hash<K>,
>(
    randomness: [u8; KEY_GENERATION_SEED_SIZE],
) -> MlKemKeyPair<PRIVATE_KEY_SIZE, PUBLIC_KEY_SIZE> {
    let ind_cpa_keypair_randomness = &randomness[0..CPA_PKE_KEY_GENERATION_SEED_SIZE];
    let implicit_rejection_value = &randomness[CPA_PKE_KEY_GENERATION_SEED_SIZE..];

    let (ind_cpa_private_key, public_key) = crate::ind_cpa::generate_keypair::<
        K,
        CPA_PRIVATE_KEY_SIZE,
        PUBLIC_KEY_SIZE,
        RANKED_BYTES_PER_RING_ELEMENT,
        ETA1,
        ETA1_RANDOMNESS_SIZE,
        Vector,
        Hasher,
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
fn encapsulate<
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
        C1_BLOCK_SIZE,
        ETA1,
        ETA1_RANDOMNESS_SIZE,
        ETA2,
        ETA2_RANDOMNESS_SIZE,
        Vector,
        Hasher,
    >(public_key.as_slice(), randomness, pseudorandomness);

    let ciphertext = MlKemCiphertext::from(ciphertext);
    let shared_secret_array = Scheme::kdf::<K, CIPHERTEXT_SIZE, Hasher>(shared_secret, &ciphertext);
    // For some reason F* manages to assert the post-condition but fails to verify it
    // as a part of function signature 
    hax_lib::fstar!("admit() (* Panic Free *)");
    (ciphertext, shared_secret_array)
}

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
    hax_lib::fstar!("admit() (* takes too long on CI *)");
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

    let shared_secret = compare_ciphertexts_select_shared_secret_in_constant_time(
                            ciphertext.as_ref(),
                            &expected_ciphertext,
                            &shared_secret,
                            &implicit_rejection_shared_secret,
                        );
    shared_secret
}

// Unpacked API
pub mod unpacked {
    use crate::{ind_cpa::unpacked::*, vector::traits::Operations};
    use super::*;

    /// An unpacked ML-KEM IND-CCA Private Key
    pub struct MlKemPrivateKeyUnpacked<const K: usize, Vector: Operations> {
        pub(crate) ind_cpa_private_key: IndCpaPrivateKeyUnpacked<K, Vector>,
        pub(crate) implicit_rejection_value: [u8; 32],
    }

    /// An unpacked ML-KEM IND-CCA Private Key
    pub struct MlKemPublicKeyUnpacked<const K: usize, Vector: Operations> {
        pub(crate) ind_cpa_public_key: IndCpaPublicKeyUnpacked<K, Vector>,
        pub(crate) public_key_hash: [u8; 32],
    }

    /// An unpacked ML-KEM KeyPair
    pub struct MlKemKeyPairUnpacked<const K: usize, Vector: Operations> {
        pub private_key: MlKemPrivateKeyUnpacked<K, Vector>,
        pub public_key: MlKemPublicKeyUnpacked<K, Vector>,
    }

    // Generate Unpacked Keys
    pub(crate) fn generate_keypair_unpacked<
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
        let ind_cpa_keypair_randomness = &randomness[0..CPA_PKE_KEY_GENERATION_SEED_SIZE];
        let implicit_rejection_value = &randomness[CPA_PKE_KEY_GENERATION_SEED_SIZE..];
        let (ind_cpa_private_key, mut ind_cpa_public_key) =
            crate::ind_cpa::generate_keypair_unpacked::<K, ETA1, ETA1_RANDOMNESS_SIZE, Vector, Hasher>(
                ind_cpa_keypair_randomness,
            );

        // We need to un-transpose the A_transpose matrix provided by IND-CPA
        //  We would like to write the following but it is not supported by Eurydice yet.
        //  https://github.com/AeneasVerif/eurydice/issues/39
        //
        //    let A = core::array::from_fn(|i| {
        //        core::array::from_fn(|j| A_transpose[j][i])
        //    });

        #[allow(non_snake_case)]
        let mut A = core::array::from_fn(|_i| {
            core::array::from_fn(|_j| PolynomialRingElement::<Vector>::ZERO())
        });
        for i in 0..K {
            for j in 0..K {
                A[i][j] = ind_cpa_public_key.A[j][i].clone();
            }
        }
        ind_cpa_public_key.A = A;

        let pk_serialized = serialize_public_key::<K, BYTES_PER_RING_ELEMENT, PUBLIC_KEY_SIZE, Vector>(
            &ind_cpa_public_key.t_as_ntt,
            &ind_cpa_public_key.seed_for_A,
        );
        let public_key_hash = Hasher::H(&pk_serialized);
        let implicit_rejection_value: [u8; 32] = implicit_rejection_value.try_into().unwrap();

        MlKemKeyPairUnpacked {
            private_key: MlKemPrivateKeyUnpacked {
                ind_cpa_private_key,
                implicit_rejection_value,
            },
            public_key: MlKemPublicKeyUnpacked {
                ind_cpa_public_key,
                public_key_hash,
            },
        }
    }

    // Encapsulate with Unpacked Public Key
    pub(crate) fn encapsulate_unpacked<
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
    pub(crate) fn decapsulate_unpacked<
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

        let selector = compare_ciphertexts_in_constant_time(ciphertext.as_ref(), &expected_ciphertext);

        select_shared_secret_in_constant_time(
            shared_secret,
            &implicit_rejection_shared_secret,
            selector,
        )
    }
}

/// This trait collects differences in specification between ML-KEM
/// (Draft FIPS 203) and the Round 3 CRYSTALS-Kyber submission in the
/// NIST PQ competition.
///
/// cf. FIPS 203 (Draft), section 1.3
#[hax_lib::attributes]
pub(crate) trait Variant {
    #[requires(shared_secret.len() == 32)]
    #[ensures(|res| fstar!("$res == $shared_secret"))]
    fn kdf<const K: usize, const CIPHERTEXT_SIZE: usize, Hasher: Hash<K>>(
        shared_secret: &[u8],
        ciphertext: &MlKemCiphertext<CIPHERTEXT_SIZE>,
    ) -> [u8; 32];
    #[requires(randomness.len() == 32)]
    fn entropy_preprocess<const K: usize, Hasher: Hash<K>>(randomness: &[u8]) -> [u8; 32];
}

/// Implements [`Variant`], to perform the Kyber-specific actions
/// during encapsulation and decapsulation.
/// Specifically,
/// * during encapsulation, the initial randomness is hashed before being used,
/// * the derivation of the shared secret includes a hash of the Kyber ciphertext.
#[cfg(feature = "kyber")]
pub(crate) struct Kyber {}

#[cfg(feature = "kyber")]
#[hax_lib::attributes]
impl Variant for Kyber {
    #[inline(always)]
    #[requires(shared_secret.len() == 32)]
    fn kdf<const K: usize, const CIPHERTEXT_SIZE: usize, Hasher: Hash<K>>(
        shared_secret: &[u8],
        ciphertext: &MlKemCiphertext<CIPHERTEXT_SIZE>,
    ) -> [u8; 32] {
        let mut kdf_input: [u8; 2 * H_DIGEST_SIZE] = into_padded_array(&shared_secret);
        kdf_input[H_DIGEST_SIZE..].copy_from_slice(&Hasher::H(ciphertext.as_slice()));
        Hasher::PRF::<32>(&kdf_input)
    }

    #[inline(always)]
    #[requires(randomness.len() == 32)]
    fn entropy_preprocess<const K: usize, Hasher: Hash<K>>(randomness: &[u8]) -> [u8; 32] {
        Hasher::H(&randomness)
    }
}

/// Implements [`Variant`], to perform the ML-KEM-specific actions
/// during encapsulation and decapsulation.
/// Specifically,
/// * during encapsulation, the initial randomness is used without prior hashing,
/// * the derivation of the shared secret does not include a hash of the ML-KEM ciphertext.
pub(crate) struct MlKem {}

#[hax_lib::attributes]
impl Variant for MlKem {
    #[inline(always)]
    #[requires(shared_secret.len() == 32)]
    // Output name has be `out` https://github.com/hacspec/hax/issues/832
    #[ensures(|out| fstar!("$out == $shared_secret"))]
    fn kdf<const K: usize, const CIPHERTEXT_SIZE: usize, Hasher: Hash<K>>(
        shared_secret: &[u8],
        _: &MlKemCiphertext<CIPHERTEXT_SIZE>,
    ) -> [u8; 32] {
        shared_secret.try_into().unwrap()
    }

    #[inline(always)]
    #[requires(randomness.len() == 32)]
    fn entropy_preprocess<const K: usize, Hasher: Hash<K>>(randomness: &[u8]) -> [u8; 32] {
        randomness.try_into().unwrap()
    }
}
