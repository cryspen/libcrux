use crate::{
    constant_time_ops::{
        compare_ciphertexts_in_constant_time, select_shared_secret_in_constant_time,
    },
    constants::{CPA_PKE_KEY_GENERATION_SEED_SIZE, H_DIGEST_SIZE, SHARED_SECRET_SIZE},
    hash_functions::Hash,
    ind_cpa::{into_padded_array, serialize_public_key},
    serialize::deserialize_ring_elements_reduced,
    types::{MlKemCiphertext, MlKemKeyPair, MlKemPrivateKey, MlKemPublicKey},
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

macro_rules! instantiate {
    ($modp:ident, $vector:path, $hash:path) => {
        pub mod $modp {
            use crate::{
                MlKemCiphertext, MlKemKeyPair, MlKemPrivateKey, MlKemPublicKey, MlKemSharedSecret,
                KEY_GENERATION_SEED_SIZE, SHARED_SECRET_SIZE,
            };

            /// Portable generate key pair.
            pub(crate) fn generate_keypair_generic<
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
                super::generate_keypair_generic::<
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

            /// Portable public key validation
            pub(crate) fn validate_public_key_generic<
                const K: usize,
                const RANKED_BYTES_PER_RING_ELEMENT: usize,
                const PUBLIC_KEY_SIZE: usize,
            >(
                public_key: &[u8; PUBLIC_KEY_SIZE],
            ) -> bool {
                super::validate_public_key_generic::<
                    K,
                    RANKED_BYTES_PER_RING_ELEMENT,
                    PUBLIC_KEY_SIZE,
                    $vector,
                >(public_key)
            }

            /// Portable encapsualte
            pub(crate) fn encapsulate_generic<
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
                super::encapsulate_generic::<
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
                    $vector,
                    $hash,
                >(public_key, randomness)
            }

            /// Portable decapsulate
            pub fn decapsulate_generic<
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
                super::decapsulate_generic::<
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
                >(private_key, ciphertext)
            }
        }
    };
}

// Portable generic implementations.
instantiate! {portable, crate::vector::PortableVector, crate::hash_functions::portable::PortableHash<K>}

// AVX2 generic implementation.
#[cfg(feature = "simd256")]
instantiate! {avx2, crate::vector::SIMD256Vector, crate::hash_functions::avx2::Simd256Hash}

// NEON generic implementation.
#[cfg(feature = "simd128")]
instantiate! {neon, crate::vector::SIMD128Vector, crate::hash_functions::neon::Simd128Hash}

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

pub(crate) fn validate_public_key<
    const K: usize,
    const RANKED_BYTES_PER_RING_ELEMENT: usize,
    const PUBLIC_KEY_SIZE: usize,
>(
    public_key: &[u8; PUBLIC_KEY_SIZE],
) -> bool {
    if cfg!(feature = "simd256")
        && cfg!(target_arch = "x86_64")
        && libcrux_platform::simd256_support()
    {
        #[cfg(all(feature = "simd256", target_arch = "x86_64"))]
        return avx2::validate_public_key_generic::<
            K,
            RANKED_BYTES_PER_RING_ELEMENT,
            PUBLIC_KEY_SIZE,
        >(public_key);
        #[cfg(not(all(feature = "simd256", target_arch = "x86_64")))]
        portable::validate_public_key_generic::<K, RANKED_BYTES_PER_RING_ELEMENT, PUBLIC_KEY_SIZE>(
            public_key,
        )
    } else if cfg!(feature = "simd128")
        && cfg!(target_arch = "aarch64")
        && libcrux_platform::simd128_support()
    {
        #[cfg(all(feature = "simd128", target_arch = "aarch64"))]
        return neon::validate_public_key_generic::<
            K,
            RANKED_BYTES_PER_RING_ELEMENT,
            PUBLIC_KEY_SIZE,
        >(public_key);
        #[cfg(not(feature = "simd128"))]
        portable::validate_public_key_generic::<K, RANKED_BYTES_PER_RING_ELEMENT, PUBLIC_KEY_SIZE>(
            public_key,
        )
    } else {
        portable::validate_public_key_generic::<K, RANKED_BYTES_PER_RING_ELEMENT, PUBLIC_KEY_SIZE>(
            public_key,
        )
    }
}

fn validate_public_key_generic<
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
            deserialized_pk,
            &public_key[RANKED_BYTES_PER_RING_ELEMENT..],
        );

    *public_key == public_key_serialized
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
) -> MlKemKeyPair<PRIVATE_KEY_SIZE, PUBLIC_KEY_SIZE> {
    // Runtime feature detection.
    if cfg!(feature = "simd256")
        && cfg!(target_arch = "x86_64")
        && libcrux_platform::simd256_support()
    {
        #[cfg(all(feature = "simd256", target_arch = "x86_64"))]
        return avx2::generate_keypair_generic::<
            K,
            CPA_PRIVATE_KEY_SIZE,
            PRIVATE_KEY_SIZE,
            PUBLIC_KEY_SIZE,
            BYTES_PER_RING_ELEMENT,
            ETA1,
            ETA1_RANDOMNESS_SIZE,
        >(randomness);
        #[cfg(not(all(feature = "simd256", target_arch = "x86_64")))]
        portable::generate_keypair_generic::<
            K,
            CPA_PRIVATE_KEY_SIZE,
            PRIVATE_KEY_SIZE,
            PUBLIC_KEY_SIZE,
            BYTES_PER_RING_ELEMENT,
            ETA1,
            ETA1_RANDOMNESS_SIZE,
        >(randomness)
    } else if cfg!(feature = "simd128")
        && cfg!(target_arch = "aarch64")
        && libcrux_platform::simd128_support()
    {
        #[cfg(all(feature = "simd128", target_arch = "aarch64"))]
        return neon::generate_keypair_generic::<
            K,
            CPA_PRIVATE_KEY_SIZE,
            PRIVATE_KEY_SIZE,
            PUBLIC_KEY_SIZE,
            BYTES_PER_RING_ELEMENT,
            ETA1,
            ETA1_RANDOMNESS_SIZE,
        >(randomness);
        #[cfg(not(feature = "simd128"))]
        portable::generate_keypair_generic::<
            K,
            CPA_PRIVATE_KEY_SIZE,
            PRIVATE_KEY_SIZE,
            PUBLIC_KEY_SIZE,
            BYTES_PER_RING_ELEMENT,
            ETA1,
            ETA1_RANDOMNESS_SIZE,
        >(randomness)
    } else {
        portable::generate_keypair_generic::<
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

/// Generate a key pair.
///
/// Depending on the `Vector` and `Hasher` used, this requires different hardware
/// features
fn generate_keypair_generic<
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
>(
    public_key: &MlKemPublicKey<PUBLIC_KEY_SIZE>,
    randomness: [u8; SHARED_SECRET_SIZE],
) -> (MlKemCiphertext<CIPHERTEXT_SIZE>, MlKemSharedSecret) {
    if cfg!(feature = "simd256")
        && cfg!(target_arch = "x86_64")
        && libcrux_platform::simd256_support()
    {
        #[cfg(all(feature = "simd256", target_arch = "x86_64"))]
        return avx2::encapsulate_generic::<
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
        >(public_key, randomness);
        #[cfg(not(all(feature = "simd256", target_arch = "x86_64")))]
        portable::encapsulate_generic::<
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
    } else if cfg!(feature = "simd128")
        && cfg!(target_arch = "aarch64")
        && libcrux_platform::simd128_support()
    {
        #[cfg(not(feature = "simd128"))]
        return portable::encapsulate_generic::<
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
        >(public_key, randomness);
        #[cfg(all(feature = "simd128", target_arch = "aarch64"))]
        neon::encapsulate_generic::<
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
        portable::encapsulate_generic::<
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

fn encapsulate_generic<
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
    public_key: &MlKemPublicKey<PUBLIC_KEY_SIZE>,
    randomness: [u8; SHARED_SECRET_SIZE],
) -> (MlKemCiphertext<CIPHERTEXT_SIZE>, MlKemSharedSecret) {
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
    let mut shared_secret_array = [0u8; SHARED_SECRET_SIZE];
    shared_secret_array.copy_from_slice(shared_secret);
    (MlKemCiphertext::from(ciphertext), shared_secret_array)
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
    private_key: &MlKemPrivateKey<SECRET_KEY_SIZE>,
    ciphertext: &MlKemCiphertext<CIPHERTEXT_SIZE>,
) -> MlKemSharedSecret {
    if cfg!(feature = "simd256")
        && cfg!(target_arch = "x86_64")
        && libcrux_platform::simd256_support()
    {
        #[cfg(all(feature = "simd256", target_arch = "x86_64"))]
        return avx2::decapsulate_generic::<
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
        >(private_key, ciphertext);
        #[cfg(not(all(feature = "simd256", target_arch = "x86_64")))]
        return portable::decapsulate_generic::<
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
        >(private_key, ciphertext);
    } else if cfg!(feature = "simd128")
        && cfg!(target_arch = "aarch64")
        && libcrux_platform::simd128_support()
    {
        #[cfg(all(feature = "simd128", target_arch = "aarch64"))]
        return neon::decapsulate_generic::<
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
        >(private_key, ciphertext);
        #[cfg(not(feature = "simd128"))]
        return portable::decapsulate_generic::<
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
        >(private_key, ciphertext);
    } else {
        portable::decapsulate_generic::<
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

pub(crate) fn decapsulate_generic<
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

    let selector = compare_ciphertexts_in_constant_time::<CIPHERTEXT_SIZE>(
        ciphertext.as_ref(),
        &expected_ciphertext,
    );

    select_shared_secret_in_constant_time(
        shared_secret,
        &implicit_rejection_shared_secret,
        selector,
    )
}
