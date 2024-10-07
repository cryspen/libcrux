use core::hash::{Hash as _, Hasher};
use std::{eprintln, hash::DefaultHasher, vec::Vec};

use crate::{
    constant_time_ops::compare_ciphertexts_select_shared_secret_in_constant_time,
    constants::{CPA_PKE_KEY_GENERATION_SEED_SIZE, H_DIGEST_SIZE, SHARED_SECRET_SIZE},
    hash_functions::Hash,
    ind_cpa::serialize_public_key,
    serialize::deserialize_ring_elements_reduced_out,
    types::*,
    utils::into_padded_array,
    variant::*,
    vector::{portable::PortableVector, Operations},
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
    const T_AS_NTT_ENCODED_SIZE: usize,
    const RANKED_BYTES_PER_RING_ELEMENT: usize,
    const PUBLIC_KEY_SIZE: usize,
    Hasher: Hash<K>,
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

    let mut valid = *public_key == public_key_serialized;

    #[cfg(all(feature = "std"))]
    if !valid {
        std::eprintln!("Invalid public key");
    } else {
        std::eprintln!("Public key is in the correct domain");
    }

    // Do some additional checks on the distribution of the key.
    // XXX: This is for linting only and not usually performed.
    // Move to a different function
    if valid {
        #[cfg(all(feature = "std"))]
        eprintln!("Checking distribution lints ...");
        let seed = &public_key[RANKED_BYTES_PER_RING_ELEMENT..];

        // ML_KEM_DIS_01: # zeroes <= 11
        let zeroes_bytes = seed.iter().filter(|&b| *b == 0).count();
        valid &= zeroes_bytes <= 11;
        #[cfg(all(feature = "std"))]
        if !valid {
            std::eprintln!("too many zeroes in public key");
        }

        // ML_KEM_DIS_02: not more than 2 sequential elements are the same
        valid &= no_sequential_elements(seed);

        // ML_KEM_DIS_03: not more than 27 values over or under 128
        let over_128 = seed.iter().filter(|&b| *b > 128).count();
        let under_128 = seed.iter().filter(|&b| *b < 128).count();
        let balanced = over_128 <= 27 && under_128 <= 27;
        #[cfg(all(feature = "std"))]
        if !balanced {
            std::eprintln!("too large or small values in public key");
        }

        valid &= balanced;

        // Unpack the public key
        let mut unpacked = unpacked::MlKemPublicKeyUnpacked::default();
        unpacked::unpack_public_key::<
            K,
            T_AS_NTT_ENCODED_SIZE,
            RANKED_BYTES_PER_RING_ELEMENT,
            PUBLIC_KEY_SIZE,
            Hasher,
            PortableVector,
        >(
            &MlKemPublicKey::try_from(public_key).unwrap(),
            &mut unpacked,
        );

        // ML_KEM_DIS_04: not more than 14, 18, 21 same elements in A'
        let counts = count_elements(&unpacked.ind_cpa_public_key.A);
        let max = match K {
            2 => 14,
            3 => 18,
            4 => 21,
            _ => unreachable!(),
        };
        let too_many: Vec<_> = counts.values().into_iter().filter(|&&x| x > max).collect();
        if !too_many.is_empty() {
            #[cfg(all(feature = "std"))]
            std::eprintln!("too many entries in A with the same value");

            valid = false;
        }

        // ML_KEM_DIS_05: no more than 3 sequential elements in A
        valid &= long_sequence_in_a(&unpacked.ind_cpa_public_key.A);

        // ML_KEM_DIS_06: no more than 656, 1369, 2338 over or under 1664 in Z_q
        let (small, large) = count_elements_zq(&unpacked.ind_cpa_public_key.A);
        let max = match K {
            2 => 656,
            3 => 1369,
            4 => 2338,
            _ => unreachable!(),
        };
        let too_many = small > max || large > max;
        if too_many {
            #[cfg(all(feature = "std"))]
            std::eprintln!("too many large or little entries in A");

            valid = false;
        }
    }

    valid
}

fn count_elements_zq<const K: usize>(
    matrix: &[[crate::polynomial::PolynomialRingElement<PortableVector>; K]; K],
) -> (u32, u32) {
    let mut large = 0;
    let mut small = 0;

    for row in matrix {
        for element in row {
            for v in element.coefficients {
                for e in v.elements {
                    if e > 1664 {
                        large += 1;
                    }
                    if e < 1664 {
                        small += 1;
                    }
                }
            }
        }
    }

    (small, large)
}

fn count_elements<const K: usize>(
    matrix: &[[crate::polynomial::PolynomialRingElement<PortableVector>; K]; K],
) -> std::collections::HashMap<Vec<u64>, u64> {
    let mut counts = std::collections::HashMap::new();

    for row in matrix {
        for element in row {
            let e: Vec<u64> = element
                .coefficients
                .iter()
                .map(|v| {
                    let mut hasher = DefaultHasher::new();
                    v.hash(&mut hasher);
                    hasher.finish()
                })
                .collect();
            *counts.entry(e).or_insert(0u64) += 1;
        }
    }

    counts
}

fn long_sequence_in_a<const K: usize>(
    matrix: &[[crate::polynomial::PolynomialRingElement<PortableVector>; K]; K],
) -> bool {
    let mut current_value = hash_re(matrix);
    let mut current_len = 1;
    let mut longest_len = current_len;

    for row in matrix {
        for element in row.iter().skip(1) {
            let e: Vec<u64> = element
                .coefficients
                .iter()
                .map(|v| {
                    let mut hasher = DefaultHasher::new();
                    v.hash(&mut hasher);
                    hasher.finish()
                })
                .collect();
            if e == current_value {
                // Count the values
                current_len += 1;
                if current_len > longest_len {
                    longest_len = current_len;
                }
            } else {
                // Value changed
                current_value = e;
                current_len = 1;
            }
        }
    }

    if longest_len > 3 {
        #[cfg(all(feature = "std"))]
        std::eprintln!("too many sequential values in public key ({longest_len}x)");

        false
    } else {
        true
    }
}

fn hash_re<const K: usize>(
    matrix: &[[crate::polynomial::PolynomialRingElement<PortableVector>; K]; K],
) -> Vec<u64> {
    matrix[0][0]
        .coefficients
        .iter()
        .map(|v| {
            let mut hasher = DefaultHasher::new();
            v.hash(&mut hasher);
            hasher.finish()
        })
        .collect()
}

fn no_sequential_elements(seed: &[u8]) -> bool {
    let mut current_value = seed[0];
    let mut current_len = 1;
    let mut _longest_value = current_value;
    let mut longest_len = current_len;

    for &byte in seed.iter().skip(1) {
        if byte == current_value {
            // Count the values
            current_len += 1;
            if current_len > longest_len {
                _longest_value = current_value;
                longest_len = current_len;
            }
        } else {
            // Value changed
            current_value = byte;
            current_len = 1;
        }
    }

    if longest_len > 2 {
        #[cfg(all(feature = "std"))]
        std::eprintln!(
            "too many sequential values in public key ({_longest_value} {longest_len}x)"
        );

        false
    } else {
        true
    }
}

// /// Generate a fake key pair that only encodes the input values.
// pub(crate) fn generate_fake_key_pair<
//     const K: usize,
//     const CPA_PRIVATE_KEY_SIZE: usize,
//     const PRIVATE_KEY_SIZE: usize,
//     const PUBLIC_KEY_SIZE: usize,
//     const BYTES_PER_RING_ELEMENT: usize,
//     const ETA1: usize,
//     const ETA1_RANDOMNESS_SIZE: usize,
//     Vector: Operations,
//     Hasher: Hash<K>,
// >(
//     private_key: [&[i16]; K],
//     public_key: [&[i16]; K],
//     seed: &[u8],
// ) -> MlKemKeyPair<PRIVATE_KEY_SIZE, PUBLIC_KEY_SIZE> {
//     let pk =
//         public_key.map(|v| PolynomialRingElement::<Vector>::from_i16_array(v));

//     // pk := (Encode_12(tˆ mod^{+}q) || ρ)
//     let public_key_serialized =
//         serialize_public_key::<K, BYTES_PER_RING_ELEMENT, PUBLIC_KEY_SIZE, Vector>(&pk, seed);

//     // sk := Encode_12(sˆ mod^{+}q)
//     let sk =
//         private_key.map(|v| PolynomialRingElement::<Vector>::from_i16_array(v));
//     let secret_key_serialized = crate::ind_cpa::serialize_secret_key(&sk);

//     let private_key: MlKemPrivateKey<PRIVATE_KEY_SIZE> =
//         MlKemPrivateKey::from(secret_key_serialized);

//     MlKemKeyPair::from(private_key, MlKemPublicKey::from(public_key_serialized))
// }

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
