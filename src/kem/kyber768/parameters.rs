/// Field modulus: 3329
pub(crate) const FIELD_MODULUS: i32 = 3329;

/// Each field element needs floor(log_2(FIELD_MODULUS)) + 1 = 12 bits to represent
pub(crate) const BITS_PER_COEFFICIENT: usize = 12;

/// Coefficients per ring element
pub(crate) const COEFFICIENTS_IN_RING_ELEMENT: usize = 256;

/// Bits required per (uncompressed) ring element
pub(crate) const BITS_PER_RING_ELEMENT: usize = COEFFICIENTS_IN_RING_ELEMENT * 12;

/// Bytes required per (uncompressed) ring element
pub(crate) const BYTES_PER_RING_ELEMENT: usize = BITS_PER_RING_ELEMENT / 8;

/// Seed size for rejection sampling.
///
/// See <https://eprint.iacr.org/2023/708> for some background regarding
/// this choice.
pub(crate) const REJECTION_SAMPLING_SEED_SIZE: usize = 168 * 5;

pub(crate) const CPA_PKE_MESSAGE_SIZE: usize = 32;

pub(crate) const CPA_PKE_KEY_GENERATION_SEED_SIZE: usize = 32;

/// Rank
pub(crate) const RANK_512: usize = 2;
pub(crate) const RANK_768: usize = 3;
pub(crate) const RANK_1024: usize = 4;

pub(crate) const RANKED_BYTES_PER_RING_ELEMENT_512: usize = RANK_512 * BITS_PER_RING_ELEMENT / 8;
pub(crate) const RANKED_BYTES_PER_RING_ELEMENT_768: usize = RANK_768 * BITS_PER_RING_ELEMENT / 8;
pub(crate) const RANKED_BYTES_PER_RING_ELEMENT_1024: usize = RANK_1024 * BITS_PER_RING_ELEMENT / 8;

/// `T` NTT encoding size in bytes
pub(crate) const T_AS_NTT_ENCODED_SIZE_512: usize =
    (RANK_512 * COEFFICIENTS_IN_RING_ELEMENT * BITS_PER_COEFFICIENT) / 8;
pub(crate) const T_AS_NTT_ENCODED_SIZE_768: usize =
    (RANK_768 * COEFFICIENTS_IN_RING_ELEMENT * BITS_PER_COEFFICIENT) / 8;
pub(crate) const T_AS_NTT_ENCODED_SIZE_1024: usize =
    (RANK_1024 * COEFFICIENTS_IN_RING_ELEMENT * BITS_PER_COEFFICIENT) / 8;

// Compression factor for `U`
pub(crate) const VECTOR_U_COMPRESSION_FACTOR_512: usize = 10;
pub(crate) const VECTOR_U_COMPRESSION_FACTOR_768: usize = 10;
pub(crate) const VECTOR_U_COMPRESSION_FACTOR_1024: usize = 11;

/// Compute serialized length for output size of ByteEncode
const fn serialized_len<const K: usize, const OUT_LEN: usize>() -> usize {
    OUT_LEN * K
}

/// Compute block length for output block size of ByteEncode u (c1)
const fn block_len<const FACTOR: usize>() -> usize {
    (COEFFICIENTS_IN_RING_ELEMENT * FACTOR) / 8
}

// Resulting c1 block lengths
pub(crate) const C1_BLOCK_SIZE_512: usize = block_len::<VECTOR_U_COMPRESSION_FACTOR_512>();
pub(crate) const C1_BLOCK_SIZE_768: usize = block_len::<VECTOR_U_COMPRESSION_FACTOR_768>();
pub(crate) const C1_BLOCK_SIZE_1024: usize = block_len::<VECTOR_U_COMPRESSION_FACTOR_1024>();

// Resulting c1 lengths
pub(crate) const C1_SIZE_512: usize = serialized_len::<RANK_512, C1_BLOCK_SIZE_512>();
pub(crate) const C1_SIZE_768: usize = serialized_len::<RANK_768, C1_BLOCK_SIZE_768>();
pub(crate) const C1_SIZE_1024: usize = serialized_len::<RANK_1024, C1_BLOCK_SIZE_1024>();

// Compression factor for `V`
pub(crate) const VECTOR_V_COMPRESSION_FACTOR_512: usize = 4;
pub(crate) const VECTOR_V_COMPRESSION_FACTOR_768: usize = 4;
pub(crate) const VECTOR_V_COMPRESSION_FACTOR_1024: usize = 5;

// Resulting c2 lengths
pub(crate) const C2_SIZE_512: usize = block_len::<VECTOR_V_COMPRESSION_FACTOR_512>();
pub(crate) const C2_SIZE_768: usize = block_len::<VECTOR_V_COMPRESSION_FACTOR_768>();
pub(crate) const C2_SIZE_1024: usize = block_len::<VECTOR_V_COMPRESSION_FACTOR_1024>();

/// `U` encoding size in bytes
pub(crate) const BYTES_PER_ENCODED_ELEMENT_OF_U: usize =
    (COEFFICIENTS_IN_RING_ELEMENT * VECTOR_U_COMPRESSION_FACTOR_768) / 8;
pub(crate) const VECTOR_U_ENCODED_SIZE_512: usize = RANK_512 * BYTES_PER_ENCODED_ELEMENT_OF_U;
pub(crate) const VECTOR_U_ENCODED_SIZE_768: usize = RANK_768 * BYTES_PER_ENCODED_ELEMENT_OF_U;
pub(crate) const VECTOR_U_ENCODED_SIZE_1024: usize = RANK_1024 * BYTES_PER_ENCODED_ELEMENT_OF_U;

/// `V` encoding size in bytes
pub(crate) const VECTOR_V_ENCODED_SIZE_512: usize =
    (COEFFICIENTS_IN_RING_ELEMENT * VECTOR_V_COMPRESSION_FACTOR_512) / 8;
pub(crate) const VECTOR_V_ENCODED_SIZE_768: usize =
    (COEFFICIENTS_IN_RING_ELEMENT * VECTOR_V_COMPRESSION_FACTOR_768) / 8;
pub(crate) const VECTOR_V_ENCODED_SIZE_1024: usize =
    (COEFFICIENTS_IN_RING_ELEMENT * VECTOR_V_COMPRESSION_FACTOR_1024) / 8;

pub(crate) const CPA_PKE_SECRET_KEY_SIZE_512: usize =
    (RANK_512 * COEFFICIENTS_IN_RING_ELEMENT * BITS_PER_COEFFICIENT) / 8;
pub(crate) const CPA_PKE_SECRET_KEY_SIZE_768: usize =
    (RANK_768 * COEFFICIENTS_IN_RING_ELEMENT * BITS_PER_COEFFICIENT) / 8;
pub(crate) const CPA_PKE_SECRET_KEY_SIZE_1024: usize =
    (RANK_1024 * COEFFICIENTS_IN_RING_ELEMENT * BITS_PER_COEFFICIENT) / 8;

pub(crate) const CPA_PKE_PUBLIC_KEY_SIZE_512: usize = T_AS_NTT_ENCODED_SIZE_512 + 32;
pub(crate) const CPA_PKE_PUBLIC_KEY_SIZE_768: usize = T_AS_NTT_ENCODED_SIZE_768 + 32;
pub(crate) const CPA_PKE_PUBLIC_KEY_SIZE_1024: usize = T_AS_NTT_ENCODED_SIZE_1024 + 32;

pub(crate) const CPA_PKE_CIPHERTEXT_SIZE_512: usize =
    VECTOR_U_ENCODED_SIZE_512 + VECTOR_V_ENCODED_SIZE_512;
pub(crate) const CPA_PKE_CIPHERTEXT_SIZE_768: usize =
    VECTOR_U_ENCODED_SIZE_768 + VECTOR_V_ENCODED_SIZE_768;
pub(crate) const CPA_PKE_CIPHERTEXT_SIZE_1024: usize =
    VECTOR_U_ENCODED_SIZE_1024 + VECTOR_V_ENCODED_SIZE_1024;

pub(crate) const CPA_SERIALIZED_KEY_LEN_512: usize = CPA_PKE_SECRET_KEY_SIZE_768
    + CPA_PKE_PUBLIC_KEY_SIZE_768
    + super::hash_functions::H_DIGEST_SIZE
    + CPA_PKE_MESSAGE_SIZE;
pub(crate) const CPA_SERIALIZED_KEY_LEN_768: usize = CPA_PKE_SECRET_KEY_SIZE_768
    + CPA_PKE_PUBLIC_KEY_SIZE_768
    + super::hash_functions::H_DIGEST_SIZE
    + CPA_PKE_MESSAGE_SIZE;
pub(crate) const CPA_SERIALIZED_KEY_LEN_1024: usize = CPA_PKE_SECRET_KEY_SIZE_768
    + CPA_PKE_PUBLIC_KEY_SIZE_1024
    + super::hash_functions::H_DIGEST_SIZE
    + CPA_PKE_MESSAGE_SIZE;
