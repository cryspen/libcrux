use crate::constants::*;

pub(super) const RANK: usize = 4;
pub(super) const RANKED_BYTES_PER_RING_ELEMENT: usize = RANK * BITS_PER_RING_ELEMENT / 8;
pub(super) const T_AS_NTT_ENCODED_SIZE: usize =
    (RANK * COEFFICIENTS_IN_RING_ELEMENT * BITS_PER_COEFFICIENT) / 8;
pub(super) const VECTOR_U_COMPRESSION_FACTOR: usize = 11;
// [hax]: hacspec/hacspec-v2#27 stealing error
// block_len::<VECTOR_U_COMPRESSION_FACTOR>();
pub(super) const C1_BLOCK_SIZE: usize =
    (COEFFICIENTS_IN_RING_ELEMENT * VECTOR_U_COMPRESSION_FACTOR) / 8;
// [hax]: hacspec/hacspec-v2#27 stealing error
// serialized_len::<RANK, C1_BLOCK_SIZE>();
pub(super) const C1_SIZE: usize = C1_BLOCK_SIZE * RANK;
pub(super) const VECTOR_V_COMPRESSION_FACTOR: usize = 5;
// [hax]: hacspec/hacspec-v2#27 stealing error
// block_len::<VECTOR_V_COMPRESSION_FACTOR>()
pub(super) const C2_SIZE: usize =
    (COEFFICIENTS_IN_RING_ELEMENT * VECTOR_V_COMPRESSION_FACTOR) / 8;
pub(super) const CPA_PKE_SECRET_KEY_SIZE: usize =
    (RANK * COEFFICIENTS_IN_RING_ELEMENT * BITS_PER_COEFFICIENT) / 8;
pub(crate) const CPA_PKE_PUBLIC_KEY_SIZE: usize = T_AS_NTT_ENCODED_SIZE + 32;
pub(super) const CPA_PKE_CIPHERTEXT_SIZE: usize = C1_SIZE + C2_SIZE;
pub(crate) const SECRET_KEY_SIZE: usize =
    CPA_PKE_SECRET_KEY_SIZE + CPA_PKE_PUBLIC_KEY_SIZE + H_DIGEST_SIZE + SHARED_SECRET_SIZE;

pub(super) const ETA1: usize = 2;
pub(super) const ETA1_RANDOMNESS_SIZE: usize = ETA1 * 64;
pub(super) const ETA2: usize = 2;
pub(super) const ETA2_RANDOMNESS_SIZE: usize = ETA2 * 64;

pub(super) const IMPLICIT_REJECTION_HASH_INPUT_SIZE: usize =
    SHARED_SECRET_SIZE + CPA_PKE_CIPHERTEXT_SIZE;
