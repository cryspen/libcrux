pub(crate) const FIELD_MODULUS: u16 = 3329;
pub(crate) const BITS_PER_COEFFICIENT: usize = 12; // Each field element needs floor(log_2(FIELD_MODULUS)) + 1 = 12 bits to represent
pub(crate) const COEFFICIENTS_IN_RING_ELEMENT: usize = 256;
pub(crate) const BITS_PER_RING_ELEMENT: usize = COEFFICIENTS_IN_RING_ELEMENT * 12;

pub(crate) const REJECTION_SAMPLING_SEED_SIZE: usize = COEFFICIENTS_IN_RING_ELEMENT * 3 * 3;

pub(crate) const RANK: usize = 3;

pub(crate) const T_AS_NTT_ENCODED_SIZE: usize =
    (RANK * COEFFICIENTS_IN_RING_ELEMENT * BITS_PER_COEFFICIENT) / 8;

pub(crate) const VECTOR_U_COMPRESSION_FACTOR: usize = 10;
pub(crate) const VECTOR_U_SIZE: usize =
    (RANK * COEFFICIENTS_IN_RING_ELEMENT * VECTOR_U_COMPRESSION_FACTOR) / 8;

pub(crate) const VECTOR_V_COMPRESSION_FACTOR: usize = 4;
pub(crate) const VECTOR_V_SIZE: usize =
    (COEFFICIENTS_IN_RING_ELEMENT * VECTOR_V_COMPRESSION_FACTOR) / 8;

pub(crate) const CPA_PKE_KEY_GENERATION_SEED_SIZE: usize = 32;
pub(crate) const CPA_PKE_SECRET_KEY_SIZE: usize =
    (RANK * COEFFICIENTS_IN_RING_ELEMENT * BITS_PER_COEFFICIENT) / 8;
pub(crate) const CPA_PKE_PUBLIC_KEY_SIZE: usize = T_AS_NTT_ENCODED_SIZE + 32;
pub(crate) const CPA_PKE_CIPHERTEXT_SIZE: usize = VECTOR_U_SIZE + VECTOR_V_SIZE;
pub(crate) const CPA_PKE_MESSAGE_SIZE: usize = 32;
pub(crate) const CPA_SERIALIZED_KEY_LEN: usize = CPA_PKE_SECRET_KEY_SIZE
    + CPA_PKE_PUBLIC_KEY_SIZE
    + hash_functions::H_DIGEST_SIZE
    + CPA_PKE_MESSAGE_SIZE;

#[allow(non_snake_case)]
pub(crate) mod hash_functions {
    use libcrux::digest::{self, digest_size, Algorithm};

    pub(crate) fn G(input: &[u8]) -> [u8; digest_size(Algorithm::Sha3_512)] {
        digest::sha3_512(input)
    }

    pub(crate) const H_DIGEST_SIZE: usize = digest_size(Algorithm::Sha3_256);
    pub(crate) fn H(input: &[u8]) -> [u8; H_DIGEST_SIZE] {
        libcrux::digest::sha3_256(input)
    }

    pub(crate) fn PRF<const LEN: usize>(input: &[u8]) -> [u8; LEN] {
        digest::shake256::<LEN>(input)
    }

    pub(crate) fn XOF<const LEN: usize>(input: &[u8]) -> [u8; LEN] {
        digest::shake128::<LEN>(input)
    }

    pub(crate) fn KDF<const LEN: usize>(input: &[u8]) -> [u8; LEN] {
        digest::shake256::<LEN>(input)
    }
}

pub(crate) type KyberFieldElement = crate::helpers::field::PrimeFieldElement<FIELD_MODULUS>;
pub(crate) type KyberPolynomialRingElement =
    crate::helpers::ring::PolynomialRingElement<KyberFieldElement, COEFFICIENTS_IN_RING_ELEMENT>;
