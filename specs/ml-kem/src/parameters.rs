//use hacspec_lib::{field::PrimeFieldElement, ring::PolynomialRingElement, vector::Vector};

/// Field modulus: 3329
pub(crate) const FIELD_MODULUS: i16 = 3329;

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

pub(crate) use hash_functions::H_DIGEST_SIZE;

/// ML-KEM parameter set
pub struct MlKemParams {
    pub rank: usize,
    pub eta1: usize,
    pub eta2: usize,
    pub du: usize,
    pub dv: usize,
}

impl MlKemParams {
    pub const fn t_as_ntt_encoded_size(&self) -> usize {
        self.rank * BYTES_PER_RING_ELEMENT
    }
    pub const fn ek_size(&self) -> usize {
        self.t_as_ntt_encoded_size() + 32
    }
    pub const fn dk_pke_size(&self) -> usize {
        self.rank * BYTES_PER_RING_ELEMENT
    }
    pub const fn dk_size(&self) -> usize {
        self.dk_pke_size() + self.ek_size() + H_DIGEST_SIZE + 32
    }
    pub const fn u_encoded_size(&self) -> usize {
        (self.rank * COEFFICIENTS_IN_RING_ELEMENT * self.du) / 8
    }
    pub const fn v_encoded_size(&self) -> usize {
        (COEFFICIENTS_IN_RING_ELEMENT * self.dv) / 8
    }
    pub const fn ciphertext_size(&self) -> usize {
        self.u_encoded_size() + self.v_encoded_size()
    }
}

pub const ML_KEM_512: MlKemParams = MlKemParams { rank: 2, eta1: 3, eta2: 2, du: 10, dv: 4 };
pub const ML_KEM_768: MlKemParams = MlKemParams { rank: 3, eta1: 2, eta2: 2, du: 10, dv: 4 };
pub const ML_KEM_1024: MlKemParams = MlKemParams { rank: 4, eta1: 2, eta2: 2, du: 11, dv: 5 };

// Derived sizes for ML-KEM-512 (k=2, du=10, dv=4)
pub const ML_KEM_512_EK_SIZE: usize = 800;       // 2*384 + 32
pub const ML_KEM_512_DK_PKE_SIZE: usize = 768;   // 2*384
pub const ML_KEM_512_DK_SIZE: usize = 1632;      // 768 + 800 + 32 + 32
pub const ML_KEM_512_CT_SIZE: usize = 768;        // 2*320 + 128
pub const ML_KEM_512_J_INPUT_SIZE: usize = 800;   // 32 + 768

// Derived sizes for ML-KEM-768 (k=3, du=10, dv=4)
pub const ML_KEM_768_EK_SIZE: usize = 1184;      // 3*384 + 32
pub const ML_KEM_768_DK_PKE_SIZE: usize = 1152;  // 3*384
pub const ML_KEM_768_DK_SIZE: usize = 2400;      // 1152 + 1184 + 32 + 32
pub const ML_KEM_768_CT_SIZE: usize = 1088;       // 3*320 + 128
pub const ML_KEM_768_J_INPUT_SIZE: usize = 1120;  // 32 + 1088

// Derived sizes for ML-KEM-1024 (k=4, du=11, dv=5)
pub const ML_KEM_1024_EK_SIZE: usize = 1568;     // 4*384 + 32
pub const ML_KEM_1024_DK_PKE_SIZE: usize = 1536; // 4*384
pub const ML_KEM_1024_DK_SIZE: usize = 3168;     // 1536 + 1568 + 32 + 32
pub const ML_KEM_1024_CT_SIZE: usize = 1568;      // 4*352 + 160
pub const ML_KEM_1024_J_INPUT_SIZE: usize = 1600; // 32 + 1568

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

    pub(crate) fn J<const LEN: usize>(input: &[u8]) -> [u8; LEN] {
        digest::shake256::<LEN>(input)
    }
}

/// An ML-KEM field element:
/// - after reduction modulo FIELD_MODULUS, it is an integer in the range [0, FIELD_MODULUS - 1]
/// - it is represented as an i16, and may not yet be reduced modulo FIELD_MODULUS
pub(crate) type FieldElement = i16;

/// A collection of 16 ML-KEM field elements.
pub(crate) type FieldElementVector = [FieldElement; 16];

/// An ML-KEM polynomial ring element
pub(crate) type Polynomial = [FieldElement; 256];

/// An ML-KEM vector
pub(crate) type Vector<const RANK: usize> = [Polynomial; RANK];

/// Am ML-KEM matrix
pub(crate) type Matrix<const RANK: usize> = [Vector<RANK>; RANK];

/// Utility function to create an array of size `N` by applying a function `f` to each index.
pub(crate) fn createi<const N: usize, T, F:Fn(usize) -> T>(f:F) -> [T; N] {
    core::array::from_fn(f)
}

#[hax_lib::opaque_type]
pub(crate) type BitVector<const N: usize> = [bool; N];

