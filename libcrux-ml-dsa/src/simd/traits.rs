use crate::constants::Eta;

// Each field element occupies 32 bits and the size of a simd_unit is 256 bits.
pub(crate) const COEFFICIENTS_IN_SIMD_UNIT: usize = 8;

pub(crate) const SIMD_UNITS_IN_RING_ELEMENT: usize =
    crate::constants::COEFFICIENTS_IN_RING_ELEMENT / COEFFICIENTS_IN_SIMD_UNIT;

pub const FIELD_MODULUS: i32 = 8_380_417;

// FIELD_MODULUS^{-1} mod MONTGOMERY_R
pub const INVERSE_OF_MODULUS_MOD_MONTGOMERY_R: u64 = 58_728_449;

/// If 'x' denotes a value of type `fe`, values having this type hold a
/// representative y ≡ x·MONTGOMERY_R (mod FIELD_MODULUS).
/// We use 'fer' as a shorthand for this type.
pub(crate) type FieldElementTimesMontgomeryR = i32;

pub(crate) trait Operations: Copy + Clone {
    type Coefficient: Copy; // XXX: make generic? drop copy?

    #[allow(non_snake_case)]
    fn zero() -> Self::Coefficient;

    fn from_coefficient_array(array: &[i32], out: &mut Self::Coefficient);
    fn to_coefficient_array(value: &Self::Coefficient, out: &mut [i32]);

    // Arithmetic
    fn add(lhs: &mut Self::Coefficient, rhs: &Self::Coefficient);
    fn subtract(lhs: &mut Self::Coefficient, rhs: &Self::Coefficient);
    fn infinity_norm_exceeds(simd_unit: &Self::Coefficient, bound: i32) -> bool;
    fn decompose(
        gamma2: i32,
        simd_unit: &Self::Coefficient,
        low: &mut Self::Coefficient,
        high: &mut Self::Coefficient,
    );
    fn compute_hint<const GAMMA2: i32>(
        low: &Self::Coefficient,
        high: &Self::Coefficient,
        hint: &mut Self::Coefficient,
    ) -> usize;
    fn use_hint<const GAMMA2: i32>(simd_unit: &Self::Coefficient, hint: &mut Self::Coefficient);

    // Modular operations
    fn montgomery_multiply(lhs: &mut Self::Coefficient, rhs: &Self::Coefficient);
    fn shift_left_then_reduce<const SHIFT_BY: i32>(simd_unit: &mut Self::Coefficient);

    // Decomposition operations
    fn power2round(t0: &mut Self::Coefficient, t1: &mut Self::Coefficient);

    // Sampling
    //
    // In the sampling functions, since each SIMD unit can hold 8 coefficients,
    // we expect that |out| has the capacity for up to 8 coefficients.

    // Since each coefficient could potentially be sampled with 3 bytes, we expect
    // |randomness| to hold 24 bytes.
    fn rejection_sample_less_than_field_modulus(randomness: &[u8], out: &mut [i32]) -> usize;

    // Since each coefficient could potentially be sampled with half a byte,
    // we expect |randomness| to hold 4 bytes.
    fn rejection_sample_less_than_eta_equals_2(randomness: &[u8], out: &mut [i32]) -> usize;
    fn rejection_sample_less_than_eta_equals_4(randomness: &[u8], out: &mut [i32]) -> usize;

    // Encoding operations

    // Gamma1
    fn gamma1_serialize(
        simd_unit: &Self::Coefficient,
        serialized: &mut [u8],
        gamma1_exponent: usize,
    );
    fn gamma1_deserialize(serialized: &[u8], out: &mut Self::Coefficient, gamma1_exponent: usize);

    // Commitment
    fn commitment_serialize(simd_unit: &Self::Coefficient, serialized: &mut [u8]);

    // Error
    fn error_serialize(eta: Eta, simd_unit: &Self::Coefficient, serialized: &mut [u8]);
    fn error_deserialize(eta: Eta, serialized: &[u8], out: &mut Self::Coefficient);

    // t0
    fn t0_serialize(simd_unit: &Self::Coefficient, out: &mut [u8]); // out len 13
    fn t0_deserialize(serialized: &[u8], out: &mut Self::Coefficient);

    // t1
    fn t1_serialize(simd_unit: &Self::Coefficient, out: &mut [u8]); // out len 10
    fn t1_deserialize(serialized: &[u8], out: &mut Self::Coefficient);

    // NTT
    fn ntt(simd_units: &mut [Self::Coefficient; SIMD_UNITS_IN_RING_ELEMENT]);

    // invert NTT and convert to standard domain
    fn invert_ntt_montgomery(simd_units: &mut [Self::Coefficient; SIMD_UNITS_IN_RING_ELEMENT]);
}
