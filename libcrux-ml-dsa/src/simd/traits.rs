// Each field element occupies 32 bits and the size of a simd_unit is 256 bits.
pub(crate) const COEFFICIENTS_IN_SIMD_UNIT: usize = 8;

pub const FIELD_MODULUS: i32 = 8_380_417;

// FIELD_MODULUS^{-1} mod MONTGOMERY_R
pub const INVERSE_OF_MODULUS_MOD_MONTGOMERY_R: u64 = 58_728_449;

pub(crate) trait Operations: Copy + Clone {
    #[allow(non_snake_case)]
    fn ZERO() -> Self;

    fn from_i32_array(array: &[i32]) -> Self;
    fn to_i32_array(simd_unit: Self) -> [i32; COEFFICIENTS_IN_SIMD_UNIT];

    // Arithmetic
    fn add(lhs: &Self, rhs: &Self) -> Self;
    fn subtract(lhs: &Self, rhs: &Self) -> Self;
    fn infinity_norm_exceeds(simd_unit: Self, bound: i32) -> bool;
    fn compute_hint<const GAMMA2: i32>(low: Self, high: Self) -> (usize, Self);

    // Modular operations
    fn montgomery_multiply(lhs: Self, rhs: Self) -> Self;
    fn montgomery_multiply_by_constant(simd_unit: Self, c: i32) -> Self;
    fn shift_left_then_reduce(simd_unit: Self, shift_by: usize) -> Self;

    // Decomposition operations
    fn power2round(simd_unit: Self) -> (Self, Self);

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
    fn gamma1_serialize<const OUTPUT_SIZE: usize>(simd_unit: Self) -> [u8; OUTPUT_SIZE];
    fn gamma1_deserialize<const GAMMA1_EXPONENT: usize>(serialized: &[u8]) -> Self;

    // Commitment
    fn commitment_serialize<const OUTPUT_SIZE: usize>(simd_unit: Self) -> [u8; OUTPUT_SIZE];

    // Error
    fn error_serialize<const OUTPUT_SIZE: usize>(simd_unit: Self) -> [u8; OUTPUT_SIZE];
    fn error_deserialize<const ETA: usize>(serialized: &[u8]) -> Self;

    // t0
    fn t0_serialize(simd_unit: Self) -> [u8; 13];
    fn t0_deserialize(serialized: &[u8]) -> Self;

    // t1
    fn t1_serialize(simd_unit: Self) -> [u8; 10];
    fn t1_deserialize(serialized: &[u8]) -> Self;

    // NTT
    fn ntt_at_layer_0(simd_unit: Self, zeta0: i32, zeta1: i32, zeta2: i32, zeta3: i32) -> Self;
    fn ntt_at_layer_1(simd_unit: Self, zeta0: i32, zeta1: i32) -> Self;
    fn ntt_at_layer_2(simd_unit: Self, zeta: i32) -> Self;

    // Inverse NTT
    fn invert_ntt_at_layer_0(
        simd_unit: Self,
        zeta0: i32,
        zeta1: i32,
        zeta2: i32,
        zeta3: i32,
    ) -> Self;
    fn invert_ntt_at_layer_1(simd_unit: Self, zeta0: i32, zeta1: i32) -> Self;
    fn invert_ntt_at_layer_2(simd_unit: Self, zeta: i32) -> Self;
}

// hax does not support trait with default implementations, so we use the
// following pattern.
pub fn montgomery_multiply_by_fer<S: Operations>(simd_unit: S, fer: i32) -> S {
    S::montgomery_multiply_by_constant(simd_unit, fer)
}
