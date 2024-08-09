// Each field element occupies 32 bits and the size of a simd_unit is 256 bits.
pub(crate) const COEFFICIENTS_IN_SIMD_UNIT: usize = 8;

pub const FIELD_MODULUS: i32 = 8_380_417;

// FIELD_MODULUS^{-1} mod MONTGOMERY_R
pub const INVERSE_OF_MODULUS_MOD_MONTGOMERY_R: u64 = 58_728_449;

pub(crate) trait Operations: Clone {
    #[allow(non_snake_case)]
    fn ZERO() -> Self;

    fn from_coefficient_array(array: &[i32]) -> Self;
    fn to_coefficient_array(&self) -> [i32; COEFFICIENTS_IN_SIMD_UNIT];

    // Arithmetic
    fn add(lhs: &Self, rhs: &Self) -> Self;
    fn subtract(lhs: &Self, rhs: &Self) -> Self;
    fn infinity_norm_exceeds(simd_unit: &Self, bound: i32) -> bool;
    fn decompose<const GAMMA2: i32>(simd_unit: Self) -> (Self, Self);
    fn compute_hint<const GAMMA2: i32>(low: &Self, high: &Self) -> (usize, Self);
    fn use_hint<const GAMMA2: i32>(simd_unit: &Self, hint: &Self) -> Self;

    // Modular operations
    fn montgomery_multiply(lhs: Self, rhs: Self) -> Self;
    fn montgomery_multiply_by_constant(simd_unit: Self, c: i32) -> Self;
    fn shift_left_then_reduce<const SHIFT_BY: i32>(simd_unit: Self) -> Self;

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
    fn commitment_serialize<const OUTPUT_SIZE: usize>(simd_unit: &Self) -> [u8; OUTPUT_SIZE];

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

#[cfg(test)]
mod tests {
    use super::*;

    fn test_decompose_generic<SIMDUnit: Operations>() {
        // When GAMMA2 = 95,232
        let input = SIMDUnit::from_coefficient_array(&[
            5520769, 5416853, 180455, 8127421, 5159850, 5553986, 3391280, 3968290,
        ]);

        let expected_low = SIMDUnit::from_coefficient_array(&[
            -2687, 83861, -10009, -62531, 17322, 30530, -37072, -31454,
        ]);
        let expected_high = SIMDUnit::from_coefficient_array(&[29, 28, 1, 43, 27, 29, 18, 21]);

        let (low, high) = SIMDUnit::decompose::<95_232>(input);

        assert_eq!(
            low.to_coefficient_array(),
            expected_low.to_coefficient_array()
        );
        assert_eq!(
            high.to_coefficient_array(),
            expected_high.to_coefficient_array()
        );

        // When GAMMA2 = 261,888
        let input = SIMDUnit::from_coefficient_array(&[
            2108939, 7162128, 6506792, 7957464, 2350341, 8333084, 496214, 2168929,
        ]);

        let expected_low = SIMDUnit::from_coefficient_array(&[
            13835, -170736, 221480, 100824, 255237, -47333, -27562, 73825,
        ]);
        let expected_high = SIMDUnit::from_coefficient_array(&[4, 14, 12, 15, 4, 0, 1, 4]);

        let (low, high) = SIMDUnit::decompose::<261_888>(input);

        assert_eq!(
            low.to_coefficient_array(),
            expected_low.to_coefficient_array()
        );
        assert_eq!(
            high.to_coefficient_array(),
            expected_high.to_coefficient_array()
        );
    }

    fn test_power2round_generic<SIMDUnit: Operations>() {
        let input = SIMDUnit::from_coefficient_array(&[
            6950677, 3362411, 5783989, 5909314, 6459529, 5751812, 864332, 3667708,
        ]);

        let expected_low =
            SIMDUnit::from_coefficient_array(&[3861, 3691, 437, 2882, -3959, 1028, -4020, -2308]);
        let expected_high =
            SIMDUnit::from_coefficient_array(&[848, 410, 706, 721, 789, 702, 106, 448]);

        let (low, high) = SIMDUnit::power2round(input);

        assert_eq!(
            low.to_coefficient_array(),
            expected_low.to_coefficient_array()
        );
        assert_eq!(
            high.to_coefficient_array(),
            expected_high.to_coefficient_array()
        );
    }

    #[cfg(not(feature = "simd256"))]
    mod portable {
        use super::{test_decompose_generic, test_power2round_generic};

        #[test]
        fn test_decompose() {
            test_decompose_generic::<crate::simd::portable::PortableSIMDUnit>();
        }
        #[test]
        fn test_power2round() {
            test_power2round_generic::<crate::simd::portable::PortableSIMDUnit>();
        }
    }

    #[cfg(feature = "simd256")]
    mod avx2 {
        use super::{test_decompose_generic, test_power2round_generic};

        #[test]
        fn test_decompose() {
            test_decompose_generic::<crate::simd::avx2::AVX2SIMDUnit>();
        }
        #[test]
        fn test_power2round() {
            test_power2round_generic::<crate::simd::avx2::AVX2SIMDUnit>();
        }
    }
}
