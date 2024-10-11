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

pub(crate) const ZETAS_TIMES_MONTGOMERY_R: [FieldElementTimesMontgomeryR; 256] = [
    0, 25847, -2608894, -518909, 237124, -777960, -876248, 466468, 1826347, 2353451, -359251,
    -2091905, 3119733, -2884855, 3111497, 2680103, 2725464, 1024112, -1079900, 3585928, -549488,
    -1119584, 2619752, -2108549, -2118186, -3859737, -1399561, -3277672, 1757237, -19422, 4010497,
    280005, 2706023, 95776, 3077325, 3530437, -1661693, -3592148, -2537516, 3915439, -3861115,
    -3043716, 3574422, -2867647, 3539968, -300467, 2348700, -539299, -1699267, -1643818, 3505694,
    -3821735, 3507263, -2140649, -1600420, 3699596, 811944, 531354, 954230, 3881043, 3900724,
    -2556880, 2071892, -2797779, -3930395, -1528703, -3677745, -3041255, -1452451, 3475950,
    2176455, -1585221, -1257611, 1939314, -4083598, -1000202, -3190144, -3157330, -3632928, 126922,
    3412210, -983419, 2147896, 2715295, -2967645, -3693493, -411027, -2477047, -671102, -1228525,
    -22981, -1308169, -381987, 1349076, 1852771, -1430430, -3343383, 264944, 508951, 3097992,
    44288, -1100098, 904516, 3958618, -3724342, -8578, 1653064, -3249728, 2389356, -210977, 759969,
    -1316856, 189548, -3553272, 3159746, -1851402, -2409325, -177440, 1315589, 1341330, 1285669,
    -1584928, -812732, -1439742, -3019102, -3881060, -3628969, 3839961, 2091667, 3407706, 2316500,
    3817976, -3342478, 2244091, -2446433, -3562462, 266997, 2434439, -1235728, 3513181, -3520352,
    -3759364, -1197226, -3193378, 900702, 1859098, 909542, 819034, 495491, -1613174, -43260,
    -522500, -655327, -3122442, 2031748, 3207046, -3556995, -525098, -768622, -3595838, 342297,
    286988, -2437823, 4108315, 3437287, -3342277, 1735879, 203044, 2842341, 2691481, -2590150,
    1265009, 4055324, 1247620, 2486353, 1595974, -3767016, 1250494, 2635921, -3548272, -2994039,
    1869119, 1903435, -1050970, -1333058, 1237275, -3318210, -1430225, -451100, 1312455, 3306115,
    -1962642, -1279661, 1917081, -2546312, -1374803, 1500165, 777191, 2235880, 3406031, -542412,
    -2831860, -1671176, -1846953, -2584293, -3724270, 594136, -3776993, -2013608, 2432395, 2454455,
    -164721, 1957272, 3369112, 185531, -1207385, -3183426, 162844, 1616392, 3014001, 810149,
    1652634, -3694233, -1799107, -3038916, 3523897, 3866901, 269760, 2213111, -975884, 1717735,
    472078, -426683, 1723600, -1803090, 1910376, -1667432, -1104333, -260646, -3833893, -2939036,
    -2235985, -420899, -2286327, 183443, -976891, 1612842, -3545687, -554416, 3919660, -48306,
    -1362209, 3937738, 1400424, -846154, 1976782,
];

pub(crate) trait Operations: Copy + Clone {
    #[allow(non_snake_case)]
    fn ZERO() -> Self;

    fn from_coefficient_array(array: &[i32]) -> Self;
    fn to_coefficient_array(&self) -> [i32; COEFFICIENTS_IN_SIMD_UNIT];

    // Arithmetic
    fn add(lhs: &Self, rhs: &Self) -> Self;
    fn subtract(lhs: &Self, rhs: &Self) -> Self;
    fn infinity_norm_exceeds(simd_unit: Self, bound: i32) -> bool;
    fn decompose<const GAMMA2: i32>(simd_unit: Self) -> (Self, Self);
    fn compute_hint<const GAMMA2: i32>(low: Self, high: Self) -> (usize, Self);
    fn use_hint<const GAMMA2: i32>(simd_unit: Self, hint: Self) -> Self;

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
    fn ntt(simd_units: [Self; SIMD_UNITS_IN_RING_ELEMENT]) -> [Self; SIMD_UNITS_IN_RING_ELEMENT];

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
