use crate::simd::traits::*;

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
