use crate::simd::avx2::simd_unit_type::{self, AVX2SIMDUnit};

#[inline(always)]
fn serialize_when_eta_is_2<const OUTPUT_SIZE: usize>(simd_unit: AVX2SIMDUnit) -> [u8; OUTPUT_SIZE] {
    let mut serialized = [0u8; OUTPUT_SIZE];
    const ETA: i32 = 2;

    let coefficient0 = (ETA - simd_unit.coefficients[0]) as u8;
    let coefficient1 = (ETA - simd_unit.coefficients[1]) as u8;
    let coefficient2 = (ETA - simd_unit.coefficients[2]) as u8;
    let coefficient3 = (ETA - simd_unit.coefficients[3]) as u8;
    let coefficient4 = (ETA - simd_unit.coefficients[4]) as u8;
    let coefficient5 = (ETA - simd_unit.coefficients[5]) as u8;
    let coefficient6 = (ETA - simd_unit.coefficients[6]) as u8;
    let coefficient7 = (ETA - simd_unit.coefficients[7]) as u8;

    serialized[0] = (coefficient2 << 6) | (coefficient1 << 3) | coefficient0;
    serialized[1] =
        (coefficient5 << 7) | (coefficient4 << 4) | (coefficient3 << 1) | (coefficient2 >> 2);
    serialized[2] = (coefficient7 << 5) | (coefficient6 << 2) | (coefficient5 >> 1);

    serialized
}
#[inline(always)]
fn serialize_when_eta_is_4<const OUTPUT_SIZE: usize>(simd_unit: AVX2SIMDUnit) -> [u8; OUTPUT_SIZE] {
    let mut serialized = [0u8; OUTPUT_SIZE];
    const ETA: i32 = 4;

    for (i, coefficients) in simd_unit.coefficients.chunks_exact(2).enumerate() {
        let coefficient0 = (ETA - coefficients[0]) as u8;
        let coefficient1 = (ETA - coefficients[1]) as u8;

        serialized[i] = (coefficient1 << 4) | coefficient0;
    }

    serialized
}
#[inline(always)]
pub(crate) fn serialize<const OUTPUT_SIZE: usize>(simd_unit: AVX2SIMDUnit) -> [u8; OUTPUT_SIZE] {
    match OUTPUT_SIZE {
        3 => serialize_when_eta_is_2::<OUTPUT_SIZE>(simd_unit),
        4 => serialize_when_eta_is_4::<OUTPUT_SIZE>(simd_unit),
        _ => unreachable!(),
    }
}

#[inline(always)]
fn deserialize_when_eta_is_2(serialized: &[u8]) -> AVX2SIMDUnit {
    debug_assert!(serialized.len() == 3);

    let mut simd_unit = simd_unit_type::ZERO();
    const ETA: i32 = 2;

    let byte0 = serialized[0] as i32;
    let byte1 = serialized[1] as i32;
    let byte2 = serialized[2] as i32;

    simd_unit.coefficients[0] = ETA - (byte0 & 7);
    simd_unit.coefficients[1] = ETA - ((byte0 >> 3) & 7);
    simd_unit.coefficients[2] = ETA - (((byte0 >> 6) | (byte1 << 2)) & 7);
    simd_unit.coefficients[3] = ETA - ((byte1 >> 1) & 7);
    simd_unit.coefficients[4] = ETA - ((byte1 >> 4) & 7);
    simd_unit.coefficients[5] = ETA - (((byte1 >> 7) | (byte2 << 1)) & 7);
    simd_unit.coefficients[6] = ETA - ((byte2 >> 2) & 7);
    simd_unit.coefficients[7] = ETA - ((byte2 >> 5) & 7);

    simd_unit
}
#[inline(always)]
fn deserialize_when_eta_is_4(serialized: &[u8]) -> AVX2SIMDUnit {
    debug_assert!(serialized.len() == 4);

    let mut simd_unit = simd_unit_type::ZERO();
    const ETA: i32 = 4;

    for (i, byte) in serialized.iter().enumerate() {
        simd_unit.coefficients[2 * i] = ETA - ((byte & 0xF) as i32);
        simd_unit.coefficients[2 * i + 1] = ETA - ((byte >> 4) as i32);
    }

    simd_unit
}
#[inline(always)]
pub(crate) fn deserialize<const ETA: usize>(serialized: &[u8]) -> AVX2SIMDUnit {
    match ETA {
        2 => deserialize_when_eta_is_2(serialized),
        4 => deserialize_when_eta_is_4(serialized),
        _ => unreachable!(),
    }
}
