use crate::simd::{portable::PortableSIMDUnit, traits::Operations};

// This function is marked public since it is called in the corresponding AVX2 code.
#[inline(always)]
pub fn serialize_when_gamma1_is_2_pow_17<const OUTPUT_SIZE: usize>(
    simd_unit: PortableSIMDUnit,
) -> [u8; OUTPUT_SIZE] {
    const GAMMA1: i32 = 1 << 17;

    let mut serialized = [0u8; OUTPUT_SIZE];

    for (i, coefficients) in simd_unit.coefficients.chunks_exact(4).enumerate() {
        let coefficient0 = GAMMA1 - coefficients[0];
        let coefficient1 = GAMMA1 - coefficients[1];
        let coefficient2 = GAMMA1 - coefficients[2];
        let coefficient3 = GAMMA1 - coefficients[3];

        serialized[9 * i] = coefficient0 as u8;
        serialized[9 * i + 1] = (coefficient0 >> 8) as u8;

        serialized[9 * i + 2] = (coefficient0 >> 16) as u8;
        serialized[9 * i + 2] |= (coefficient1 << 2) as u8;

        serialized[9 * i + 3] = (coefficient1 >> 6) as u8;

        serialized[9 * i + 4] = (coefficient1 >> 14) as u8;
        serialized[9 * i + 4] |= (coefficient2 << 4) as u8;

        serialized[9 * i + 5] = (coefficient2 >> 4) as u8;

        serialized[9 * i + 6] = (coefficient2 >> 12) as u8;
        serialized[9 * i + 6] |= (coefficient3 << 6) as u8;

        serialized[9 * i + 7] = (coefficient3 >> 2) as u8;
        serialized[9 * i + 8] = (coefficient3 >> 10) as u8;
    }

    serialized
}
#[inline(always)]
fn serialize_when_gamma1_is_2_pow_19<const OUTPUT_SIZE: usize>(
    simd_unit: PortableSIMDUnit,
) -> [u8; OUTPUT_SIZE] {
    const GAMMA1: i32 = 1 << 19;

    let mut serialized = [0u8; OUTPUT_SIZE];

    for (i, coefficients) in simd_unit.coefficients.chunks_exact(2).enumerate() {
        let coefficient0 = GAMMA1 - coefficients[0];
        let coefficient1 = GAMMA1 - coefficients[1];

        serialized[5 * i] = coefficient0 as u8;
        serialized[5 * i + 1] = (coefficient0 >> 8) as u8;

        serialized[5 * i + 2] = (coefficient0 >> 16) as u8;
        serialized[5 * i + 2] |= (coefficient1 << 4) as u8;

        serialized[5 * i + 3] = (coefficient1 >> 4) as u8;
        serialized[5 * i + 4] = (coefficient1 >> 12) as u8;
    }

    serialized
}
#[inline(always)]
pub(crate) fn serialize<const OUTPUT_SIZE: usize>(
    simd_unit: PortableSIMDUnit,
) -> [u8; OUTPUT_SIZE] {
    match OUTPUT_SIZE as u8 {
        18 => serialize_when_gamma1_is_2_pow_17::<OUTPUT_SIZE>(simd_unit),
        20 => serialize_when_gamma1_is_2_pow_19::<OUTPUT_SIZE>(simd_unit),
        _ => unreachable!(),
    }
}

#[inline(always)]
fn deserialize_when_gamma1_is_2_pow_17(serialized: &[u8]) -> PortableSIMDUnit {
    // Each set of 9 bytes deserializes to 4 elements, and since each PortableSIMDUnit
    // can hold 8, we process 18 bytes in this function.
    debug_assert!(serialized.len() == 18);

    const GAMMA1: i32 = 1 << 17;
    const GAMMA1_TIMES_2_BITMASK: i32 = (GAMMA1 << 1) - 1;

    let mut simd_unit = PortableSIMDUnit::ZERO();

    for (i, bytes) in serialized.chunks_exact(9).enumerate() {
        simd_unit.coefficients[4 * i] = bytes[0] as i32;
        simd_unit.coefficients[4 * i] |= (bytes[1] as i32) << 8;
        simd_unit.coefficients[4 * i] |= (bytes[2] as i32) << 16;
        simd_unit.coefficients[4 * i] &= GAMMA1_TIMES_2_BITMASK;

        simd_unit.coefficients[4 * i + 1] = (bytes[2] as i32) >> 2;
        simd_unit.coefficients[4 * i + 1] |= (bytes[3] as i32) << 6;
        simd_unit.coefficients[4 * i + 1] |= (bytes[4] as i32) << 14;
        simd_unit.coefficients[4 * i + 1] &= GAMMA1_TIMES_2_BITMASK;

        simd_unit.coefficients[4 * i + 2] = (bytes[4] as i32) >> 4;
        simd_unit.coefficients[4 * i + 2] |= (bytes[5] as i32) << 4;
        simd_unit.coefficients[4 * i + 2] |= (bytes[6] as i32) << 12;
        simd_unit.coefficients[4 * i + 2] &= GAMMA1_TIMES_2_BITMASK;

        simd_unit.coefficients[4 * i + 3] = (bytes[6] as i32) >> 6;
        simd_unit.coefficients[4 * i + 3] |= (bytes[7] as i32) << 2;
        simd_unit.coefficients[4 * i + 3] |= (bytes[8] as i32) << 10;
        simd_unit.coefficients[4 * i + 3] &= GAMMA1_TIMES_2_BITMASK;

        simd_unit.coefficients[4 * i] = GAMMA1 - simd_unit.coefficients[4 * i];
        simd_unit.coefficients[4 * i + 1] = GAMMA1 - simd_unit.coefficients[4 * i + 1];
        simd_unit.coefficients[4 * i + 2] = GAMMA1 - simd_unit.coefficients[4 * i + 2];
        simd_unit.coefficients[4 * i + 3] = GAMMA1 - simd_unit.coefficients[4 * i + 3];
    }

    simd_unit
}
#[inline(always)]
fn deserialize_when_gamma1_is_2_pow_19(serialized: &[u8]) -> PortableSIMDUnit {
    // Each set of 5 bytes deserializes to 2 elements, and since each PortableSIMDUnit
    // can hold 8, we process 5 * (8 / 2) = 20 bytes in this function.
    debug_assert!(serialized.len() == 20);

    const GAMMA1: i32 = 1 << 19;
    const GAMMA1_TIMES_2_BITMASK: i32 = (GAMMA1 << 1) - 1;

    let mut simd_unit = PortableSIMDUnit::ZERO();

    for (i, bytes) in serialized.chunks_exact(5).enumerate() {
        simd_unit.coefficients[2 * i] = bytes[0] as i32;
        simd_unit.coefficients[2 * i] |= (bytes[1] as i32) << 8;
        simd_unit.coefficients[2 * i] |= (bytes[2] as i32) << 16;
        simd_unit.coefficients[2 * i] &= GAMMA1_TIMES_2_BITMASK;

        simd_unit.coefficients[2 * i + 1] = (bytes[2] as i32) >> 4;
        simd_unit.coefficients[2 * i + 1] |= (bytes[3] as i32) << 4;
        simd_unit.coefficients[2 * i + 1] |= (bytes[4] as i32) << 12;

        simd_unit.coefficients[2 * i] = GAMMA1 - simd_unit.coefficients[2 * i];
        simd_unit.coefficients[2 * i + 1] = GAMMA1 - simd_unit.coefficients[2 * i + 1];
    }

    simd_unit
}
#[inline(always)]
pub(crate) fn deserialize<const GAMMA1_EXPONENT: usize>(serialized: &[u8]) -> PortableSIMDUnit {
    match GAMMA1_EXPONENT as u8 {
        17 => deserialize_when_gamma1_is_2_pow_17(serialized),
        19 => deserialize_when_gamma1_is_2_pow_19(serialized),
        _ => unreachable!(),
    }
}
