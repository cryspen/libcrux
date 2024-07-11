use crate::simd::portable::simd_unit_type::*;

#[inline(always)]
fn deserialize_when_gamma1_is_2_pow_17(serialized: &[u8]) -> PortableSIMDUnit {
    // Each set of 9 bytes deserializes to 4 elements, and since each PortableSIMDUnit
    // can hold 8, we process 18 bytes in this function.
    debug_assert!(serialized.len() == 18);

    const GAMMA1: i32 = 1 << 17;
    const GAMMA1_TIMES_2_BITMASK: i32 = (GAMMA1 << 1) - 1;

    let mut simd_unit = ZERO();

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

    let mut simd_unit = ZERO();

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
    match GAMMA1_EXPONENT {
        17 => deserialize_when_gamma1_is_2_pow_17(serialized),
        19 => deserialize_when_gamma1_is_2_pow_19(serialized),
        _ => unreachable!(),
    }
}
