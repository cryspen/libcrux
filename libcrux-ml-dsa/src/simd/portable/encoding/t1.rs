use crate::{
    constants::BITS_IN_UPPER_PART_OF_T,
    simd::{portable::PortableSIMDUnit, traits::Operations},
};

#[inline(always)]
pub fn serialize(simd_unit: PortableSIMDUnit) -> [u8; 10] {
    let mut serialized = [0u8; 10];

    for (i, coefficients) in simd_unit.coefficients.chunks_exact(4).enumerate() {
        serialized[5 * i] = (coefficients[0] & 0xFF) as u8;
        serialized[5 * i + 1] =
            ((coefficients[1] & 0x3F) as u8) << 2 | ((coefficients[0] >> 8) & 0x03) as u8;
        serialized[5 * i + 2] =
            ((coefficients[2] & 0x0F) as u8) << 4 | ((coefficients[1] >> 6) & 0x0F) as u8;
        serialized[5 * i + 3] =
            ((coefficients[3] & 0x03) as u8) << 6 | ((coefficients[2] >> 4) & 0x3F) as u8;
        serialized[5 * i + 4] = ((coefficients[3] >> 2) & 0xFF) as u8;
    }

    serialized
}

#[inline(always)]
pub fn deserialize(serialized: &[u8]) -> PortableSIMDUnit {
    debug_assert!(serialized.len() == 10);

    let mut simd_unit = PortableSIMDUnit::ZERO();
    let mask = (1 << BITS_IN_UPPER_PART_OF_T) - 1;

    for (i, bytes) in serialized.chunks_exact(5).enumerate() {
        let byte0 = bytes[0] as i32;
        let byte1 = bytes[1] as i32;
        let byte2 = bytes[2] as i32;
        let byte3 = bytes[3] as i32;
        let byte4 = bytes[4] as i32;

        simd_unit.coefficients[4 * i] = (byte0 | (byte1 << 8)) & mask;
        simd_unit.coefficients[4 * i + 1] = ((byte1 >> 2) | (byte2 << 6)) & mask;
        simd_unit.coefficients[4 * i + 2] = ((byte2 >> 4) | (byte3 << 4)) & mask;
        simd_unit.coefficients[4 * i + 3] = ((byte3 >> 6) | (byte4 << 2)) & mask;
    }

    simd_unit
}
