use crate::{constants::BITS_IN_LOWER_PART_OF_T, simd::portable::vector_type::Coefficients};

// If t0 is a signed representative, change it to an unsigned one and
// vice versa.
#[inline(always)]
fn change_t0_interval(t0: i32) -> i32 {
    (1 << (BITS_IN_LOWER_PART_OF_T - 1)) - t0
}

#[inline(always)]
pub fn serialize(simd_unit: &Coefficients, serialized: &mut [u8]) {
    let coefficient0 = change_t0_interval(simd_unit[0]);
    let coefficient1 = change_t0_interval(simd_unit[1]);
    let coefficient2 = change_t0_interval(simd_unit[2]);
    let coefficient3 = change_t0_interval(simd_unit[3]);
    let coefficient4 = change_t0_interval(simd_unit[4]);
    let coefficient5 = change_t0_interval(simd_unit[5]);
    let coefficient6 = change_t0_interval(simd_unit[6]);
    let coefficient7 = change_t0_interval(simd_unit[7]);

    serialized[0] = coefficient0 as u8;

    serialized[1] = (coefficient0 >> 8) as u8;
    serialized[1] |= (coefficient1 << 5) as u8;

    serialized[2] = (coefficient1 >> 3) as u8;

    serialized[3] = (coefficient1 >> 11) as u8;
    serialized[3] |= (coefficient2 << 2) as u8;

    serialized[4] = (coefficient2 >> 6) as u8;
    serialized[4] |= (coefficient3 << 7) as u8;

    serialized[5] = (coefficient3 >> 1) as u8;

    serialized[6] = (coefficient3 >> 9) as u8;
    serialized[6] |= (coefficient4 << 4) as u8;

    serialized[7] = (coefficient4 >> 4) as u8;

    serialized[8] = (coefficient4 >> 12) as u8;
    serialized[8] |= (coefficient5 << 1) as u8;

    serialized[9] = (coefficient5 >> 7) as u8;
    serialized[9] |= (coefficient6 << 6) as u8;

    serialized[10] = (coefficient6 >> 2) as u8;

    serialized[11] = (coefficient6 >> 10) as u8;
    serialized[11] |= (coefficient7 << 3) as u8;

    serialized[12] = (coefficient7 >> 5) as u8;
}

#[inline(always)]
pub fn deserialize(serialized: &[u8], simd_unit: &mut Coefficients) {
    debug_assert!(serialized.len() == 13);

    const BITS_IN_LOWER_PART_OF_T_MASK: i32 = (1 << (BITS_IN_LOWER_PART_OF_T as i32)) - 1;

    let byte0 = serialized[0] as i32;
    let byte1 = serialized[1] as i32;
    let byte2 = serialized[2] as i32;
    let byte3 = serialized[3] as i32;
    let byte4 = serialized[4] as i32;
    let byte5 = serialized[5] as i32;
    let byte6 = serialized[6] as i32;
    let byte7 = serialized[7] as i32;
    let byte8 = serialized[8] as i32;
    let byte9 = serialized[9] as i32;
    let byte10 = serialized[10] as i32;
    let byte11 = serialized[11] as i32;
    let byte12 = serialized[12] as i32;

    let mut coefficient0 = byte0;
    coefficient0 |= byte1 << 8;
    coefficient0 &= BITS_IN_LOWER_PART_OF_T_MASK;

    let mut coefficient1 = byte1 >> 5;
    coefficient1 |= byte2 << 3;
    coefficient1 |= byte3 << 11;
    coefficient1 &= BITS_IN_LOWER_PART_OF_T_MASK;

    let mut coefficient2 = byte3 >> 2;
    coefficient2 |= byte4 << 6;
    coefficient2 &= BITS_IN_LOWER_PART_OF_T_MASK;

    let mut coefficient3 = byte4 >> 7;
    coefficient3 |= byte5 << 1;
    coefficient3 |= byte6 << 9;
    coefficient3 &= BITS_IN_LOWER_PART_OF_T_MASK;

    let mut coefficient4 = byte6 >> 4;
    coefficient4 |= byte7 << 4;
    coefficient4 |= byte8 << 12;
    coefficient4 &= BITS_IN_LOWER_PART_OF_T_MASK;

    let mut coefficient5 = byte8 >> 1;
    coefficient5 |= byte9 << 7;
    coefficient5 &= BITS_IN_LOWER_PART_OF_T_MASK;

    let mut coefficient6 = byte9 >> 6;
    coefficient6 |= byte10 << 2;
    coefficient6 |= byte11 << 10;
    coefficient6 &= BITS_IN_LOWER_PART_OF_T_MASK;

    let mut coefficient7 = byte11 >> 3;
    coefficient7 |= byte12 << 5;
    coefficient7 &= BITS_IN_LOWER_PART_OF_T_MASK;

    simd_unit[0] = change_t0_interval(coefficient0);
    simd_unit[1] = change_t0_interval(coefficient1);
    simd_unit[2] = change_t0_interval(coefficient2);
    simd_unit[3] = change_t0_interval(coefficient3);
    simd_unit[4] = change_t0_interval(coefficient4);
    simd_unit[5] = change_t0_interval(coefficient5);
    simd_unit[6] = change_t0_interval(coefficient6);
    simd_unit[7] = change_t0_interval(coefficient7);
}
