// ---------------------------------------------------------------------------
// Functions for serializing and deserializing the ring element t0.
// ---------------------------------------------------------------------------

pub(crate) mod t0 {
    use crate::{
        arithmetic::PolynomialRingElement,
        constants::{BITS_IN_LOWER_PART_OF_T, RING_ELEMENT_OF_T0S_SIZE},
        ntt::ntt,
    };

    // If t0 is a signed representative, change it to an unsigned one and
    // vice versa.
    #[inline(always)]
    fn change_t0_interval(t0: i32) -> i32 {
        (1 << (BITS_IN_LOWER_PART_OF_T - 1)) - t0
    }

    #[inline(always)]
    pub(crate) fn serialize(re: PolynomialRingElement) -> [u8; RING_ELEMENT_OF_T0S_SIZE] {
        let mut serialized = [0u8; RING_ELEMENT_OF_T0S_SIZE];

        for (i, coefficients) in re.coefficients.chunks_exact(8).enumerate() {
            let coefficient0 = change_t0_interval(coefficients[0]);
            let coefficient1 = change_t0_interval(coefficients[1]);
            let coefficient2 = change_t0_interval(coefficients[2]);
            let coefficient3 = change_t0_interval(coefficients[3]);
            let coefficient4 = change_t0_interval(coefficients[4]);
            let coefficient5 = change_t0_interval(coefficients[5]);
            let coefficient6 = change_t0_interval(coefficients[6]);
            let coefficient7 = change_t0_interval(coefficients[7]);

            serialized[13 * i + 0] = coefficient0 as u8;

            serialized[13 * i + 1] = (coefficient0 >> 8) as u8;
            serialized[13 * i + 1] |= (coefficient1 << 5) as u8;

            serialized[13 * i + 2] = (coefficient1 >> 3) as u8;

            serialized[13 * i + 3] = (coefficient1 >> 11) as u8;
            serialized[13 * i + 3] |= (coefficient2 << 2) as u8;

            serialized[13 * i + 4] = (coefficient2 >> 6) as u8;
            serialized[13 * i + 4] |= (coefficient3 << 7) as u8;

            serialized[13 * i + 5] = (coefficient3 >> 1) as u8;

            serialized[13 * i + 6] = (coefficient3 >> 9) as u8;
            serialized[13 * i + 6] |= (coefficient4 << 4) as u8;

            serialized[13 * i + 7] = (coefficient4 >> 4) as u8;

            serialized[13 * i + 8] = (coefficient4 >> 12) as u8;
            serialized[13 * i + 8] |= (coefficient5 << 1) as u8;

            serialized[13 * i + 9] = (coefficient5 >> 7) as u8;
            serialized[13 * i + 9] |= (coefficient6 << 6) as u8;

            serialized[13 * i + 10] = (coefficient6 >> 2) as u8;

            serialized[13 * i + 11] = (coefficient6 >> 10) as u8;
            serialized[13 * i + 11] |= (coefficient7 << 3) as u8;

            serialized[13 * i + 12] = (coefficient7 >> 5) as u8;
        }

        serialized
    }

    #[inline(always)]
    pub(crate) fn deserialize(serialized: &[u8]) -> PolynomialRingElement {
        let mut re = PolynomialRingElement::ZERO;

        const BITS_IN_LOWER_PART_OF_T_MASK: i32 = (1 << (BITS_IN_LOWER_PART_OF_T as i32)) - 1;

        for (i, bytes) in serialized.chunks_exact(13).enumerate() {
            let byte0 = bytes[0] as i32;
            let byte1 = bytes[1] as i32;
            let byte2 = bytes[2] as i32;
            let byte3 = bytes[3] as i32;
            let byte4 = bytes[4] as i32;
            let byte5 = bytes[5] as i32;
            let byte6 = bytes[6] as i32;
            let byte7 = bytes[7] as i32;
            let byte8 = bytes[8] as i32;
            let byte9 = bytes[9] as i32;
            let byte10 = bytes[10] as i32;
            let byte11 = bytes[11] as i32;
            let byte12 = bytes[12] as i32;

            re.coefficients[8 * i + 0] = byte0;
            re.coefficients[8 * i + 0] |= byte1 << 8;
            re.coefficients[8 * i + 0] &= BITS_IN_LOWER_PART_OF_T_MASK;

            re.coefficients[8 * i + 1] = byte1 >> 5;
            re.coefficients[8 * i + 1] |= byte2 << 3;
            re.coefficients[8 * i + 1] |= byte3 << 11;
            re.coefficients[8 * i + 1] &= BITS_IN_LOWER_PART_OF_T_MASK;

            re.coefficients[8 * i + 2] = byte3 >> 2;
            re.coefficients[8 * i + 2] |= byte4 << 6;
            re.coefficients[8 * i + 2] &= BITS_IN_LOWER_PART_OF_T_MASK;

            re.coefficients[8 * i + 3] = byte4 >> 7;
            re.coefficients[8 * i + 3] |= byte5 << 1;
            re.coefficients[8 * i + 3] |= byte6 << 9;
            re.coefficients[8 * i + 3] &= BITS_IN_LOWER_PART_OF_T_MASK;

            re.coefficients[8 * i + 4] = byte6 >> 4;
            re.coefficients[8 * i + 4] |= byte7 << 4;
            re.coefficients[8 * i + 4] |= byte8 << 12;
            re.coefficients[8 * i + 4] &= BITS_IN_LOWER_PART_OF_T_MASK;

            re.coefficients[8 * i + 5] = byte8 >> 1;
            re.coefficients[8 * i + 5] |= byte9 << 7;
            re.coefficients[8 * i + 5] &= BITS_IN_LOWER_PART_OF_T_MASK;

            re.coefficients[8 * i + 6] = byte9 >> 6;
            re.coefficients[8 * i + 6] |= byte10 << 2;
            re.coefficients[8 * i + 6] |= byte11 << 10;
            re.coefficients[8 * i + 6] &= BITS_IN_LOWER_PART_OF_T_MASK;

            re.coefficients[8 * i + 7] = byte11 >> 3;
            re.coefficients[8 * i + 7] |= byte12 << 5;
            re.coefficients[8 * i + 7] &= BITS_IN_LOWER_PART_OF_T_MASK;

            re.coefficients[8 * i + 0] = change_t0_interval(re.coefficients[8 * i + 0]);
            re.coefficients[8 * i + 1] = change_t0_interval(re.coefficients[8 * i + 1]);
            re.coefficients[8 * i + 2] = change_t0_interval(re.coefficients[8 * i + 2]);
            re.coefficients[8 * i + 3] = change_t0_interval(re.coefficients[8 * i + 3]);
            re.coefficients[8 * i + 4] = change_t0_interval(re.coefficients[8 * i + 4]);
            re.coefficients[8 * i + 5] = change_t0_interval(re.coefficients[8 * i + 5]);
            re.coefficients[8 * i + 6] = change_t0_interval(re.coefficients[8 * i + 6]);
            re.coefficients[8 * i + 7] = change_t0_interval(re.coefficients[8 * i + 7]);
        }

        re
    }

    #[inline(always)]
    pub(crate) fn deserialize_to_vector_then_ntt<const DIMENSION: usize>(
        serialized: &[u8],
    ) -> [PolynomialRingElement; DIMENSION] {
        let mut ring_elements = [PolynomialRingElement::ZERO; DIMENSION];

        for (i, bytes) in serialized.chunks(RING_ELEMENT_OF_T0S_SIZE).enumerate() {
            ring_elements[i] = ntt(deserialize(bytes));
        }

        ring_elements
    }
}

// ---------------------------------------------------------------------------
// Functions for serializing and deserializing the ring element t1.
// ---------------------------------------------------------------------------

pub(crate) mod t1 {
    use crate::{arithmetic::PolynomialRingElement, constants::RING_ELEMENT_OF_T1S_SIZE};
    #[inline(always)]
    pub(crate) fn serialize(re: PolynomialRingElement) -> [u8; RING_ELEMENT_OF_T1S_SIZE] {
        let mut serialized = [0u8; RING_ELEMENT_OF_T1S_SIZE];

        for (i, coefficients) in re.coefficients.chunks_exact(4).enumerate() {
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
}

// ---------------------------------------------------------------------------
// Functions for serializing and deserializing an error ring element.
// ---------------------------------------------------------------------------

pub(crate) mod error {
    use crate::{arithmetic::PolynomialRingElement, ntt::ntt};

    #[inline(always)]
    fn serialize_when_eta_is_2<const OUTPUT_SIZE: usize>(
        re: PolynomialRingElement,
    ) -> [u8; OUTPUT_SIZE] {
        let mut serialized = [0u8; OUTPUT_SIZE];
        const ETA: i32 = 2;

        for (i, coefficients) in re.coefficients.chunks_exact(8).enumerate() {
            let coefficient0 = (ETA - coefficients[0]) as u8;
            let coefficient1 = (ETA - coefficients[1]) as u8;
            let coefficient2 = (ETA - coefficients[2]) as u8;
            let coefficient3 = (ETA - coefficients[3]) as u8;
            let coefficient4 = (ETA - coefficients[4]) as u8;
            let coefficient5 = (ETA - coefficients[5]) as u8;
            let coefficient6 = (ETA - coefficients[6]) as u8;
            let coefficient7 = (ETA - coefficients[7]) as u8;

            serialized[3 * i + 0] = (coefficient2 << 6) | (coefficient1 << 3) | coefficient0;
            serialized[3 * i + 1] = (coefficient5 << 7)
                | (coefficient4 << 4)
                | (coefficient3 << 1)
                | (coefficient2 >> 2);
            serialized[3 * i + 2] = (coefficient7 << 5) | (coefficient6 << 2) | (coefficient5 >> 1);
        }

        serialized
    }

    #[inline(always)]
    fn serialize_when_eta_is_4<const OUTPUT_SIZE: usize>(
        re: PolynomialRingElement,
    ) -> [u8; OUTPUT_SIZE] {
        let mut serialized = [0u8; OUTPUT_SIZE];
        const ETA: i32 = 4;

        for (i, coefficients) in re.coefficients.chunks_exact(2).enumerate() {
            let coefficient0 = (ETA - coefficients[0]) as u8;
            let coefficient1 = (ETA - coefficients[1]) as u8;
            serialized[i] = (coefficient1 << 4) | coefficient0;
        }

        serialized
    }

    #[inline(always)]
    pub(crate) fn serialize<const ETA: usize, const OUTPUT_SIZE: usize>(
        re: PolynomialRingElement,
    ) -> [u8; OUTPUT_SIZE] {
        match ETA {
            2 => serialize_when_eta_is_2::<OUTPUT_SIZE>(re),
            4 => serialize_when_eta_is_4::<OUTPUT_SIZE>(re),
            _ => unreachable!(),
        }
    }

    #[inline(always)]
    fn deserialize_when_eta_is_2(serialized: &[u8]) -> PolynomialRingElement {
        let mut re = PolynomialRingElement::ZERO;
        const ETA: i32 = 2;

        for (i, bytes) in serialized.chunks_exact(3).enumerate() {
            let byte0 = bytes[0] as i32;
            let byte1 = bytes[1] as i32;
            let byte2 = bytes[2] as i32;

            re.coefficients[8 * i + 0] = (byte0 >> 0) & 7;
            re.coefficients[8 * i + 1] = (byte0 >> 3) & 7;
            re.coefficients[8 * i + 2] = ((byte0 >> 6) | (byte1 << 2)) & 7;
            re.coefficients[8 * i + 3] = (byte1 >> 1) & 7;
            re.coefficients[8 * i + 4] = (byte1 >> 4) & 7;
            re.coefficients[8 * i + 5] = ((byte1 >> 7) | (byte2 << 1)) & 7;
            re.coefficients[8 * i + 6] = (byte2 >> 2) & 7;
            re.coefficients[8 * i + 7] = (byte2 >> 5) & 7;

            re.coefficients[8 * i + 0] = ETA - re.coefficients[8 * i + 0];
            re.coefficients[8 * i + 1] = ETA - re.coefficients[8 * i + 1];
            re.coefficients[8 * i + 2] = ETA - re.coefficients[8 * i + 2];
            re.coefficients[8 * i + 3] = ETA - re.coefficients[8 * i + 3];
            re.coefficients[8 * i + 4] = ETA - re.coefficients[8 * i + 4];
            re.coefficients[8 * i + 5] = ETA - re.coefficients[8 * i + 5];
            re.coefficients[8 * i + 6] = ETA - re.coefficients[8 * i + 6];
            re.coefficients[8 * i + 7] = ETA - re.coefficients[8 * i + 7];
        }

        re
    }

    #[inline(always)]
    fn deserialize_when_eta_is_4(serialized: &[u8]) -> PolynomialRingElement {
        let mut re = PolynomialRingElement::ZERO;
        const ETA: i32 = 4;

        for (i, byte) in serialized.into_iter().enumerate() {
            re.coefficients[2 * i + 0] = ETA - ((byte & 0xF) as i32);
            re.coefficients[2 * i + 1] = ETA - ((byte >> 4) as i32);
        }

        re
    }

    #[inline(always)]
    pub(crate) fn deserialize<const ETA: usize>(serialized: &[u8]) -> PolynomialRingElement {
        match ETA {
            2 => deserialize_when_eta_is_2(serialized),
            4 => deserialize_when_eta_is_4(serialized),
            _ => unreachable!(),
        }
    }

    #[inline(always)]
    pub(crate) fn deserialize_to_vector_then_ntt<
        const DIMENSION: usize,
        const ETA: usize,
        const RING_ELEMENT_SIZE: usize,
    >(
        serialized: &[u8],
    ) -> [PolynomialRingElement; DIMENSION] {
        let mut ring_elements = [PolynomialRingElement::ZERO; DIMENSION];

        for (i, bytes) in serialized.chunks(RING_ELEMENT_SIZE).enumerate() {
            ring_elements[i] = ntt(deserialize::<ETA>(bytes));
        }

        ring_elements
    }
}

// ---------------------------------------------------------------------------
// Functions for serializing and deserializing a mask ring element.
// ---------------------------------------------------------------------------

pub(crate) mod gamma1 {
    use crate::arithmetic::PolynomialRingElement;

    #[inline(always)]
    fn serialize_when_gamma1_is_2_pow_17<const OUTPUT_SIZE: usize>(
        re: PolynomialRingElement,
    ) -> [u8; OUTPUT_SIZE] {
        let mut serialized = [0u8; OUTPUT_SIZE];
        const GAMMA1: i32 = 1 << 17;

        for (i, coefficients) in re.coefficients.chunks_exact(4).enumerate() {
            let coefficient0 = GAMMA1 - coefficients[0];
            let coefficient1 = GAMMA1 - coefficients[1];
            let coefficient2 = GAMMA1 - coefficients[2];
            let coefficient3 = GAMMA1 - coefficients[3];

            serialized[9 * i + 0] = coefficient0 as u8;
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
        re: PolynomialRingElement,
    ) -> [u8; OUTPUT_SIZE] {
        let mut serialized = [0u8; OUTPUT_SIZE];
        const GAMMA1: i32 = 1 << 19;

        for (i, coefficients) in re.coefficients.chunks_exact(2).enumerate() {
            let coefficient0 = GAMMA1 - coefficients[0];
            let coefficient1 = GAMMA1 - coefficients[1];

            serialized[5 * i + 0] = coefficient0 as u8;
            serialized[5 * i + 1] = (coefficient0 >> 8) as u8;

            serialized[5 * i + 2] = (coefficient0 >> 16) as u8;
            serialized[5 * i + 2] |= (coefficient1 << 4) as u8;

            serialized[5 * i + 3] = (coefficient1 >> 4) as u8;
            serialized[5 * i + 4] = (coefficient1 >> 12) as u8;
        }

        serialized
    }

    #[inline(always)]
    pub(crate) fn serialize<const GAMMA1_EXPONENT: usize, const OUTPUT_SIZE: usize>(
        re: PolynomialRingElement,
    ) -> [u8; OUTPUT_SIZE] {
        match GAMMA1_EXPONENT {
            17 => serialize_when_gamma1_is_2_pow_17(re),
            19 => serialize_when_gamma1_is_2_pow_19(re),
            _ => unreachable!(),
        }
    }

    #[inline(always)]
    fn deserialize_when_gamma1_is_2_pow_17(serialized: &[u8]) -> PolynomialRingElement {
        const GAMMA1: i32 = 1 << 17;
        const GAMMA1_TIMES_2_BITMASK: i32 = (GAMMA1 << 1) - 1;

        let mut re = PolynomialRingElement::ZERO;

        for (i, bytes) in serialized.chunks_exact(9).enumerate() {
            re.coefficients[4 * i + 0] = bytes[0] as i32;
            re.coefficients[4 * i + 0] |= (bytes[1] as i32) << 8;
            re.coefficients[4 * i + 0] |= (bytes[2] as i32) << 16;
            re.coefficients[4 * i + 0] &= GAMMA1_TIMES_2_BITMASK;

            re.coefficients[4 * i + 1] = (bytes[2] as i32) >> 2;
            re.coefficients[4 * i + 1] |= (bytes[3] as i32) << 6;
            re.coefficients[4 * i + 1] |= (bytes[4] as i32) << 14;
            re.coefficients[4 * i + 1] &= GAMMA1_TIMES_2_BITMASK;

            re.coefficients[4 * i + 2] = (bytes[4] as i32) >> 4;
            re.coefficients[4 * i + 2] |= (bytes[5] as i32) << 4;
            re.coefficients[4 * i + 2] |= (bytes[6] as i32) << 12;
            re.coefficients[4 * i + 2] &= GAMMA1_TIMES_2_BITMASK;

            re.coefficients[4 * i + 3] = (bytes[6] as i32) >> 6;
            re.coefficients[4 * i + 3] |= (bytes[7] as i32) << 2;
            re.coefficients[4 * i + 3] |= (bytes[8] as i32) << 10;
            re.coefficients[4 * i + 3] &= GAMMA1_TIMES_2_BITMASK;

            re.coefficients[4 * i + 0] = GAMMA1 - re.coefficients[4 * i + 0];
            re.coefficients[4 * i + 1] = GAMMA1 - re.coefficients[4 * i + 1];
            re.coefficients[4 * i + 2] = GAMMA1 - re.coefficients[4 * i + 2];
            re.coefficients[4 * i + 3] = GAMMA1 - re.coefficients[4 * i + 3];
        }

        re
    }

    #[inline(always)]
    fn deserialize_when_gamma1_is_2_pow_19(serialized: &[u8]) -> PolynomialRingElement {
        const GAMMA1: i32 = 1 << 19;
        const GAMMA1_TIMES_2_BITMASK: i32 = (GAMMA1 << 1) - 1;

        let mut re = PolynomialRingElement::ZERO;

        for (i, bytes) in serialized.chunks_exact(5).enumerate() {
            re.coefficients[2 * i + 0] = bytes[0] as i32;
            re.coefficients[2 * i + 0] |= (bytes[1] as i32) << 8;
            re.coefficients[2 * i + 0] |= (bytes[2] as i32) << 16;
            re.coefficients[2 * i + 0] &= GAMMA1_TIMES_2_BITMASK;

            re.coefficients[2 * i + 1] = (bytes[2] as i32) >> 4;
            re.coefficients[2 * i + 1] |= (bytes[3] as i32) << 4;
            re.coefficients[2 * i + 1] |= (bytes[4] as i32) << 12;

            re.coefficients[2 * i + 0] = GAMMA1 - re.coefficients[2 * i + 0];
            re.coefficients[2 * i + 1] = GAMMA1 - re.coefficients[2 * i + 1];
        }

        re
    }

    #[inline(always)]
    pub(crate) fn deserialize<const GAMMA1_EXPONENT: usize>(
        serialized: &[u8],
    ) -> PolynomialRingElement {
        match GAMMA1_EXPONENT {
            17 => deserialize_when_gamma1_is_2_pow_17(serialized),
            19 => deserialize_when_gamma1_is_2_pow_19(serialized),
            _ => unreachable!(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::arithmetic::PolynomialRingElement;

    #[test]
    fn test_t0_serialize() {
        let re = PolynomialRingElement {
            coefficients: [
                -1072, -3712, -3423, -27, 1995, 3750, -922, 3806, 2356, 3801, -1709, -2709, 1191,
                108, -593, -3081, -949, -926, 3107, -3820, 379, 3747, -2910, -2370, 939, 3218,
                -3190, 1311, 1110, -2717, -1191, -1019, -2478, -1860, -4018, 2615, -3208, 337,
                -3406, -1225, -261, -329, -3624, -726, -3159, 3407, 4042, 2124, 2921, 1507, 279,
                -2830, -2850, -4011, 402, 1510, -2648, -168, 18, 652, 3443, 1723, 3112, -1605,
                -3885, 3174, 832, -3424, 2886, 3815, 2064, 1757, 3298, 3365, -1489, -1021, 1594,
                3630, -3352, 1055, -2914, -816, 864, -1251, 2628, -3199, 549, -1966, 419, 685,
                -3414, -3673, -3939, -1422, -3994, 4073, 86, -1703, 1179, 758, -3588, 3427, -1798,
                -2139, -456, -547, -3741, 3191, -2432, 1213, -3415, -3825, -1993, -763, -1757, 887,
                1587, -1995, -887, -873, 1152, -1897, 2738, 2867, 1952, 3834, 3562, 3118, -768,
                1400, 3883, 2636, 456, -3884, -1726, -3232, 2373, -1039, 591, 1975, 1634, 459,
                -595, 2864, 3619, 3288, -2180, 4048, -2469, 1826, 1764, -1345, 3761, 2320, 3935,
                -1219, -1397, 214, -1008, 299, -3270, -2628, 1070, 2904, 1597, 3471, 2383, -417,
                -3456, 327, 3997, 1662, -3363, 2033, 1180, 1625, 923, -1911, -3511, -41, 1525,
                -3882, -3104, 3023, 3794, -1028, 3818, -3216, -2875, -1755, -354, -3137, -1546,
                -3535, -1156, 1802, -1081, 3726, 3067, 773, 2408, 72, 810, 3607, -1524, 3478, 3409,
                3377, 3159, 159, -706, -60, 1462, 2224, 2279, 2373, -3027, -78, 405, -4078, 2697,
                3474, -3611, 3632, 1229, 2396, -3729, -1110, 290, -2861, 3018, 122, 1177, -3123,
                -3583, 2683, 2743, 2888, -2104, 874, -1150, -2453, -125, -2561, -2011, -2384, 2259,
                -10, 836, -2773, 2487, -2292, -201, -3235, 1232, -3197,
            ],
        };

        let expected_re_serialized = [
            48, 20, 208, 127, 245, 13, 88, 131, 180, 130, 230, 20, 9, 204, 230, 36, 180, 218, 74,
            157, 181, 40, 95, 148, 76, 224, 181, 211, 115, 118, 15, 118, 95, 232, 186, 130, 215,
            22, 202, 85, 204, 109, 216, 241, 112, 165, 186, 58, 245, 41, 221, 159, 174, 153, 232,
            202, 254, 228, 130, 200, 95, 157, 83, 79, 166, 5, 49, 41, 162, 120, 107, 121, 197, 99,
            133, 13, 160, 61, 151, 164, 67, 165, 59, 135, 45, 178, 87, 191, 155, 211, 80, 88, 26,
            21, 186, 63, 186, 214, 40, 138, 18, 246, 40, 178, 45, 95, 115, 0, 51, 176, 174, 75, 50,
            2, 252, 25, 73, 30, 99, 91, 68, 215, 254, 105, 156, 164, 3, 70, 15, 95, 98, 27, 102,
            130, 178, 113, 202, 91, 254, 248, 118, 115, 189, 93, 110, 170, 89, 245, 44, 63, 246,
            29, 171, 230, 191, 0, 170, 239, 212, 150, 45, 133, 70, 224, 59, 133, 193, 221, 194,
            200, 113, 68, 118, 250, 196, 1, 152, 135, 214, 85, 143, 247, 201, 119, 95, 118, 219,
            68, 214, 156, 150, 239, 221, 76, 155, 128, 43, 237, 58, 149, 102, 2, 134, 12, 130, 133,
            144, 30, 0, 19, 81, 85, 3, 218, 130, 227, 88, 190, 175, 5, 229, 187, 230, 129, 198,
            182, 36, 228, 153, 106, 220, 148, 132, 38, 221, 1, 101, 16, 98, 24, 80, 154, 189, 17,
            71, 10, 170, 79, 1, 222, 132, 130, 97, 90, 87, 85, 30, 252, 172, 118, 198, 156, 72, 75,
            47, 84, 50, 156, 226, 68, 172, 9, 141, 128, 61, 215, 141, 1, 193, 52, 210, 31, 16, 217,
            58, 77, 101, 236, 238, 222, 246, 20, 184, 160, 84, 62, 8, 143, 33, 46, 129, 128, 90, 4,
            72, 190, 179, 183, 173, 88, 12, 226, 10, 246, 185, 19, 82, 123, 148, 67, 229, 66, 1,
            217, 103, 152, 6, 247, 89, 179, 244, 64, 95, 213, 196, 171, 120, 22, 169, 35, 236, 9,
            75, 30, 168, 164, 160, 78, 198, 217, 53, 211, 219, 9, 174, 57, 247, 127, 87, 220, 196,
            134, 135, 14, 51, 139, 212, 68, 122, 43, 234, 237, 90, 182, 13, 49, 124, 103, 107, 134,
            255, 247, 194, 146, 84, 112, 9, 14, 182, 100, 126, 180, 50, 247, 193, 0, 189, 125, 161,
            114, 203, 81, 128, 188, 172, 90, 39, 25, 122, 156, 12, 71, 57, 204, 234, 227,
        ];

        assert_eq!(t0::serialize(re), expected_re_serialized);
    }

    #[test]
    fn test_deserialize_to_t0() {
        let serialized = [
            142, 115, 136, 74, 18, 206, 88, 7, 0, 22, 20, 228, 219, 113, 49, 227, 242, 177, 86, 8,
            110, 150, 82, 137, 103, 225, 186, 160, 235, 159, 98, 45, 123, 187, 93, 112, 177, 99,
            251, 129, 207, 135, 162, 175, 115, 126, 16, 1, 68, 214, 247, 203, 33, 148, 238, 24, 92,
            61, 61, 70, 127, 17, 66, 65, 162, 196, 167, 28, 225, 232, 40, 224, 246, 214, 32, 44, 0,
            64, 182, 68, 10, 16, 127, 154, 193, 64, 220, 171, 165, 110, 54, 86, 243, 191, 193, 96,
            102, 104, 85, 97, 195, 220, 185, 8, 98, 225, 29, 111, 9, 154, 159, 243, 83, 167, 78,
            106, 106, 46, 37, 117, 135, 86, 12, 164, 2, 139, 19, 89, 160, 108, 163, 85, 44, 92,
            165, 163, 89, 231, 204, 238, 154, 211, 104, 62, 245, 69, 55, 19, 240, 91, 3, 107, 179,
            195, 198, 23, 104, 95, 134, 200, 100, 224, 188, 54, 149, 209, 120, 104, 162, 62, 251,
            175, 105, 37, 2, 241, 62, 147, 210, 96, 89, 232, 131, 193, 167, 154, 122, 85, 23, 17,
            130, 227, 120, 89, 120, 5, 76, 28, 116, 125, 92, 136, 19, 239, 246, 150, 215, 151, 153,
            79, 157, 252, 136, 86, 115, 251, 95, 170, 181, 223, 2, 210, 134, 84, 40, 177, 151, 148,
            82, 254, 195, 81, 161, 173, 141, 161, 65, 254, 179, 54, 53, 243, 145, 27, 157, 62, 39,
            161, 234, 177, 25, 47, 82, 228, 236, 162, 68, 252, 94, 90, 4, 137, 43, 183, 221, 79,
            218, 218, 78, 243, 237, 180, 32, 92, 75, 15, 210, 71, 59, 254, 113, 145, 98, 26, 99,
            79, 204, 24, 150, 162, 219, 250, 92, 252, 112, 109, 203, 75, 20, 133, 166, 243, 231,
            120, 220, 28, 149, 7, 77, 128, 3, 48, 203, 190, 8, 116, 79, 149, 166, 187, 60, 34, 221,
            241, 217, 2, 38, 57, 118, 243, 26, 174, 47, 4, 240, 77, 188, 119, 126, 239, 235, 207,
            105, 14, 59, 223, 155, 108, 56, 53, 39, 134, 181, 79, 78, 189, 98, 123, 52, 69, 242,
            124, 194, 30, 190, 206, 2, 185, 8, 150, 250, 186, 47, 147, 129, 27, 67, 45, 124, 165,
            37, 165, 223, 215, 169, 175, 63, 43, 16, 181, 202, 134, 66, 162, 246, 48, 30, 235, 124,
            145, 86, 76, 50, 247, 213, 157, 68, 112, 162, 228, 14, 164, 240, 198, 232, 176,
        ];

        let expected_coefficients = [
            -910, -1091, 2926, -412, 3979, 1280, -80, -2940, -369, -1817, 900, -173, 2336, 1717,
            -3621, -3116, 3910, -3933, -2215, -1626, -2999, -2094, 315, -3948, 127, -1086, 1048,
            -3303, -263, 3584, -3929, -2430, -1057, 2188, -1798, -2682, -1123, 1857, 2808, -1096,
            2108, 1819, -2616, 4015, 146, -107, 3920, 2048, 2890, 4014, -4036, 3276, 3060, -1518,
            -2710, 2355, -854, 513, -2096, -204, -1366, 3664, 2189, 3817, 3742, -2287, 3493, -3892,
            -3897, -937, 1734, 691, 2770, -2985, -1441, 2024, -42, 1595, 3740, 620, -1443, 3742,
            1705, -839, 395, -1894, 405, 742, -1342, -2607, 2867, -2016, -53, -2485, -2830, 3336,
            -3944, 3022, -2354, -2496, -875, 1846, 3613, -1101, -2878, 641, 1702, 3580, -1007,
            1719, 2685, -3339, 3709, -1342, -3750, 342, 3823, -449, 2589, 245, 1019, 3870, -3933,
            -184, -312, -2935, -3675, -762, 103, 2838, 3521, 2387, -4023, -1327, -3798, 4005, 2350,
            3420, 950, 1745, 2775, 3585, 2745, -1460, 3699, -525, 769, 1427, -3891, 568, -2676,
            2841, 1375, 625, 1082, 1884, 306, 3503, -3057, 1205, 1788, -2396, -1901, -1183, 595,
            -2471, -951, 3050, 1188, -122, -500, -3190, -1823, -328, 919, 1556, -2252, -1200,
            -1768, -2549, 59, -1720, 211, 3447, 2427, -3997, -3641, -2488, -2385, 2429, 511, 2560,
            -3787, 4027, -989, 726, 1094, -286, 2188, -2878, 2558, -457, -3293, -3125, 3334, -2050,
            -311, 265, 130, -3935, -2675, -1564, -3571, -1613, -1249, 2842, -1414, -637, 173,
            -1733, -839, -2338, 1549, 3112, 322, 2026, 3538, -1324, -2991, 1641, 506, 1949, -3117,
            725, 1719, 65, -2717, -4055, 3924, -1698, 2358, -532, -3496, -3169, 335, 1858, -346,
            2487, -1527, 2834, -3089, 1724, 3858, -2130, 3301, -1565,
        ];

        assert_eq!(
            t0::deserialize(&serialized).coefficients,
            expected_coefficients
        );
    }

    #[test]
    fn test_serialize_t1() {
        let re = PolynomialRingElement {
            coefficients: [
                127, 627, 86, 834, 463, 169, 792, 8, 595, 212, 1015, 213, 321, 501, 471, 633, 686,
                333, 973, 464, 737, 30, 761, 358, 659, 607, 177, 826, 147, 995, 89, 365, 302, 585,
                406, 76, 535, 406, 952, 664, 102, 270, 879, 877, 127, 437, 1010, 418, 695, 596,
                847, 131, 1004, 228, 882, 433, 39, 569, 284, 225, 676, 740, 712, 165, 912, 71, 491,
                887, 668, 607, 919, 607, 891, 647, 904, 957, 846, 256, 353, 57, 712, 98, 200, 722,
                734, 596, 187, 470, 501, 524, 1000, 435, 195, 594, 834, 848, 438, 548, 819, 533,
                898, 777, 676, 284, 215, 95, 811, 134, 338, 915, 12, 951, 124, 246, 365, 532, 359,
                561, 280, 923, 236, 299, 916, 394, 266, 946, 645, 872, 898, 228, 737, 229, 452,
                562, 355, 403, 321, 161, 202, 983, 306, 898, 172, 304, 921, 796, 232, 1011, 293,
                183, 130, 376, 874, 1018, 501, 154, 747, 62, 262, 185, 397, 208, 75, 933, 459, 687,
                574, 803, 570, 635, 57, 548, 253, 970, 583, 425, 626, 562, 96, 52, 715, 240, 58,
                451, 888, 932, 179, 632, 605, 394, 941, 646, 286, 217, 477, 443, 80, 639, 64, 139,
                394, 227, 2, 927, 455, 719, 377, 533, 438, 120, 788, 811, 650, 402, 240, 516, 354,
                950, 372, 105, 247, 762, 445, 108, 1009, 862, 885, 870, 53, 346, 392, 710, 434, 72,
                899, 610, 543, 937, 501, 41, 615, 97, 557, 168, 105, 665, 179, 708, 137, 849, 508,
                742, 512, 879, 534, 490,
            ],
        };

        let expected_re_serialized = [
            127, 204, 105, 133, 208, 207, 165, 130, 49, 2, 83, 82, 115, 127, 53, 65, 213, 119, 93,
            158, 174, 54, 213, 60, 116, 225, 122, 144, 175, 89, 147, 126, 25, 139, 206, 147, 140,
            159, 69, 91, 46, 37, 105, 25, 19, 23, 90, 134, 59, 166, 102, 56, 244, 118, 219, 127,
            212, 38, 191, 104, 183, 82, 249, 244, 32, 236, 147, 35, 119, 108, 39, 228, 200, 81, 56,
            164, 146, 139, 108, 41, 144, 31, 177, 222, 221, 156, 126, 121, 249, 151, 123, 31, 138,
            120, 239, 78, 3, 20, 86, 14, 200, 138, 129, 140, 180, 222, 82, 185, 139, 117, 245, 49,
            136, 254, 108, 195, 72, 41, 52, 212, 182, 145, 56, 115, 133, 130, 39, 76, 42, 71, 215,
            124, 177, 178, 33, 82, 77, 206, 192, 237, 124, 216, 211, 22, 133, 103, 197, 136, 209,
            230, 236, 172, 68, 185, 98, 10, 201, 94, 40, 218, 130, 147, 19, 110, 57, 196, 201, 56,
            214, 100, 65, 133, 162, 204, 245, 50, 9, 206, 10, 76, 153, 115, 140, 206, 252, 37, 221,
            34, 8, 94, 106, 235, 95, 159, 38, 235, 250, 96, 80, 46, 141, 65, 179, 68, 233, 203,
            189, 234, 227, 200, 58, 238, 153, 3, 137, 253, 40, 127, 100, 106, 114, 202, 8, 6, 13,
            203, 194, 163, 195, 112, 120, 147, 62, 11, 158, 93, 42, 214, 186, 161, 30, 101, 211,
            221, 110, 80, 252, 9, 196, 34, 138, 141, 35, 192, 231, 199, 61, 155, 87, 133, 182, 225,
            65, 241, 202, 138, 74, 6, 15, 129, 98, 217, 78, 87, 26, 247, 232, 219, 27, 27, 241,
            123, 93, 183, 217, 53, 104, 133, 152, 177, 178, 33, 49, 184, 152, 31, 166, 94, 95, 10,
            103, 134, 209, 34, 42, 105, 100, 58, 11, 177, 137, 68, 205, 159, 185, 0, 190, 109, 161,
            122,
        ];

        assert_eq!(t1::serialize(re), expected_re_serialized);
    }

    #[test]
    fn test_deserialize_to_error_when_eta_is_2() {
        let serialized = [
            220, 24, 44, 136, 134, 36, 11, 195, 72, 82, 34, 144, 36, 33, 9, 196, 22, 70, 100, 148,
            65, 32, 163, 1, 210, 40, 14, 224, 38, 72, 33, 41, 136, 156, 146, 80, 25, 37, 50, 92,
            66, 140, 227, 144, 96, 9, 64, 141, 193, 50, 1, 140, 20, 141, 92, 32, 97, 2, 25, 42, 34,
            66, 50, 193, 72, 113, 202, 8, 16, 209, 54, 44, 129, 194, 48, 144, 20, 141, 228, 166,
            141, 228, 20, 144, 146, 54, 12, 99, 4, 140, 226, 18, 12, 194, 38, 97,
        ];

        let expected_coefficients = [
            -2, -1, -1, -2, 1, 2, -1, 1, 2, 1, 0, -1, 2, 1, 1, 1, -1, 1, -2, 1, -2, 1, 0, 0, 0, 0,
            1, 1, 0, 2, -2, -2, -2, -2, -2, 2, 0, 0, 0, 2, -2, 2, -1, -1, 1, -2, 1, 0, -2, -2, 1,
            0, 1, -1, 2, 0, 2, -2, -2, 1, 0, -1, 2, 2, 0, 0, -1, -2, 0, -2, -1, 2, 2, -2, -1, -1,
            0, 2, 0, 0, 1, -2, -2, -2, 0, 2, 0, -2, -2, -1, 0, 1, 1, 1, -2, 0, 1, -1, -2, 0, 0, -2,
            -2, 1, -2, -1, 1, 1, -2, 2, -1, -2, -1, -2, -1, 2, 1, 1, 2, -1, 1, 1, 2, 2, -2, 0, -1,
            -2, 1, 2, -1, 1, -1, 0, 2, 2, -2, 1, 0, 0, 1, 0, -1, -2, -2, -1, 1, 2, 0, 0, 2, -1, 0,
            2, -2, -2, 1, -2, 0, 1, 0, -2, 2, 1, -2, -2, -2, 1, 1, 2, -1, -2, -2, 0, -2, -1, 0, 1,
            -1, -2, 2, 2, -2, 2, 1, 0, -1, -1, -1, 2, -1, 1, 1, 2, 0, 1, -2, 1, -2, 1, 2, 0, 0, 0,
            1, 0, -1, -2, -2, -2, -1, -1, 0, -1, -1, -2, -2, -2, -1, 0, 1, 2, -2, -2, 0, 0, 0, -1,
            -1, 2, -1, 2, -1, -2, 1, 0, 2, 2, -1, -2, 0, -2, -1, 1, 1, 2, -1, 2, 0, 2, -1, -1, 0,
            0, 2, -1,
        ];

        assert_eq!(
            error::deserialize::<2>(&serialized).coefficients,
            expected_coefficients
        );
    }

    #[test]
    fn test_deserialize_to_error_when_eta_is_4() {
        let serialized = [
            22, 103, 55, 49, 34, 65, 50, 129, 52, 65, 21, 85, 82, 69, 3, 55, 52, 101, 80, 64, 114,
            136, 53, 8, 135, 67, 64, 71, 131, 21, 117, 81, 23, 99, 17, 84, 51, 23, 117, 56, 52, 85,
            131, 17, 22, 117, 85, 68, 34, 113, 87, 24, 65, 81, 2, 80, 118, 53, 34, 8, 32, 51, 51,
            82, 24, 2, 69, 0, 80, 68, 129, 133, 134, 17, 134, 82, 18, 21, 37, 114, 55, 87, 83, 8,
            80, 52, 103, 1, 84, 82, 99, 16, 86, 48, 16, 133, 17, 2, 67, 51, 120, 71, 19, 5, 72, 19,
            21, 103, 114, 115, 69, 36, 97, 68, 115, 56, 18, 83, 99, 32, 83, 88, 37, 71, 35, 82, 24,
            19,
        ];

        let expected_coefficients = [
            -2, 3, -3, -2, -3, 1, 3, 1, 2, 2, 3, 0, 2, 1, 3, -4, 0, 1, 3, 0, -1, 3, -1, -1, 2, -1,
            -1, 0, 1, 4, -3, 1, 0, 1, -1, -2, 4, -1, 4, 0, 2, -3, -4, -4, -1, 1, -4, 4, -3, -4, 1,
            0, 4, 0, -3, 0, 1, -4, -1, 3, -1, -3, 3, -1, -3, 3, 1, -2, 3, 3, 0, -1, 1, 1, -3, 3,
            -1, -3, -4, 1, 0, 1, -1, -1, 1, -4, 3, 3, -2, 3, -1, -3, -1, -1, 0, 0, 2, 2, 3, -3, -3,
            -1, -4, 3, 3, 0, 3, -1, 2, 4, 4, -1, -2, -3, -1, 1, 2, 2, -4, 4, 4, 2, 1, 1, 1, 1, 2,
            -1, -4, 3, 2, 4, -1, 0, 4, 4, 4, -1, 0, 0, 3, -4, -1, -4, -2, -4, 3, 3, -2, -4, 2, -1,
            2, 3, -1, 3, -1, 2, 2, -3, -3, 1, -3, -1, 1, -1, -4, 4, 4, -1, 0, 1, -3, -2, 3, 4, 0,
            -1, 2, -1, 1, -2, 4, 3, -2, -1, 4, 1, 4, 3, -1, -4, 3, 3, 2, 4, 1, 0, 1, 1, -4, -3, -3,
            0, 1, 3, -1, 4, -4, 0, 1, 3, -1, 3, -3, -2, 2, -3, 1, -3, -1, 0, 0, 2, 3, -2, 0, 0, 1,
            -3, -4, 1, 2, 3, 1, -1, 1, -2, 4, 2, 1, -1, -4, -1, -1, 2, -3, 0, 1, 2, 2, -1, -4, 3,
            1, 3,
        ];

        assert_eq!(
            error::deserialize::<4>(&serialized).coefficients,
            expected_coefficients
        );
    }

    #[test]
    fn test_deserialize_when_gamma1_is_2_pow_17() {
        let bytes = [
            198, 32, 33, 79, 53, 132, 46, 198, 17, 233, 84, 94, 175, 136, 13, 127, 137, 254, 113,
            82, 68, 239, 94, 176, 179, 22, 102, 177, 253, 142, 176, 250, 96, 201, 11, 213, 230, 41,
            207, 14, 252, 247, 44, 197, 61, 57, 233, 239, 7, 173, 48, 253, 53, 43, 107, 174, 112,
            33, 144, 137, 117, 234, 75, 181, 150, 72, 158, 193, 130, 225, 136, 17, 65, 227, 146,
            207, 208, 228, 176, 164, 158, 62, 142, 193, 250, 109, 210, 52, 182, 254, 148, 179, 247,
            164, 167, 177, 209, 148, 189, 86, 221, 208, 92, 28, 51, 228, 176, 249, 12, 142, 124,
            187, 37, 164, 131, 203, 222, 228, 211, 250, 222, 114, 123, 183, 44, 125, 14, 97, 12,
            64, 154, 168, 11, 96, 112, 93, 225, 58, 8, 110, 164, 69, 246, 67, 102, 109, 227, 41,
            170, 254, 3, 137, 7, 0, 7, 12, 89, 123, 133, 155, 52, 14, 80, 211, 96, 229, 7, 100,
            208, 68, 109, 222, 122, 84, 80, 163, 240, 121, 126, 235, 54, 72, 124, 163, 195, 30,
            207, 194, 158, 106, 46, 181, 90, 251, 232, 201, 121, 115, 110, 225, 245, 38, 111, 109,
            248, 202, 9, 161, 220, 240, 202, 155, 72, 236, 80, 97, 168, 67, 128, 160, 37, 56, 211,
            167, 71, 73, 215, 92, 101, 148, 227, 207, 180, 155, 233, 42, 144, 30, 28, 236, 184, 13,
            133, 206, 47, 170, 205, 59, 29, 209, 245, 226, 66, 69, 144, 146, 168, 83, 66, 233, 193,
            59, 79, 41, 167, 246, 246, 95, 161, 50, 105, 109, 255, 137, 188, 210, 189, 142, 91, 73,
            139, 24, 228, 30, 36, 133, 202, 123, 206, 244, 9, 229, 227, 255, 94, 198, 149, 5, 193,
            37, 72, 129, 16, 205, 245, 177, 242, 241, 120, 66, 137, 39, 20, 111, 197, 64, 89, 9,
            238, 114, 4, 212, 146, 75, 206, 58, 232, 33, 231, 186, 90, 202, 95, 49, 233, 209, 177,
            195, 88, 253, 80, 103, 112, 163, 245, 31, 6, 78, 119, 131, 17, 240, 77, 210, 72, 61, 1,
            104, 110, 70, 49, 83, 172, 187, 39, 53, 235, 40, 4, 19, 170, 110, 153, 249, 52, 6, 122,
            225, 235, 40, 196, 149, 80, 184, 69, 148, 61, 158, 255, 145, 72, 129, 51, 16, 2, 196,
            156, 146, 128, 107, 76, 122, 194, 42, 99, 240, 12, 213, 57, 55, 232, 145, 61, 45, 160,
            136, 168, 6, 128, 210, 250, 114, 174, 126, 230, 8, 228, 207, 143, 146, 135, 161, 201,
            156, 182, 241, 219, 217, 69, 27, 35, 156, 194, 91, 192, 115, 201, 22, 197, 145, 240,
            132, 11, 206, 138, 128, 139, 222, 212, 13, 212, 22, 92, 232, 216, 16, 69, 109, 55, 230,
            217, 210, 95, 192, 242, 193, 250, 91, 217, 140, 11, 98, 111, 8, 117, 91, 212, 63, 24,
            93, 161, 48, 241, 55, 11, 5, 171, 199, 212, 161, 230, 156, 205, 103, 171, 11, 226, 125,
            213, 216, 76, 17, 229, 56, 203, 30, 43, 39, 212, 232, 96, 198, 217, 109, 81, 125, 22,
            180, 195, 249, 20, 18, 57, 153, 132, 63, 206, 40, 137, 240, 149, 189, 220, 75, 227,
            142, 178, 214, 215, 101, 232, 204, 94, 189, 109, 236, 173, 200, 39, 114, 203, 136, 152,
            114, 173, 199, 38, 195, 46, 224, 68, 92, 129, 184, 157, 35,
        ];

        let expected_coefficients = [
            57146, 44088, -59459, 112872, -21737, -11223, -127192, -129573, 109967, -113617,
            -80645, 26534, -64945, -44067, 92657, -87087, -76262, -66483, -53119, 67820, -125241,
            -82427, -119562, 86825, 86421, 128932, -88217, 53335, 92491, 104558, -6188, 113117,
            -58177, 117788, -69197, -31378, 29122, -97968, -85286, -129752, -111508, 5827, 58598,
            -63059, 74410, -71476, -17201, -124611, 94708, 37153, 116158, -97070, -54244, 84034,
            -96183, 2894, 106226, -36867, 83319, 16000, -57693, -98830, 107962, 61479, -93542,
            -35448, 114710, 123356, 129280, -54851, 18345, 116526, 76976, 1704, 63936, 19181,
            99618, 76779, -106250, -110073, 112586, 71457, 69140, -31499, 53654, -54957, 90481,
            12825, 7826, -117181, -100054, 121045, 74591, -62140, -50313, 31421, 113752, 38880,
            52350, 57697, 75959, 59049, 65991, -28371, 120087, -67492, -102081, -5174, -12238,
            -62314, 60973, -101335, 113342, -9380, 121542, -67493, 45253, 22070, 145, 79227,
            -93545, -74367, -122155, 37318, 95415, -112902, 110015, 4310, 2866, 67262, 4098,
            -22297, 16123, 110071, 77560, -51159, 69134, -20638, 48520, -71100, 42688, 83070,
            49081, 53685, 116018, 14214, 21586, 32983, 5839, 70540, -120204, 25277, 23696, 30723,
            -95456, 113139, -19952, -86580, -32787, 58951, 109775, 4373, -45906, 126813, -43539,
            -26203, 105649, -99816, 120597, 121487, 107643, 68015, 98, 110044, 64712, -69640,
            93540, -72416, 120924, 29525, 62224, 12683, 57725, 84746, 96096, 130646, -109864,
            -47563, 72066, -129282, 55044, -34334, -40137, -64621, 107107, 95123, -115356, 69610,
            37737, -18196, -99568, -45954, 83960, -86906, -54285, -5893, 62066, 19180, 6601,
            -128182, -76805, -125703, 75429, 97565, 96522, 37420, 114732, 108730, -70410, 119585,
            -109317, 101071, 12694, 24778, -2987, 41096, 78451, -103493, -52024, 13625, -36162,
            -72067, 37415, 24748, 115903, 109593, 50926, -123174, -36067, -115236, 82539, 77065,
            -76014, -89946, 71579, -87987, -50907, -74423, -94759, -8754, -55081, 91362, 119101,
            -69944, -100373, 94602,
        ];

        assert_eq!(
            gamma1::deserialize::<17>(&bytes).coefficients,
            expected_coefficients
        );
    }

    #[test]
    fn test_deserialize_when_gamma1_is_2_pow_19() {
        let bytes: [u8; 640] = [
            253, 11, 216, 60, 251, 71, 79, 187, 242, 250, 209, 44, 72, 206, 98, 3, 22, 91, 184, 22,
            197, 50, 249, 184, 253, 104, 8, 3, 9, 116, 147, 157, 110, 167, 67, 218, 30, 79, 58, 12,
            2, 72, 239, 104, 6, 162, 57, 195, 128, 18, 93, 245, 0, 132, 218, 172, 178, 214, 243,
            53, 171, 128, 90, 13, 126, 226, 148, 153, 238, 106, 146, 46, 220, 184, 140, 28, 167,
            18, 38, 212, 17, 6, 136, 251, 94, 47, 164, 196, 66, 120, 204, 45, 111, 37, 45, 51, 38,
            109, 32, 32, 144, 122, 13, 52, 144, 108, 75, 152, 73, 164, 139, 91, 26, 37, 76, 237,
            211, 47, 124, 0, 210, 175, 145, 149, 28, 19, 81, 38, 3, 121, 106, 191, 144, 129, 93,
            118, 202, 8, 163, 27, 182, 42, 148, 249, 166, 67, 198, 69, 164, 49, 157, 40, 230, 39,
            126, 108, 93, 96, 211, 185, 61, 99, 30, 83, 183, 241, 30, 16, 91, 76, 200, 55, 228, 22,
            33, 142, 114, 240, 217, 138, 155, 223, 136, 77, 216, 181, 102, 56, 218, 49, 91, 223,
            67, 68, 190, 216, 214, 180, 230, 199, 165, 17, 171, 151, 156, 33, 125, 248, 0, 56, 104,
            184, 150, 91, 83, 138, 61, 162, 255, 96, 168, 189, 86, 60, 76, 36, 163, 207, 76, 227,
            76, 180, 145, 125, 229, 251, 212, 77, 115, 88, 177, 134, 20, 122, 27, 211, 207, 254,
            233, 226, 31, 112, 10, 181, 117, 97, 56, 188, 176, 229, 156, 140, 97, 31, 64, 139, 249,
            217, 172, 100, 70, 121, 130, 94, 182, 245, 239, 138, 4, 65, 64, 228, 118, 200, 128, 94,
            143, 59, 53, 12, 185, 209, 191, 52, 91, 170, 161, 200, 12, 223, 221, 54, 151, 218, 3,
            156, 49, 176, 78, 50, 117, 16, 36, 179, 203, 91, 222, 181, 53, 151, 211, 229, 22, 49,
            247, 223, 195, 241, 1, 44, 157, 56, 48, 158, 25, 246, 231, 54, 106, 197, 107, 199, 252,
            60, 182, 216, 27, 129, 32, 149, 8, 239, 44, 176, 119, 104, 207, 77, 206, 150, 220, 18,
            172, 54, 140, 37, 235, 243, 23, 220, 149, 241, 197, 149, 240, 41, 223, 179, 98, 188,
            135, 231, 56, 176, 102, 173, 39, 46, 236, 79, 177, 224, 17, 164, 88, 227, 108, 214,
            234, 106, 253, 242, 27, 120, 44, 44, 63, 117, 135, 97, 90, 239, 81, 138, 112, 203, 188,
            13, 239, 224, 37, 53, 1, 27, 33, 26, 213, 36, 129, 146, 254, 82, 106, 111, 179, 25,
            199, 217, 243, 188, 250, 141, 136, 148, 154, 241, 152, 195, 225, 82, 174, 149, 124,
            237, 3, 81, 218, 90, 157, 6, 243, 34, 62, 141, 211, 164, 2, 103, 45, 46, 253, 115, 244,
            216, 191, 245, 177, 121, 216, 86, 131, 66, 63, 18, 167, 41, 199, 241, 195, 117, 168,
            134, 193, 73, 201, 83, 197, 85, 147, 217, 45, 162, 18, 203, 166, 95, 166, 159, 8, 1,
            110, 125, 113, 228, 180, 78, 194, 174, 60, 172, 124, 151, 23, 202, 247, 189, 206, 204,
            101, 51, 35, 8, 196, 85, 237, 64, 222, 81, 143, 182, 205, 105, 110, 173, 197, 239, 196,
            5, 108, 128, 248, 191, 247, 43, 25, 180, 246, 154, 125, 142, 227, 246, 17, 2, 207, 193,
            89, 244, 159, 82, 218, 117, 78, 191, 40, 49, 154, 160, 83, 246, 93, 94, 52, 85, 45,
            140, 99, 40, 23, 179, 141, 10, 143, 62, 176, 84, 19, 94, 79, 72, 58, 138, 7, 87, 196,
            2, 87, 0, 191, 226, 2, 224, 187, 150, 199, 217, 211, 51, 114, 228, 71, 54, 23, 17, 9,
            212, 195, 125, 236, 213, 254, 189, 203, 232, 161, 50, 81, 174, 129, 117,
        ];

        let expected_coefficients = [
            -3069, -504781, -216903, -503595, -11473, 119580, -202243, 431227, -78533, -514959,
            325528, 49008, -433555, 247178, -466650, 474204, -477186, 498034, 312926, 448500,
            461475, -370752, 85332, 303299, -164011, 7979, -103650, 86295, -274066, -52109, 350436,
            -344673, -1553, 135240, 220113, 31700, -470476, 339370, -337459, 392698, -359056,
            -66368, -19308, -148633, -154507, 212399, -513005, 522302, 413742, 407207, 110317,
            28622, 475286, 141287, -51830, 411088, 251210, -159641, 145853, 320956, 120675, 7554,
            500372, -236854, -418621, -226609, 516367, 211535, 247864, 388754, 494962, -44447,
            -57243, -361688, -26293, 320093, 270501, -255044, 207144, -294507, -201125, -117114,
            -32033, 294897, 83864, 182855, 377462, 126982, 82520, 212027, -500516, -406732, 412596,
            -415705, -382203, 161996, 227663, 411743, -446419, -405151, -159775, 42160, -276577,
            -416523, 422756, 261642, -129419, 111923, 362170, -222696, -192501, 257976, 72640,
            -3207, -233310, 474285, -512441, 150709, -41386, -389324, 51491, 508503, 511588,
            318229, 257931, -310066, 139685, -95067, 72237, -488209, 408609, 344033, 509795,
            419357, 71690, -284323, -313195, -222159, 451624, -86536, -323336, 34046, -380776,
            -93412, -266972, -50026, 267483, -377215, 134763, -461148, 270551, -247339, -59271,
            103677, -403373, 196926, 401231, 161215, 103197, 86355, -258813, 342143, 180436,
            124809, 397478, 63323, -376011, -397040, 445147, 388688, 207590, -75794, -152318,
            -210678, -116505, -249661, -36346, -108872, 288527, 184804, -300462, 508201, -186961,
            497195, -402163, -342227, 64860, 335146, 232451, -261519, -111093, 168569, -475779,
            -160035, 407767, 41921, 424280, -300188, 146093, -366901, 351699, -158897, -501343,
            520055, 426642, -216647, -442958, -181194, 26756, -490657, -315069, 313764, 260061,
            -447836, 401856, -223477, -420301, -285398, 146193, -1728, 16392, 421185, -194228,
            -59353, 395549, -323617, 239167, 185857, -423386, 357388, 484815, -484666, 237987,
            338605, -25484, -209266, -461453, -197608, -398164, 228107, 30150, -279920, 502014,
            -404464, -253954, -293227, 273447, -411427, 51641, 487151, -377812, -351943, -245246,
            -138892, -414002, 42982,
        ];

        assert_eq!(
            gamma1::deserialize::<19>(&bytes).coefficients,
            expected_coefficients
        );
    }
}
