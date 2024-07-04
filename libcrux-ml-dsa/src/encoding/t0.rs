// ---------------------------------------------------------------------------
// Functions for serializing and deserializing the ring element t0.
// ---------------------------------------------------------------------------

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

        serialized[13 * i] = coefficient0 as u8;

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
fn deserialize(serialized: &[u8]) -> PolynomialRingElement {
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

        re.coefficients[8 * i] = byte0;
        re.coefficients[8 * i] |= byte1 << 8;
        re.coefficients[8 * i] &= BITS_IN_LOWER_PART_OF_T_MASK;

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

        re.coefficients[8 * i] = change_t0_interval(re.coefficients[8 * i]);
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

#[cfg(test)]
mod tests {
    use super::*;

    use crate::arithmetic::PolynomialRingElement;

    #[test]
    fn test_serialize() {
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

        assert_eq!(serialize(re), expected_re_serialized);
    }

    #[test]
    fn test_deserialize() {
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

        assert_eq!(deserialize(&serialized).coefficients, expected_coefficients);
    }
}
