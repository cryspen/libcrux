use crate::{
    arithmetic::{t0_to_unsigned_representative, PolynomialRingElement},
    constants::{BYTES_FOR_RING_ELEMENT_OF_T0S, BYTES_FOR_RING_ELEMENT_OF_T1S},
};

#[inline(always)]
pub(crate) fn serialize_ring_element_of_t0s(
    re: PolynomialRingElement,
) -> [u8; BYTES_FOR_RING_ELEMENT_OF_T0S] {
    let mut serialized = [0u8; BYTES_FOR_RING_ELEMENT_OF_T0S];

    for (i, coefficients) in re.coefficients.chunks_exact(8).enumerate() {
        let coefficient0 = t0_to_unsigned_representative(coefficients[0]);
        let coefficient1 = t0_to_unsigned_representative(coefficients[1]);
        let coefficient2 = t0_to_unsigned_representative(coefficients[2]);
        let coefficient3 = t0_to_unsigned_representative(coefficients[3]);
        let coefficient4 = t0_to_unsigned_representative(coefficients[4]);
        let coefficient5 = t0_to_unsigned_representative(coefficients[5]);
        let coefficient6 = t0_to_unsigned_representative(coefficients[6]);
        let coefficient7 = t0_to_unsigned_representative(coefficients[7]);

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
pub(crate) fn serialize_ring_element_of_t1s(
    re: PolynomialRingElement,
) -> [u8; BYTES_FOR_RING_ELEMENT_OF_T1S] {
    let mut serialized = [0u8; BYTES_FOR_RING_ELEMENT_OF_T1S];

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

#[inline(always)]
fn serialize_error_ring_element_when_eta_is_2<const BYTES_FOR_OUTPUT: usize>(
    re: PolynomialRingElement,
) -> [u8; BYTES_FOR_OUTPUT] {
    let mut serialized = [0u8; BYTES_FOR_OUTPUT];

    for (i, coefficients) in re.coefficients.chunks_exact(8).enumerate() {
        let coefficient0 = (2 - coefficients[0]) as u8;
        let coefficient1 = (2 - coefficients[1]) as u8;
        let coefficient2 = (2 - coefficients[2]) as u8;
        let coefficient3 = (2 - coefficients[3]) as u8;
        let coefficient4 = (2 - coefficients[4]) as u8;
        let coefficient5 = (2 - coefficients[5]) as u8;
        let coefficient6 = (2 - coefficients[6]) as u8;
        let coefficient7 = (2 - coefficients[7]) as u8;

        serialized[3 * i + 0] = (coefficient2 << 6) | (coefficient1 << 3) | coefficient0;
        serialized[3 * i + 1] =
            (coefficient5 << 7) | (coefficient4 << 4) | (coefficient3 << 1) | (coefficient2 >> 2);
        serialized[3 * i + 2] = (coefficient7 << 5) | (coefficient6 << 2) | (coefficient5 >> 1);
    }

    serialized
}

#[inline(always)]
fn serialize_error_ring_element_when_eta_is_4<const BYTES_FOR_OUTPUT: usize>(
    re: PolynomialRingElement,
) -> [u8; BYTES_FOR_OUTPUT] {
    let mut serialized = [0u8; BYTES_FOR_OUTPUT];

    for (i, coefficients) in re.coefficients.chunks_exact(2).enumerate() {
        let coefficient0 = (4 - coefficients[0]) as u8;
        let coefficient1 = (4 - coefficients[1]) as u8;
        serialized[i] = (coefficient1 << 4) | coefficient0;
    }

    serialized
}

pub(crate) fn serialize_error_ring_element<const ETA: usize, const BYTES_FOR_OUTPUT: usize>(
    re: PolynomialRingElement,
) -> [u8; BYTES_FOR_OUTPUT] {
    match ETA {
        2 => serialize_error_ring_element_when_eta_is_2::<BYTES_FOR_OUTPUT>(re),
        4 => serialize_error_ring_element_when_eta_is_4::<BYTES_FOR_OUTPUT>(re),
        _ => unreachable!(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::arithmetic::PolynomialRingElement;

    #[test]
    fn test_serialize_ring_element_of_t1s() {
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

        assert_eq!(serialize_ring_element_of_t1s(re), expected_re_serialized);
    }

    #[test]
    fn test_serialize_ring_element_of_t0s() {
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

        assert_eq!(serialize_ring_element_of_t0s(re), expected_re_serialized);
    }
}
