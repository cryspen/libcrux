use crate::kem::kyber768::{
    arithmetic::{barrett_reduce, from_montgomery_domain, KyberPolynomialRingElement},
    parameters::RANK,
};

use self::kyber_polynomial_ring_element_mod::ntt_multiply;

pub(crate) mod kyber_polynomial_ring_element_mod {
    use crate::kem::kyber768::{
        arithmetic::{
            barrett_reduce, fe_mul, montgomery_reduce, KyberFieldElement,
            KyberPolynomialRingElement,
        },
        parameters::COEFFICIENTS_IN_RING_ELEMENT,
    };

    const ZETAS: [i16; 128] = [
        1, -1600, -749, -40, -687, 630, -1432, 848, 1062, -1410, 193, 797, -543, -69, 569, -1583,
        296, -882, 1339, 1476, -283, 56, -1089, 1333, 1426, -1235, 535, -447, -936, -450, -1355,
        821, 289, 331, -76, -1573, 1197, -1025, -1052, -1274, 650, -1352, -816, 632, -464, 33,
        1320, -1414, -1010, 1435, 807, 452, 1438, -461, 1534, -927, -682, -712, 1481, 648, -855,
        -219, 1227, 910, 17, -568, 583, -680, 1637, 723, -1041, 1100, 1409, -667, -48, 233, 756,
        -1173, -314, -279, -1626, 1651, -540, -1540, -1482, 952, 1461, -642, 939, -1021, -892,
        -941, 733, -992, 268, 641, 1584, -1031, -1292, -109, 375, -780, -1239, 1645, 1063, 319,
        -556, 757, -1230, 561, -863, -735, -525, 1092, 403, 1026, 1143, -1179, -554, 886, -1607,
        1212, -1455, 1029, -1219, -394, 885, -1175,
    ];

    const ZETAS_MONTGOMERY_DOMAIN: [i32; 128] = [
        -1044, -758, -359, -1517, 1493, 1422, 287, 202, -171, 622, 1577, 182, 962, -1202, -1474,
        1468, 573, -1325, 264, 383, -829, 1458, -1602, -130, -681, 1017, 732, 608, -1542, 411,
        -205, -1571, 1223, 652, -552, 1015, -1293, 1491, -282, -1544, 516, -8, -320, -666, -1618,
        -1162, 126, 1469, -853, -90, -271, 830, 107, -1421, -247, -951, -398, 961, -1508, -725,
        448, -1065, 677, -1275, -1103, 430, 555, 843, -1251, 871, 1550, 105, 422, 587, 177, -235,
        -291, -460, 1574, 1653, -246, 778, 1159, -147, -777, 1483, -602, 1119, -1590, 644, -872,
        349, 418, 329, -156, -75, 817, 1097, 603, 610, 1322, -1285, -1465, 384, -1215, -136, 1218,
        -1335, -874, 220, -1187, -1659, -1185, -1530, -1278, 794, -1510, -854, -870, 478, -108,
        -308, 996, 991, 958, -1460, 1522, 1628,
    ];

    const NTT_LAYERS: [usize; 7] = [2, 4, 8, 16, 32, 64, 128];

    pub fn ntt_representation(mut re: KyberPolynomialRingElement) -> KyberPolynomialRingElement {
        let mut zeta_i = 0;
        for layer in NTT_LAYERS.iter().rev() {
            for offset in (0..(COEFFICIENTS_IN_RING_ELEMENT - layer)).step_by(2 * layer) {
                zeta_i += 1;

                for j in offset..offset + layer {
                    let t = montgomery_reduce(
                        i32::from(re[j + layer]) * ZETAS_MONTGOMERY_DOMAIN[zeta_i],
                    );
                    re[j + layer] = re[j] - t;
                    re[j] += t;
                }
            }
        }
        re.coefficients = re.coefficients.map(barrett_reduce);

        re
    }

    pub fn invert_ntt(mut re: KyberPolynomialRingElement) -> KyberPolynomialRingElement {
        let inverse_of_2: i16 = -1664;

        let mut zeta_i = COEFFICIENTS_IN_RING_ELEMENT / 2;

        for layer in NTT_LAYERS {
            for offset in (0..(COEFFICIENTS_IN_RING_ELEMENT - layer)).step_by(2 * layer) {
                zeta_i -= 1;

                for j in offset..offset + layer {
                    let a_minus_b = re[j + layer] - re[j];
                    re[j] = fe_mul(re[j] + re[j + layer], inverse_of_2);
                    re[j + layer] = fe_mul(fe_mul(a_minus_b, ZETAS[zeta_i]), inverse_of_2);
                }
            }
        }
        re.coefficients = re.coefficients.map(barrett_reduce);

        re
    }

    fn ntt_multiply_binomials(
        (a0, a1): (KyberFieldElement, KyberFieldElement),
        (b0, b1): (KyberFieldElement, KyberFieldElement),
        zeta: i32,
    ) -> (KyberFieldElement, KyberFieldElement) {
        let a0 = i32::from(a0);
        let a1 = i32::from(a1);

        let b0 = i32::from(b0);
        let b1 = i32::from(b1);

        (
            montgomery_reduce(a0 * b0) + montgomery_reduce((montgomery_reduce(a1 * b1) as i32) * zeta),
            montgomery_reduce(a0 * b1) + montgomery_reduce(a1 * b0),
        )
    }

    pub fn ntt_multiply(
        left: &KyberPolynomialRingElement,
        right: &KyberPolynomialRingElement,
    ) -> KyberPolynomialRingElement {
        let mut out = KyberPolynomialRingElement::ZERO;

        for i in (0..COEFFICIENTS_IN_RING_ELEMENT).step_by(4) {
            let product = ntt_multiply_binomials(
                (left[i], left[i + 1]),
                (right[i], right[i + 1]),
                ZETAS_MONTGOMERY_DOMAIN[64 + (i/4)],
            );
            out[i] = product.0;
            out[i + 1] = product.1;

            let product = ntt_multiply_binomials(
                (left[i + 2], left[i + 3]),
                (right[i + 2], right[i + 3]),
                -ZETAS_MONTGOMERY_DOMAIN[64 + (i/4)],
            );
            out[i + 2] = product.0;
            out[i + 3] = product.1;
        }

        out
    }
}

pub(crate) fn multiply_row_by_column(
    row_vector: &[KyberPolynomialRingElement; RANK],
    column_vector: &[KyberPolynomialRingElement; RANK],
) -> KyberPolynomialRingElement {
    let mut result = KyberPolynomialRingElement::ZERO;

    for (row_element, column_element) in row_vector.iter().zip(column_vector.iter()) {
        result = result + ntt_multiply(row_element, column_element);
    }

    result.coefficients = result.coefficients.map(|coefficient| from_montgomery_domain(coefficient as i32)).map(barrett_reduce);

    result
}

pub(crate) fn multiply_matrix_by_column(
    matrix: &[[KyberPolynomialRingElement; RANK]; RANK],
    vector: &[KyberPolynomialRingElement; RANK],
) -> [KyberPolynomialRingElement; RANK] {
    let mut result = [KyberPolynomialRingElement::ZERO; RANK];

    for (i, row) in matrix.iter().enumerate() {
        for (j, matrix_element) in row.iter().enumerate() {
            let product = ntt_multiply(matrix_element, &vector[j]);
            result[i] = result[i] + product;
        }
        result[i].coefficients = result[i].coefficients.map(|coefficient| from_montgomery_domain(coefficient as i32)).map(barrett_reduce);
    }

    result
}
