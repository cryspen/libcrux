use crate::kem::kyber768::{
    arithmetic::{barrett_reduce, KyberPolynomialRingElement},
    parameters::RANK,
};

use self::kyber_polynomial_ring_element_mod::ntt_multiply;

pub(crate) mod kyber_polynomial_ring_element_mod {
    use crate::kem::kyber768::{
        arithmetic::{barrett_reduce, fe_mul, KyberFieldElement, KyberPolynomialRingElement},
        parameters::COEFFICIENTS_IN_RING_ELEMENT,
    };

    const ZETAS: [i16; 128] = [
        1, -1600, -749, -40, -687, 630, -1432, 848, 1062, -1410, 193, 797, -543, -69, 569, -1583, 296, -882, 1339, 1476, -283, 56, -1089, 1333, 1426, -1235, 535, -447, -936, -450, -1355, 821, 289, 331, -76, -1573, 1197, -1025, -1052, -1274, 650, -1352, -816, 632, -464, 33, 1320, -1414, -1010, 1435, 807, 452, 1438, -461, 1534, -927, -682, -712, 1481, 648, -855, -219, 1227, 910, 17, -568, 583, -680, 1637, 723, -1041, 1100, 1409, -667, -48, 233, 756, -1173, -314, -279, -1626, 1651, -540, -1540, -1482, 952, 1461, -642, 939, -1021, -892, -941, 733, -992, 268, 641, 1584, -1031, -1292, -109, 375, -780, -1239, 1645, 1063, 319, -556, 757, -1230, 561, -863, -735, -525, 1092, 403, 1026, 1143, -1179, -554, 886, -1607, 1212, -1455, 1029, -1219, -394, 885, -1175
    ];

    const MOD_ROOTS: [i16; 128] = [
        17, -17, -568, 568, 583, -583, -680, 680, 1637, -1637, 723, -723, -1041, 1041, 1100, -1100, 1409, -1409, -667, 667, -48, 48, 233, -233, 756, -756, -1173, 1173, -314, 314, -279, 279, -1626, 1626, 1651, -1651, -540, 540, -1540, 1540, -1482, 1482, 952, -952, 1461, -1461, -642, 642, 939, -939, -1021, 1021, -892, 892, -941, 941, 733, -733, -992, 992, 268, -268, 641, -641, 1584, -1584, -1031, 1031, -1292, 1292, -109, 109, 375, -375, -780, 780, -1239, 1239, 1645, -1645, 1063, -1063, 319, -319, -556, 556, 757, -757, -1230, 1230, 561, -561, -863, 863, -735, 735, -525, 525, 1092, -1092, 403, -403, 1026, -1026, 1143, -1143, -1179, 1179, -554, 554, 886, -886, -1607, 1607, 1212, -1212, -1455, 1455, 1029, -1029, -1219, 1219, -394, 394, 885, -885, -1175, 1175
    ];

    const NTT_LAYERS: [usize; 7] = [2, 4, 8, 16, 32, 64, 128];

    pub fn ntt_representation(mut re: KyberPolynomialRingElement) -> KyberPolynomialRingElement {
        let mut zeta_i = 0;
        for layer in NTT_LAYERS.iter().rev() {
            for offset in (0..(COEFFICIENTS_IN_RING_ELEMENT - layer)).step_by(2 * layer) {
                zeta_i += 1;

                for j in offset..offset + layer {
                    let t = fe_mul(re[j + layer], ZETAS[zeta_i]);
                    re[j + layer] = re[j] - t;
                    re[j] = re[j] + t;
                }
            }
        }

        KyberPolynomialRingElement::new(re.coefficients.map(barrett_reduce))
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

        KyberPolynomialRingElement::new(re.coefficients.map(barrett_reduce))
    }

    fn ntt_multiply_binomials(
        (a0, a1): (KyberFieldElement, KyberFieldElement),
        (b0, b1): (KyberFieldElement, KyberFieldElement),
        zeta: i16,
    ) -> (KyberFieldElement, KyberFieldElement) {
        (
            fe_mul(a0, b0) + fe_mul(fe_mul(a1, b1), zeta),
            fe_mul(a0, b1) + fe_mul(a1, b0),
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
                MOD_ROOTS[i / 2],
            );
            out[i] = product.0;
            out[i + 1] = product.1;

            let product = ntt_multiply_binomials(
                (left[i + 2], left[i + 3]),
                (right[i + 2], right[i + 3]),
                MOD_ROOTS[(i + 2) / 2],
            );
            out[i + 2] = product.0;
            out[i + 3] = product.1;
        }

        out
    }
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

        result[i].coefficients = result[i].coefficients.map(barrett_reduce);
    }

    result
}

pub(crate) fn multiply_row_by_column(
    row_vector: &[KyberPolynomialRingElement; RANK],
    column_vector: &[KyberPolynomialRingElement; RANK],
) -> KyberPolynomialRingElement {
    let mut result = KyberPolynomialRingElement::ZERO;

    for (row_element, column_element) in row_vector.iter().zip(column_vector.iter()) {
        result = result + ntt_multiply(row_element, column_element);
    }

    KyberPolynomialRingElement::new(result.coefficients.map(barrett_reduce))
}
