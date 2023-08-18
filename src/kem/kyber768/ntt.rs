use crate::kem::kyber768::arithmetic::KyberPolynomialRingElement;
use crate::kem::kyber768::parameters::RANK;

use self::kyber_polynomial_ring_element_mod::ntt_multiply;

pub(crate) mod kyber_polynomial_ring_element_mod {
    use crate::kem::kyber768::{
        arithmetic::{fe_add, fe_mul, fe_sub, KyberFieldElement, KyberPolynomialRingElement},
        parameters::{self, COEFFICIENTS_IN_RING_ELEMENT},
    };

    const ZETAS: [i16; 128] = [
        1, 1729, 2580, 3289, 2642, 630, 1897, 848, 1062, 1919, 193, 797, 2786, 3260, 569, 1746,
        296, 2447, 1339, 1476, 3046, 56, 2240, 1333, 1426, 2094, 535, 2882, 2393, 2879, 1974, 821,
        289, 331, 3253, 1756, 1197, 2304, 2277, 2055, 650, 1977, 2513, 632, 2865, 33, 1320, 1915,
        2319, 1435, 807, 452, 1438, 2868, 1534, 2402, 2647, 2617, 1481, 648, 2474, 3110, 1227, 910,
        17, 2761, 583, 2649, 1637, 723, 2288, 1100, 1409, 2662, 3281, 233, 756, 2156, 3015, 3050,
        1703, 1651, 2789, 1789, 1847, 952, 1461, 2687, 939, 2308, 2437, 2388, 733, 2337, 268, 641,
        1584, 2298, 2037, 3220, 375, 2549, 2090, 1645, 1063, 319, 2773, 757, 2099, 561, 2466, 2594,
        2804, 1092, 403, 1026, 1143, 2150, 2775, 886, 1722, 1212, 1874, 1029, 2110, 2935, 885,
        2154,
    ];

    const MOD_ROOTS: [i16; 128] = [
        17, 3312, 2761, 568, 583, 2746, 2649, 680, 1637, 1692, 723, 2606, 2288, 1041, 1100, 2229,
        1409, 1920, 2662, 667, 3281, 48, 233, 3096, 756, 2573, 2156, 1173, 3015, 314, 3050, 279,
        1703, 1626, 1651, 1678, 2789, 540, 1789, 1540, 1847, 1482, 952, 2377, 1461, 1868, 2687,
        642, 939, 2390, 2308, 1021, 2437, 892, 2388, 941, 733, 2596, 2337, 992, 268, 3061, 641,
        2688, 1584, 1745, 2298, 1031, 2037, 1292, 3220, 109, 375, 2954, 2549, 780, 2090, 1239,
        1645, 1684, 1063, 2266, 319, 3010, 2773, 556, 757, 2572, 2099, 1230, 561, 2768, 2466, 863,
        2594, 735, 2804, 525, 1092, 2237, 403, 2926, 1026, 2303, 1143, 2186, 2150, 1179, 2775, 554,
        886, 2443, 1722, 1607, 1212, 2117, 1874, 1455, 1029, 2300, 2110, 1219, 2935, 394, 885,
        2444, 2154, 1175,
    ];

    const NTT_LAYERS: [usize; 7] = [2, 4, 8, 16, 32, 64, 128];

    pub fn ntt_representation(mut re: KyberPolynomialRingElement) -> KyberPolynomialRingElement {
        let mut zeta_i = 0;
        for layer in NTT_LAYERS.iter().rev() {
            for offset in (0..(COEFFICIENTS_IN_RING_ELEMENT - layer)).step_by(2 * layer) {
                zeta_i += 1;

                for j in offset..offset + layer {
                    let t = fe_mul(re[j + layer], ZETAS[zeta_i]);
                    re[j + layer] = fe_sub(re[j], t);
                    re[j] = fe_add(re[j], t);
                }
            }
        }
        re
    }

    pub fn invert_ntt(re: KyberPolynomialRingElement) -> KyberPolynomialRingElement {
        let inverse_of_2: i16 = (parameters::FIELD_MODULUS + 1) >> 1;

        let mut out = KyberPolynomialRingElement::ZERO;
        for i in 0..COEFFICIENTS_IN_RING_ELEMENT {
            out[i] = re[i];
        }

        let mut zeta_i = COEFFICIENTS_IN_RING_ELEMENT / 2;

        for layer in NTT_LAYERS {
            for offset in (0..(COEFFICIENTS_IN_RING_ELEMENT - layer)).step_by(2 * layer) {
                zeta_i -= 1;

                for j in offset..offset + layer {
                    let a_minus_b = fe_sub(out[j + layer], out[j]);
                    out[j] = fe_mul(fe_add(out[j], out[j + layer]), inverse_of_2);
                    out[j + layer] = fe_mul(fe_mul(a_minus_b, ZETAS[zeta_i]), inverse_of_2);
                }
            }
        }

        out
    }

    fn ntt_multiply_binomials(
        (a0, a1): (KyberFieldElement, KyberFieldElement),
        (b0, b1): (KyberFieldElement, KyberFieldElement),
        zeta: i16,
    ) -> (KyberFieldElement, KyberFieldElement) {
        (
            fe_add(fe_mul(a0, b0), fe_mul(fe_mul(a1, b1), zeta)),
            fe_add(fe_mul(a0, b1), fe_mul(a1, b0)),
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

    result
}
