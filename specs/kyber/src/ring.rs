use crate::parameters;
use crate::field::FieldElement;

#[derive(Debug, Clone, Copy, PartialEq)]
pub(crate) struct RingElement {
    pub coefficients : [FieldElement; parameters::COEFFICIENTS_IN_RING_ELEMENT]
}

impl RingElement {
    // Using constant due to:
    // https://github.com/hacspec/hacspec-v2/issues/27
    pub const ZERO : Self = Self { coefficients : [FieldElement::ZERO; 256] };

    // ZETAS = [pow(17, bitreverse(i), p) for i in range(128)]
    const ZETAS : [u16; 128] = [
        17,    1729, 2580, 3289, 2642, 630,  1897, 848,  1062, 1919, 193,  797,
        2786, 3260, 569,  1746, 296,  2447, 1339, 1476, 3046, 56,   2240, 1333,
        1426, 2094, 535,  2882, 2393, 2879, 1974, 821,  289,  331,  3253, 1756,
        1197, 2304, 2277, 2055, 650,  1977, 2513, 632,  2865, 33,   1320, 1915,
        2319, 1435, 807,  452,  1438, 2868, 1534, 2402, 2647, 2617, 1481, 648,
        2474, 3110, 1227, 910,  17,   2761, 583,  2649, 1637, 723,  2288, 1100,
        1409, 2662, 3281, 233,  756,  2156, 3015, 3050, 1703, 1651, 2789, 1789,
        1847, 952,  1461, 2687, 939,  2308, 2437, 2388, 733,  2337, 268,  641,
        1584, 2298, 2037, 3220, 375,  2549, 2090, 1645, 1063, 319,  2773, 757,
        2099, 561,  2466, 2594, 2804, 1092, 403,  1026, 1143, 2150, 2775, 886,
        1722, 1212, 1874, 1029, 2110, 2935, 885,  2154
    ];

    // MOD_ROOTS = [pow(17, 2*bitreverse(i) + 1, p) for i in range(128)]
    const MOD_ROOTS : [u16; 128] = [
        17,   3312, 2761, 568,  583,  2746, 2649, 680,  1637, 1692, 723,  2606,
        2288, 1041, 1100, 2229, 1409, 1920, 2662, 667,  3281, 48,   233,  3096,
        756,  2573, 2156, 1173, 3015, 314,  3050, 279,  1703, 1626, 1651, 1678,
        2789, 540,  1789, 1540, 1847, 1482, 952,  2377, 1461, 1868, 2687, 642,
        939,  2390, 2308, 1021, 2437, 892,  2388, 941,  733,  2596, 2337, 992,
        268,  3061, 641,  2688, 1584, 1745, 2298, 1031, 2037, 1292, 3220, 109,
        375,  2954, 2549, 780,  2090, 1239, 1645, 1684, 1063, 2266, 319,  3010,
        2773, 556,  757,  2572, 2099, 1230, 561,  2768, 2466, 863,  2594, 735,
        2804, 525,  1092, 2237, 403,  2926, 1026, 2303, 1143, 2186, 2150, 1179,
        2775, 554,  886,  2443, 1722, 1607, 1212, 2117, 1874, 1455, 1029, 2300,
        2110, 1219, 2935, 394,  885,  2444, 2154, 1175,
    ];

    pub fn ntt_representation(&self) -> Self {
        let mut out = RingElement::ZERO;
        for i in 0..self.coefficients.len() {
            out.coefficients[i].value = self.coefficients[i].value;
        }

        let mut zeta_i = 0;
        for layer in [128, 64, 32, 16, 8, 4, 2] {
            for offset in (0..(parameters::COEFFICIENTS_IN_RING_ELEMENT - layer)).step_by(2*layer) {
                zeta_i += 1;
                let zeta = FieldElement::from_u16(Self::ZETAS[zeta_i]);

                for j in offset..offset+layer {
                        let t = zeta.multiply(&out.coefficients[j + layer]);
                        out.coefficients[j + layer] = out.coefficients[j].subtract(&t);
                        out.coefficients[j] = out.coefficients[j].add(&t);
                }
            }
        }
        out
    }

    pub fn add(&self, rhs: &Self) -> Self {
        let mut result = RingElement::ZERO;
        for i in 0..self.coefficients.len() {
            result.coefficients[i] = self.coefficients[i].add(&rhs.coefficients[i]);
        }
        result
    }

    pub fn ntt_multiply(&self, rhs: &Self) -> Self {
        let mut out = RingElement::ZERO;

        for i in (0..parameters::COEFFICIENTS_IN_RING_ELEMENT).step_by(2) {
            let a1_times_a2 = self.coefficients[i].multiply(&rhs.coefficients[i]);
            let b1_times_b2 = self.coefficients[i + 1].multiply(&rhs.coefficients[i + 1]);

            let a2_times_b1 = self.coefficients[i + 1].multiply(&rhs.coefficients[i]);
            let a1_times_b2 = self.coefficients[i].multiply(&rhs.coefficients[i + 1]);

            out.coefficients[i] = a1_times_a2.add(&b1_times_b2.multiply_by_u16(Self::MOD_ROOTS[i / 2]));
            out.coefficients[i + 1] = a2_times_b1.add(&a1_times_b2);
        }
        out
    }
}

#[allow(non_snake_case)]
pub(crate) fn multiply_matrix_by_vector(matrix : &[[RingElement; parameters::RANK]; parameters::RANK], vector : &[RingElement; parameters::RANK]) -> [RingElement; parameters::RANK] {
    let mut result = [RingElement::ZERO; parameters::RANK];

    for i in 0..parameters::RANK {
        for j in 0..parameters::RANK {
            let product = matrix[i][j].ntt_multiply(&vector[j]);
            result[i] = result[i].add(&product);
        }
    }
    result
}

#[cfg(test)]
impl quickcheck::Arbitrary for RingElement {
    fn arbitrary(_g: &mut quickcheck::Gen) -> RingElement {

        use rand::distributions::{Distribution, Uniform};

        let between = Uniform::from(0..parameters::FIELD_MODULUS);
        let mut rng = rand::thread_rng();

        let mut ring_element = RingElement::ZERO;

        for i in 0..ring_element.coefficients.len() {
            let coefficient = between.sample(&mut rng);
            ring_element.coefficients[i] = FieldElement::from_u16(coefficient);
        }

        ring_element
    }
}
