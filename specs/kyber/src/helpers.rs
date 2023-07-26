pub(crate) mod bit_vector;
pub(crate) mod field;
pub(crate) mod ring;

#[cfg(test)]
pub(crate) mod testing {
    use crate::parameters::{self, KyberFieldElement, KyberPolynomialRingElement};

    use proptest::collection::vec;
    use proptest::prelude::*;

    prop_compose! {
        fn arb_field_element(bit_size : usize) (
            representative in 0u16..parameters::FIELD_MODULUS) -> KyberFieldElement {
                (representative & ((1 << bit_size) - 1)).into()
        }
    }

    prop_compose! {
        pub(crate) fn arb_ring_element(bits_per_coefficient : usize) (arb_ring_coefficients in vec(arb_field_element(bits_per_coefficient), parameters::COEFFICIENTS_IN_RING_ELEMENT)) -> KyberPolynomialRingElement {
                KyberPolynomialRingElement {
                    coefficients: arb_ring_coefficients.try_into().unwrap(),
            }
        }
    }
}
