pub(crate) mod bit_vector;
pub(crate) mod field;
pub(crate) mod ring;

#[cfg(test)]
pub(crate) mod testing {
    use crate::parameters::{self, KyberFieldElement};
    use proptest::prelude::*;

    prop_compose! {
        pub(crate) fn arb_field_element() (
            representative in 0u16..parameters::FIELD_MODULUS) -> KyberFieldElement {
                representative.into()
            }
    }
}
