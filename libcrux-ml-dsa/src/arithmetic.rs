use crate::constants::COEFFICIENTS_IN_RING_ELEMENT;

/// Values having this type hold a representative 'x' of the ML-DSA field.
pub(crate) type FieldElement = i32;

#[derive(Clone, Copy)]
pub struct PolynomialRingElement {
    pub(crate) coefficients: [FieldElement; COEFFICIENTS_IN_RING_ELEMENT],
}

impl PolynomialRingElement {
    pub const ZERO: Self = Self {
        // FIXME: hax issue, 256 is COEFFICIENTS_IN_RING_ELEMENT
        coefficients: [0i32; 256],
    };
}
