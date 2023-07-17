use std::ops;

use crate::parameters;

#[derive(Debug, Clone, Copy, PartialEq)]
pub(crate) struct FieldElement {
    pub value: u16,
}

impl FieldElement {
    const MODULUS: u16 = parameters::FIELD_MODULUS;
    pub const ZERO: Self = Self { value: 0 };

    pub fn new(number: u16) -> Self {
        Self {
            value: number % Self::MODULUS,
        }
    }
}

impl From<u8> for FieldElement {
    fn from(number: u8) -> Self {
        Self {
            value: u16::from(number),
        }
    }
}
impl From<u16> for FieldElement {
    fn from(number: u16) -> Self {
        FieldElement::new(number)
    }
}
impl From<u32> for FieldElement {
    fn from(number: u32) -> Self {
        Self {
            value: (number % u32::from(Self::MODULUS)).try_into().unwrap(),
        }
    }
}

impl ops::Add for FieldElement {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        let sum: u32 = u32::from(self.value) + u32::from(other.value);

        sum.into()
    }
}
impl ops::Sub for FieldElement {
    type Output = Self;

    fn sub(self, other: Self) -> Self {
        let difference: i32 =
            i32::try_from(self.value).unwrap() - i32::try_from(other.value).unwrap();
        let representative = difference.rem_euclid(Self::MODULUS.into());

        u16::try_from(representative).unwrap().into()
    }
}
impl ops::Mul for FieldElement {
    type Output = Self;

    fn mul(self, other: Self) -> Self {
        let product: u32 = u32::from(self.value) * u32::from(other.value);

        product.into()
    }
}

#[cfg(test)]
pub(crate) mod testing {
    use super::*;
    use proptest::prelude::*;

    prop_compose! {
        pub(crate) fn arb_field_element() (
            representative in 0u16..parameters::FIELD_MODULUS) -> FieldElement {
                representative.into()
            }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn subtraction() {
        let lhs = FieldElement::new(3);
        let rhs = FieldElement::new(2);

        assert_eq!((lhs - rhs).value, 1);
        assert_eq!((rhs - lhs).value, parameters::FIELD_MODULUS - 1);

        let lhs = FieldElement::new(parameters::FIELD_MODULUS - 1);
        let rhs = FieldElement::new(0);

        assert_eq!((lhs - rhs).value, parameters::FIELD_MODULUS - 1);
        assert_eq!((rhs - lhs).value, 1);
    }

    #[test]
    fn addition() {
        let lhs = FieldElement::new(3);
        let rhs = FieldElement::new(2);

        assert_eq!((lhs + rhs).value, 5);
        assert_eq!((rhs + lhs).value, 5);

        let lhs = FieldElement::new(parameters::FIELD_MODULUS - 1);
        let rhs = FieldElement::new(10);

        assert_eq!((lhs + rhs).value, 9);
    }
}
