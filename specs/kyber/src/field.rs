use crate::parameters;

#[derive(Debug, Clone, Copy, PartialEq)]
pub(crate) struct FieldElement {
    pub value : u16
}

impl FieldElement {
    const MODULUS : u16 = parameters::Q;
    pub const ZERO: Self = Self { value: 0 };

    pub fn from_u16(inp : u16) -> Self {
        Self { value : inp % Self::MODULUS }
    }

    pub fn from_u32(inp : u32) -> Self {
        Self { value : (inp % u32::from(Self::MODULUS)).try_into().unwrap() }
    }

    pub fn add(&self, other : &Self) -> Self {
        let sum : u32 = u32::from(self.value) + u32::from(other.value);
        Self::from_u32(sum)
    }

    pub fn subtract(&self, other : &Self) -> Self {
        let difference : i32 = i32::try_from(self.value).unwrap() - i32::try_from(other.value).unwrap();
        let representative = difference.rem_euclid(Self::MODULUS.into());
        Self::from_u16(u16::try_from(representative).unwrap())
    }

    pub fn multiply(&self, other : &Self) -> Self {
        let product : u32 = u32::from(self.value) * u32::from(other.value);
        Self::from_u32(product)
    }

    pub fn multiply_by_u16(&self, other : u16) -> Self {
        let product : u32 = u32::from(self.value) * u32::from(other);
        Self::from_u32(product)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn subtraction() {
        let lhs = FieldElement::from_u16(3);
        let rhs = FieldElement::from_u16(2);

        assert_eq!(lhs.subtract(&rhs).value, 1);
        assert_eq!(rhs.subtract(&lhs).value, parameters::Q - 1);

        let lhs = FieldElement::from_u16(parameters::Q - 1);
        let rhs = FieldElement::from_u16(0);

        assert_eq!(lhs.subtract(&rhs).value, parameters::Q - 1);
        assert_eq!(rhs.subtract(&lhs).value, 1);
    }

    #[test]
    fn addition() {
        let lhs = FieldElement::from_u16(3);
        let rhs = FieldElement::from_u16(2);

        assert_eq!(lhs.add(&rhs).value, 5);
        assert_eq!(rhs.add(&lhs).value, 5);

        let lhs = FieldElement::from_u16(parameters::Q - 1);
        let rhs = FieldElement::from_u16(10);

        assert_eq!(lhs.add(&rhs).value, 9);
    }

}
