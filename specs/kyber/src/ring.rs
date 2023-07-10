use crate::parameters;

#[derive(Clone)]
pub struct FieldElement {
    pub value : u16
}

impl FieldElement {
    const MODULUS : u16 = parameters::Q;
    pub const ZERO: Self = Self { value: 0 };

    pub fn from_u8(inp : u8) -> Self {
        Self { value : u16::from(inp) % Self::MODULUS }
    }

    pub fn from_u16(inp : u16) -> Self {
        Self { value : inp % Self::MODULUS }
    }
}

pub struct RingElement {
    pub coefficients : [FieldElement; parameters::N]
}

impl RingElement {
    // We use `256` instead of `parameters::N` due to
    // https://github.com/hacspec/hacspec-v2/issues/27
    pub const ZERO : Self = Self { coefficients : [FieldElement::ZERO; 256] };
}

