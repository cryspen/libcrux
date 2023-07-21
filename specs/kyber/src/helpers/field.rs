use std::ops;

pub(crate) trait FieldElement:
    Copy
    + Clone
    + PartialEq
    + From<u8>
    + From<u16>
    + From<u32>
    + ops::Add<Output = Self>
    + ops::Sub<Output = Self>
    + ops::Mul<Output = Self>
{
    const ZERO : Self;
    const MODULUS : u16;

    fn new(number: u16) -> Self;
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub(crate) struct PrimeFieldElement<const MODULUS: u16> {
    pub value: u16,
}

impl<const MODULUS: u16> FieldElement for PrimeFieldElement<MODULUS> {
    const MODULUS : u16 = MODULUS;

    const ZERO : Self = Self {
        value: 0,
    };

    fn new(number: u16) -> Self {
        Self {
            value: number % Self::MODULUS,
        }
    }
}

impl<const MODULUS: u16> From<u8> for PrimeFieldElement<MODULUS> {
    fn from(number: u8) -> Self {
        Self::new(u16::from(number))
    }
}
impl<const MODULUS: u16> From<u16> for PrimeFieldElement<MODULUS> {
    fn from(number: u16) -> Self {
        Self::new(number)
    }
}
impl<const MODULUS: u16> From<u32> for PrimeFieldElement<MODULUS> {
    fn from(number: u32) -> Self {
        let remainder_as_u32 = number % u32::from(Self::MODULUS);

        Self::new(remainder_as_u32.try_into().unwrap())
    }
}

impl<const MODULUS: u16> ops::Add for PrimeFieldElement<MODULUS> {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        let sum: u32 = u32::from(self.value) + u32::from(other.value);

        sum.into()
    }
}
impl<const MODULUS: u16> ops::Sub for PrimeFieldElement<MODULUS> {
    type Output = Self;

    fn sub(self, other: Self) -> Self {
        let difference: i32 =
            i32::try_from(self.value).unwrap() - i32::try_from(other.value).unwrap();
        let representative = difference.rem_euclid(Self::MODULUS.into());

        u16::try_from(representative).unwrap().into()
    }
}
impl<const MODULUS: u16> ops::Mul for PrimeFieldElement<MODULUS> {
    type Output = Self;

    fn mul(self, other: Self) -> Self {
        let product: u32 = u32::from(self.value) * u32::from(other.value);

        product.into()
    }
}
