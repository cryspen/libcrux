pub trait FieldElement:
    Copy
    + Clone
    + PartialEq
{
    const ZERO: Self;

    fn new(number: u16) -> Self;
    fn add(self, other: Self) -> Self;
    fn sub(self, other: Self) -> Self;
    fn mul(self, other: Self) -> Self;
    fn mul_by_u16(self, other: u16) -> Self;
}
