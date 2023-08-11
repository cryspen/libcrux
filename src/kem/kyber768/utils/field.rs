use std::ops;

pub trait FieldElement:
    Copy
    + Clone
    + PartialEq
    + From<u8>
    + Into<u16>
    + ops::Add<Output = Self>
    + ops::Sub<Output = Self>
    + ops::Mul<Output = Self>
{
    const ZERO: Self;

    fn new(number: u16) -> Self;
}
