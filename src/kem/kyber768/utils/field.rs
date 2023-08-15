use std::ops;

pub trait FieldElement:
    Copy
    + Clone
    + PartialEq
    + ops::Add<Output = Self>
    + ops::Sub<Output = Self>
    + ops::Mul<Output = Self>
{
    const ZERO: Self;

    fn new(number: u16) -> Self;
}
