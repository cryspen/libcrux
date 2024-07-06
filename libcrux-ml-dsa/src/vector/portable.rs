use crate::vector::traits::Operations;

mod arithmetic;
mod vector_type;

pub(crate) use vector_type::PortableVector;

impl Operations for PortableVector {
    fn ZERO() -> Self {
        vector_type::ZERO()
    }

    fn from_i32_array(array: &[i32]) -> Self {
        vector_type::from_i32_array(array)
    }

    fn to_i32_array(vector: Self) -> [i32; 8] {
        vector_type::to_i32_array(vector)
    }

    fn add(lhs: Self, rhs: &Self) -> Self {
        arithmetic::add(lhs, rhs)
    }

    fn subtract(lhs: Self, rhs: &Self) -> Self {
        arithmetic::subtract(lhs, rhs)
    }
}
