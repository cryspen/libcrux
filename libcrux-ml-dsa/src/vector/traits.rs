// Each field element occupies 32 bits and the size of a vector is 256 bits.
pub(crate) const COEFFICIENTS_PER_VECTOR: usize = 8;

pub(crate) trait Operations: Copy + Clone {
    #[allow(non_snake_case)]
    fn ZERO() -> Self;

    fn from_i32_array(array: &[i32]) -> Self;
    fn to_i32_array(vector: Self) -> [i32; COEFFICIENTS_PER_VECTOR];

    // Basic arithmetic
    fn add(lhs: Self, rhs: &Self) -> Self;
    fn subtract(lhs: Self, rhs: &Self) -> Self;
}
