// Each field element occupies 32 bits and the size of a vector is 256 bits.
pub(crate) const COEFFICIENTS_PER_VECTOR: usize = 8;

pub const FIELD_MODULUS: i32 = 8_380_417;

// FIELD_MODULUS^{-1} mod MONTGOMERY_R
pub const INVERSE_OF_MODULUS_MOD_MONTGOMERY_R: u64 = 58_728_449;

pub(crate) trait Operations: Copy + Clone {
    #[allow(non_snake_case)]
    fn ZERO() -> Self;

    fn from_i32_array(array: &[i32]) -> Self;
    fn to_i32_array(vector: Self) -> [i32; COEFFICIENTS_PER_VECTOR];

    // Basic arithmetic
    fn add(lhs: &Self, rhs: &Self) -> Self;
    fn subtract(lhs: &Self, rhs: &Self) -> Self;

    // Modular operations
    fn montgomery_multiply(lhs: Self, rhs: Self) -> Self;
    fn montgomery_multiply_by_constant(vector: Self, c: i32) -> Self;

    // NTT
    fn ntt_at_layer_0(vector: Self, zeta0: i32, zeta1: i32, zeta2: i32, zeta3: i32) -> Self;
    fn ntt_at_layer_1(vector: Self, zeta0: i32, zeta1: i32) -> Self;
    fn ntt_at_layer_2(vector: Self, zeta: i32) -> Self;

    // Inverse NTT
    fn invert_ntt_at_layer_0(vector: Self, zeta0: i32, zeta1: i32, zeta2: i32, zeta3: i32) -> Self;
    fn invert_ntt_at_layer_1(vector: Self, zeta0: i32, zeta1: i32) -> Self;
    fn invert_ntt_at_layer_2(vector: Self, zeta: i32) -> Self;
}

// hax does not support trait with default implementations, so we use the
// following pattern.
pub fn montgomery_multiply_by_fer<V: Operations>(vector: V, fer: i32) -> V {
    V::montgomery_multiply_by_constant(vector, fer)
}
