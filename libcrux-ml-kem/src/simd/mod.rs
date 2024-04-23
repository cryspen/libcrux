use crate::arithmetic::MONTGOMERY_R_SQUARED_MOD_FIELD_MODULUS;
use crate::constants::FIELD_MODULUS;

pub(crate) trait Operations {
    type Vector: Copy;

    const FIELD_ELEMENTS_IN_VECTOR: usize;

    #[allow(non_snake_case)]
    fn ZERO() -> Self::Vector;

    fn to_i32_array(v: Self::Vector) -> [i32; 8];
    fn from_i32_array(array: [i32; 8]) -> Self::Vector;

    // Basic arithmetic
    fn add_constant(v: Self::Vector, c: i32) -> Self::Vector;
    fn add(lhs: Self::Vector, rhs: &Self::Vector) -> Self::Vector;
    fn sub(lhs: Self::Vector, rhs: &Self::Vector) -> Self::Vector;

    fn multiply_by_constant(v: Self::Vector, c: i32) -> Self::Vector;

    // Bitwise operations
    fn bitwise_and_with_constant(v: Self::Vector, c: i32) -> Self::Vector;
    fn shift_right(v: Self::Vector, shift_amount: u8) -> Self::Vector;
    fn shift_left(v: Self::Vector, shift_amount: u8) -> Self::Vector;

    // Modular operations
    fn modulo_a_constant(v: Self::Vector, modulus: i32) -> Self::Vector;
    fn barrett_reduce(v: Self::Vector) -> Self::Vector;

    fn montgomery_reduce(v: Self::Vector) -> Self::Vector;

    // Compression
    fn compress_1(v: Self::Vector) -> Self::Vector;
    fn compress(coefficient_bits: u8, v: Self::Vector) -> Self::Vector;

    // NTT
    fn ntt_layer_1_step(a: Self::Vector, zeta1: i32, zeta2: i32) -> Self::Vector;
    fn ntt_layer_2_step(a: Self::Vector, zeta: i32) -> Self::Vector;

    fn inv_ntt_layer_1_step(a: Self::Vector, zeta1: i32, zeta2: i32) -> Self::Vector;
    fn inv_ntt_layer_2_step(a: Self::Vector, zeta: i32) -> Self::Vector;

    fn ntt_multiply(lhs: &Self::Vector, rhs: &Self::Vector, zeta0: i32, zeta1: i32)
        -> Self::Vector;

    // Serialization and deserialization
    fn serialize_1(a: Self::Vector) -> u8;
    fn deserialize_1(a: u8) -> Self::Vector;

    fn serialize_4(a: Self::Vector) -> [u8; 4];
    fn deserialize_4(a: &[u8]) -> Self::Vector;

    fn serialize_5(a: Self::Vector) -> [u8; 5];
    fn deserialize_5(a: &[u8]) -> Self::Vector;

    fn serialize_10(a: Self::Vector) -> [u8; 10];
    fn deserialize_10(a: &[u8]) -> Self::Vector;

    fn serialize_11(a: Self::Vector) -> [u8; 11];
    fn deserialize_11(a: &[u8]) -> Self::Vector;

    fn serialize_12(a: Self::Vector) -> [u8; 12];
    fn deserialize_12(a: &[u8]) -> Self::Vector;

    // Default implementations
    fn montgomery_multiply_fe_by_fer(v: Self::Vector, fer: i32) -> Self::Vector {
        let t = Self::multiply_by_constant(v, fer);

        Self::montgomery_reduce(t)
    }
    fn to_standard_domain(v: Self::Vector) -> Self::Vector {
        let t = Self::multiply_by_constant(v, MONTGOMERY_R_SQUARED_MOD_FIELD_MODULUS);

        Self::montgomery_reduce(t)
    }

    fn to_unsigned_representative(a: Self::Vector) -> Self::Vector {
        let t = Self::shift_right(a, 31);
        let fm = Self::bitwise_and_with_constant(t, FIELD_MODULUS);

        Self::add(a, &fm)
    }

    fn decompress_1(v: Self::Vector) -> Self::Vector {
        Self::bitwise_and_with_constant(Self::sub(Self::ZERO(), &v), 1665)
    }
    fn decompress(coefficient_bits: u8, v: Self::Vector) -> Self::Vector {
        let mut decompressed = Self::multiply_by_constant(v, FIELD_MODULUS);
        decompressed =
            Self::add_constant(Self::shift_left(decompressed, 1), 1i32 << coefficient_bits);
        decompressed = Self::shift_right(decompressed, coefficient_bits + 1);

        decompressed
    }
}

//#[cfg(feature = "simd128")]
//mod simd128;

#[cfg(not(feature = "simd128"))]
mod fallback;

#[cfg(not(feature = "simd128"))]
pub(crate) type Vector = fallback::FallbackVector;
