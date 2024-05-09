//! Vectors for libcrux using aarch64 (neon) intrinsics

use libcrux_traits::Operations;

mod neon;
mod rejsample;
mod simd128ops;

pub use simd128ops::SIMD128Vector;
use simd128ops::*;

// This is an empty shell, calling into standalone functions in `simd128ops`.
// This is due to limitations in F* and hax to deal with large trait implementations
// See hacspec/hax#638 for more details.
impl Operations for SIMD128Vector {
    #[inline(always)]
    fn ZERO() -> Self {
        ZERO()
    }

    fn to_i16_array(v: Self) -> [i16; 16] {
        to_i16_array(v)
    }

    fn from_i16_array(array: [i16; 16]) -> Self {
        from_i16_array(array)
    }

    fn add(lhs: Self, rhs: &Self) -> Self {
        add(lhs, rhs)
    }

    fn sub(lhs: Self, rhs: &Self) -> Self {
        sub(lhs, rhs)
    }

    fn multiply_by_constant(v: Self, c: i16) -> Self {
        multiply_by_constant(v, c)
    }

    fn bitwise_and_with_constant(v: Self, c: i16) -> Self {
        bitwise_and_with_constant(v, c)
    }

    fn shift_right<const SHIFT_BY: i32>(v: Self) -> Self {
        shift_right::<SHIFT_BY>(v)
    }

    fn shift_left<const SHIFT_BY: i32>(v: Self) -> Self {
        shift_left::<SHIFT_BY>(v)
    }

    fn cond_subtract_3329(v: Self) -> Self {
        cond_subtract_3329(v)
    }

    fn barrett_reduce(v: Self) -> Self {
        barrett_reduce(v)
    }

    fn montgomery_multiply_by_constant(v: Self, c: i16) -> Self {
        montgomery_multiply_by_constant(v, c)
    }

    fn compress_1(v: Self) -> Self {
        compress_1(v)
    }

    fn compress<const COEFFICIENT_BITS: i32>(v: Self) -> Self {
        compress::<COEFFICIENT_BITS>(v)
    }

    fn decompress<const COEFFICIENT_BITS: i32>(v: Self) -> Self {
        decompress::<COEFFICIENT_BITS>(v)
    }

    fn ntt_layer_1_step(a: Self, zeta1: i16, zeta2: i16, zeta3: i16, zeta4: i16) -> Self {
        ntt_layer_1_step(a, zeta1, zeta2, zeta3, zeta4)
    }

    fn ntt_layer_2_step(a: Self, zeta1: i16, zeta2: i16) -> Self {
        ntt_layer_2_step(a, zeta1, zeta2)
    }

    fn ntt_layer_3_step(a: Self, zeta: i16) -> Self {
        ntt_layer_3_step(a, zeta)
    }

    fn inv_ntt_layer_1_step(a: Self, zeta1: i16, zeta2: i16, zeta3: i16, zeta4: i16) -> Self {
        inv_ntt_layer_1_step(a, zeta1, zeta2, zeta3, zeta4)
    }

    fn inv_ntt_layer_2_step(a: Self, zeta1: i16, zeta2: i16) -> Self {
        inv_ntt_layer_2_step(a, zeta1, zeta2)
    }

    fn inv_ntt_layer_3_step(a: Self, zeta: i16) -> Self {
        inv_ntt_layer_3_step(a, zeta)
    }

    fn ntt_multiply(
        lhs: &Self,
        rhs: &Self,
        zeta1: i16,
        zeta2: i16,
        zeta3: i16,
        zeta4: i16,
    ) -> Self {
        ntt_multiply(lhs, rhs, zeta1, zeta2, zeta3, zeta4)
    }

    fn serialize_1(a: Self) -> [u8; 2] {
        serialize_1(a)
    }

    fn deserialize_1(a: &[u8]) -> Self {
        deserialize_1(a)
    }

    fn serialize_4(a: Self) -> [u8; 8] {
        serialize_4(a)
    }

    fn deserialize_4(a: &[u8]) -> Self {
        deserialize_4(a)
    }

    fn serialize_5(a: Self) -> [u8; 10] {
        serialize_5(a)
    }

    fn deserialize_5(a: &[u8]) -> Self {
        deserialize_5(a)
    }

    fn serialize_10(a: Self) -> [u8; 20] {
        serialize_10(a)
    }

    fn deserialize_10(a: &[u8]) -> Self {
        deserialize_10(a)
    }

    fn serialize_11(a: Self) -> [u8; 22] {
        serialize_11(a)
    }

    fn deserialize_11(a: &[u8]) -> Self {
        deserialize_11(a)
    }

    fn serialize_12(a: Self) -> [u8; 24] {
        serialize_12(a)
    }

    fn deserialize_12(a: &[u8]) -> Self {
        deserialize_12(a)
    }

    fn rej_sample(a: &[u8]) -> (usize, [i16; 16]) {
        rejsample::rej_sample(a)
    }
}
