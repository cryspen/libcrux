#[cfg(target_arch = "x86")]
use core::arch::x86::*;
#[cfg(target_arch = "x86_64")]
use core::arch::x86_64::*;
use libcrux_traits::Operations;

#[cfg(test)]
mod debug;

mod arithmetic;
mod compress;
mod ntt;
mod portable;
mod sampling;
mod serialize;

#[derive(Clone, Copy)]
pub struct SIMD256Vector {
    elements: __m256i,
}

#[inline(always)]
fn zero() -> SIMD256Vector {
    SIMD256Vector {
        elements: unsafe { _mm256_setzero_si256() },
    }
}

#[inline(always)]
fn to_i16_array(v: SIMD256Vector) -> [i16; 16] {
    let mut out = [0i16; 16];

    unsafe {
        _mm256_storeu_si256(out.as_mut_ptr() as *mut __m256i, v.elements);
    }

    out
}
#[inline(always)]
fn from_i16_array(array: &[i16]) -> SIMD256Vector {
    SIMD256Vector {
        elements: unsafe { _mm256_loadu_si256(array.as_ptr() as *const __m256i) },
    }
}

impl Operations for SIMD256Vector {
    fn ZERO() -> Self {
        zero()
    }

    fn to_i16_array(v: Self) -> [i16; 16] {
        to_i16_array(v)
    }

    fn from_i16_array(array: &[i16]) -> Self {
        from_i16_array(array)
    }

    fn add(lhs: Self, rhs: &Self) -> Self {
        arithmetic::add(lhs, rhs)
    }

    fn sub(lhs: Self, rhs: &Self) -> Self {
        arithmetic::sub(lhs, rhs)
    }

    fn multiply_by_constant(v: Self, c: i16) -> Self {
        arithmetic::multiply_by_constant(v, c)
    }

    fn bitwise_and_with_constant(v: Self, c: i16) -> Self {
        arithmetic::bitwise_and_with_constant(v, c)
    }

    fn shift_right<const SHIFT_BY: i32>(v: Self) -> Self {
        arithmetic::shift_right::<{ SHIFT_BY }>(v)
    }

    fn shift_left<const SHIFT_BY: i32>(v: Self) -> Self {
        arithmetic::shift_left::<{ SHIFT_BY }>(v)
    }

    fn cond_subtract_3329(v: Self) -> Self {
        arithmetic::cond_subtract_3329(v)
    }

    fn barrett_reduce(v: Self) -> Self {
        arithmetic::barrett_reduce(v)
    }

    fn montgomery_multiply_by_constant(v: Self, r: i16) -> Self {
        arithmetic::montgomery_multiply_by_constant(v, r)
    }

    fn compress_1(v: Self) -> Self {
        compress::compress_message_coefficient(v)
    }

    fn compress<const COEFFICIENT_BITS: i32>(v: Self) -> Self {
        compress::compress_ciphertext_coefficient::<COEFFICIENT_BITS>(v)
    }

    fn decompress_ciphertext_coefficient<const COEFFICIENT_BITS: i32>(v: Self) -> Self {
        compress::decompress_ciphertext_coefficient::<COEFFICIENT_BITS>(v)
    }

    fn ntt_layer_1_step(a: Self, zeta0: i16, zeta1: i16, zeta2: i16, zeta3: i16) -> Self {
        ntt::ntt_layer_1_step(a, zeta0, zeta1, zeta2, zeta3)
    }

    fn ntt_layer_2_step(a: Self, zeta0: i16, zeta1: i16) -> Self {
        ntt::ntt_layer_2_step(a, zeta0, zeta1)
    }

    fn ntt_layer_3_step(a: Self, zeta: i16) -> Self {
        ntt::ntt_layer_3_step(a, zeta)
    }

    fn inv_ntt_layer_1_step(a: Self, zeta0: i16, zeta1: i16, zeta2: i16, zeta3: i16) -> Self {
        ntt::inv_ntt_layer_1_step(a, zeta0, zeta1, zeta2, zeta3)
    }

    fn inv_ntt_layer_2_step(a: Self, zeta0: i16, zeta1: i16) -> Self {
        ntt::inv_ntt_layer_2_step(a, zeta0, zeta1)
    }

    fn inv_ntt_layer_3_step(a: Self, zeta: i16) -> Self {
        ntt::inv_ntt_layer_3_step(a, zeta)
    }

    fn ntt_multiply(
        lhs: &Self,
        rhs: &Self,
        zeta0: i16,
        zeta1: i16,
        zeta2: i16,
        zeta3: i16,
    ) -> Self {
        ntt::ntt_multiply(lhs, rhs, zeta0, zeta1, zeta2, zeta3)
    }

    fn serialize_1(a: Self) -> [u8; 2] {
        serialize::serialize_1(a)
    }

    fn deserialize_1(a: &[u8]) -> Self {
        serialize::deserialize_1(a)
    }

    fn serialize_4(a: Self) -> [u8; 8] {
        serialize::serialize_4(a)
    }

    fn deserialize_4(a: &[u8]) -> Self {
        serialize::deserialize_4(a)
    }

    fn serialize_5(a: Self) -> [u8; 10] {
        serialize::serialize_5(a)
    }

    fn deserialize_5(a: &[u8]) -> Self {
        serialize::deserialize_5(a)
    }

    fn serialize_10(a: Self) -> [u8; 20] {
        serialize::serialize_10(a)
    }

    fn deserialize_10(a: &[u8]) -> Self {
        serialize::deserialize_10(a)
    }

    fn serialize_11(a: Self) -> [u8; 22] {
        serialize::serialize_11(a)
    }

    fn deserialize_11(a: &[u8]) -> Self {
        serialize::deserialize_11(a)
    }

    fn serialize_12(a: Self) -> [u8; 24] {
        serialize::serialize_12(a)
    }

    fn deserialize_12(a: &[u8]) -> Self {
        serialize::deserialize_12(a)
    }

    fn rej_sample(input: &[u8], output: &mut [i16]) -> usize {
        sampling::rejection_sample(input, output)
    }
}
