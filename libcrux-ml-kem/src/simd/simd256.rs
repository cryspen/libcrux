use crate::{
    constants::FIELD_MODULUS,
    simd::{portable, simd_trait::*},
};
use core::arch::x86_64::*;

#[derive(Clone, Copy)]
pub(crate) struct SIMD256Vector {
    elements: __m256i,
}

#[allow(non_snake_case)]
fn ZERO() -> SIMD256Vector {
    SIMD256Vector {
        elements: unsafe { _mm256_setzero_si256() },
    }
}

fn to_i32_array(v: SIMD256Vector) -> [i32; 8] {
    let mut out = [0i32; 8];

    unsafe {
        _mm256_storeu_si256(out.as_mut_ptr() as *mut __m256i, v.elements);
    }

    out
}

fn from_i32_array(array: [i32; 8]) -> SIMD256Vector {
    SIMD256Vector {
        elements: unsafe { _mm256_loadu_si256(array.as_ptr() as *const __m256i) },
    }
}

fn add_constant(mut v: SIMD256Vector, c: i32) -> SIMD256Vector {
    let c = unsafe { _mm256_set1_epi32(c) };

    v.elements = unsafe { _mm256_add_epi32(v.elements, c) };

    v
}
fn add(mut lhs: SIMD256Vector, rhs: &SIMD256Vector) -> SIMD256Vector {
    lhs.elements = unsafe { _mm256_add_epi32(lhs.elements, rhs.elements) };

    lhs
}

fn sub(mut lhs: SIMD256Vector, rhs: &SIMD256Vector) -> SIMD256Vector {
    lhs.elements = unsafe { _mm256_sub_epi32(lhs.elements, rhs.elements) };

    lhs
}

fn multiply_by_constant(mut v: SIMD256Vector, c: i32) -> SIMD256Vector {
    let c = unsafe { _mm256_set1_epi32(c) };

    // In theory, we could get the wrong answer if the product occupies
    // more than 32 bits, but so far in the Kyber code that doesn't seem
    // to be the case.
    v.elements = unsafe { _mm256_mullo_epi32(v.elements, c) };

    v
}

fn bitwise_and_with_constant(mut v: SIMD256Vector, c: i32) -> SIMD256Vector {
    let c = unsafe { _mm256_set1_epi32(c) };

    v.elements = unsafe { _mm256_and_si256(v.elements, c) };

    v
}

fn shift_right<const SHIFT_BY: i32>(mut v: SIMD256Vector) -> SIMD256Vector {
    v.elements = unsafe { _mm256_srai_epi32(v.elements, SHIFT_BY) };

    v
}

fn shift_left<const SHIFT_BY: i32>(mut v: SIMD256Vector) -> SIMD256Vector {
    v.elements = unsafe { _mm256_slli_epi32(v.elements, SHIFT_BY) };

    v
}

fn cond_subtract_3329(mut v: SIMD256Vector) -> SIMD256Vector {
    unsafe {
        let field_modulus = _mm256_set1_epi32(FIELD_MODULUS);

        v.elements = _mm256_sub_epi32(v.elements, field_modulus);

        let mut mask = _mm256_srai_epi32(v.elements, 31);
        mask = _mm256_and_si256(mask, field_modulus);

        v.elements = _mm256_add_epi32(v.elements, mask);
    }

    v
}

fn barrett_reduce(v: SIMD256Vector) -> SIMD256Vector {
    let input = portable::PortableVector::from_i32_array(to_i32_array(v));
    let output = portable::PortableVector::barrett_reduce(input);

    from_i32_array(portable::PortableVector::to_i32_array(output))
}

fn montgomery_reduce(v: SIMD256Vector) -> SIMD256Vector {
    let input = portable::PortableVector::from_i32_array(to_i32_array(v));
    let output = portable::PortableVector::montgomery_reduce(input);

    from_i32_array(portable::PortableVector::to_i32_array(output))
}

fn compress_1(mut v: SIMD256Vector) -> SIMD256Vector {
    unsafe {
        let field_modulus_halved = _mm256_set1_epi32((FIELD_MODULUS - 1) / 2);
        let field_modulus_quartered = _mm256_set1_epi32((FIELD_MODULUS - 1) / 4);

        v.elements = _mm256_sub_epi32(field_modulus_halved, v.elements);
        let mask = _mm256_srai_epi32(v.elements, 31);

        v.elements = _mm256_xor_si256(mask, v.elements);
        v.elements = _mm256_sub_epi32(v.elements, field_modulus_quartered);

        v.elements = _mm256_srli_epi32(v.elements, 31);
    }

    v
}

fn compress(coefficient_bits: u8, v: SIMD256Vector) -> SIMD256Vector {
    let input = portable::PortableVector::from_i32_array(to_i32_array(v));
    let output = portable::PortableVector::compress(coefficient_bits, input);

    from_i32_array(portable::PortableVector::to_i32_array(output))
}

fn ntt_layer_1_step(v: SIMD256Vector, zeta1: i32, zeta2: i32) -> SIMD256Vector {
    let input = portable::PortableVector::from_i32_array(to_i32_array(v));
    let output = portable::PortableVector::ntt_layer_1_step(input, zeta1, zeta2);

    from_i32_array(portable::PortableVector::to_i32_array(output))
}

fn ntt_layer_2_step(v: SIMD256Vector, zeta: i32) -> SIMD256Vector {
    let input = portable::PortableVector::from_i32_array(to_i32_array(v));
    let output = portable::PortableVector::ntt_layer_2_step(input, zeta);

    from_i32_array(portable::PortableVector::to_i32_array(output))
}

fn inv_ntt_layer_1_step(v: SIMD256Vector, zeta1: i32, zeta2: i32) -> SIMD256Vector {
    let input = portable::PortableVector::from_i32_array(to_i32_array(v));
    let output = portable::PortableVector::inv_ntt_layer_1_step(input, zeta1, zeta2);

    from_i32_array(portable::PortableVector::to_i32_array(output))
}

fn inv_ntt_layer_2_step(v: SIMD256Vector, zeta: i32) -> SIMD256Vector {
    let input = portable::PortableVector::from_i32_array(to_i32_array(v));
    let output = portable::PortableVector::inv_ntt_layer_2_step(input, zeta);

    from_i32_array(portable::PortableVector::to_i32_array(output))
}

fn ntt_multiply(lhs: &SIMD256Vector, rhs: &SIMD256Vector, zeta0: i32, zeta1: i32) -> SIMD256Vector {
    let input1 = portable::PortableVector::from_i32_array(to_i32_array(*lhs));
    let input2 = portable::PortableVector::from_i32_array(to_i32_array(*rhs));

    let output = portable::PortableVector::ntt_multiply(&input1, &input2, zeta0, zeta1);

    from_i32_array(portable::PortableVector::to_i32_array(output))
}

fn serialize_1(mut v: SIMD256Vector) -> u8 {
    let mut shifted_bytes = [0i32; 8];

    unsafe {
        let shifts = _mm256_set_epi32(7, 6, 5, 4, 3, 2, 1, 0);

        v.elements = _mm256_sllv_epi32(v.elements, shifts);

        _mm256_store_si256(shifted_bytes.as_mut_ptr() as *mut __m256i, v.elements);
    }

    (shifted_bytes[0]
        | shifted_bytes[1]
        | shifted_bytes[2]
        | shifted_bytes[3]
        | shifted_bytes[4]
        | shifted_bytes[5]
        | shifted_bytes[6]
        | shifted_bytes[7]) as u8
}

fn deserialize_1(a: u8) -> SIMD256Vector {
    let output = portable::PortableVector::deserialize_1(a);

    from_i32_array(portable::PortableVector::to_i32_array(output))
}

fn serialize_4(v: SIMD256Vector) -> [u8; 4] {
    let input = portable::PortableVector::from_i32_array(to_i32_array(v));
    portable::PortableVector::serialize_4(input)
}
fn deserialize_4(v: &[u8]) -> SIMD256Vector {
    let output = portable::PortableVector::deserialize_4(v);

    from_i32_array(portable::PortableVector::to_i32_array(output))
}

fn serialize_5(v: SIMD256Vector) -> [u8; 5] {
    let input = portable::PortableVector::from_i32_array(to_i32_array(v));

    portable::PortableVector::serialize_5(input)
}
fn deserialize_5(v: &[u8]) -> SIMD256Vector {
    let output = portable::PortableVector::deserialize_5(v);

    from_i32_array(portable::PortableVector::to_i32_array(output))
}

fn serialize_10(v: SIMD256Vector) -> [u8; 10] {
    let input = portable::PortableVector::from_i32_array(to_i32_array(v));
    portable::PortableVector::serialize_10(input)
}
fn deserialize_10(v: &[u8]) -> SIMD256Vector {
    let output = portable::PortableVector::deserialize_10(v);

    from_i32_array(portable::PortableVector::to_i32_array(output))
}

fn serialize_11(v: SIMD256Vector) -> [u8; 11] {
    let input = portable::PortableVector::from_i32_array(to_i32_array(v));
    portable::PortableVector::serialize_11(input)
}
fn deserialize_11(v: &[u8]) -> SIMD256Vector {
    let output = portable::PortableVector::deserialize_11(v);

    from_i32_array(portable::PortableVector::to_i32_array(output))
}

fn serialize_12(v: SIMD256Vector) -> [u8; 12] {
    let input = portable::PortableVector::from_i32_array(to_i32_array(v));

    portable::PortableVector::serialize_12(input)
}

fn deserialize_12(v: &[u8]) -> SIMD256Vector {
    let output = portable::PortableVector::deserialize_12(v);

    from_i32_array(portable::PortableVector::to_i32_array(output))
}

impl Operations for SIMD256Vector {
    fn ZERO() -> Self {
        ZERO()
    }

    fn to_i32_array(v: Self) -> [i32; 8] {
        to_i32_array(v)
    }

    fn from_i32_array(array: [i32; 8]) -> Self {
        from_i32_array(array)
    }

    fn add_constant(v: Self, c: i32) -> Self {
        add_constant(v, c)
    }

    fn add(lhs: Self, rhs: &Self) -> Self {
        add(lhs, rhs)
    }

    fn sub(lhs: Self, rhs: &Self) -> Self {
        sub(lhs, rhs)
    }

    fn multiply_by_constant(v: Self, c: i32) -> Self {
        multiply_by_constant(v, c)
    }

    fn bitwise_and_with_constant(v: Self, c: i32) -> Self {
        bitwise_and_with_constant(v, c)
    }

    fn shift_right<const SHIFT_BY: i32>(v: Self) -> Self {
        shift_right::<{ SHIFT_BY }>(v)
    }

    fn shift_left<const SHIFT_BY: i32>(v: Self) -> Self {
        shift_left::<{ SHIFT_BY }>(v)
    }

    fn cond_subtract_3329(v: Self) -> Self {
        cond_subtract_3329(v)
    }

    fn barrett_reduce(v: Self) -> Self {
        barrett_reduce(v)
    }

    fn montgomery_reduce(v: Self) -> Self {
        montgomery_reduce(v)
    }

    fn compress_1(v: Self) -> Self {
        compress_1(v)
    }

    fn compress(coefficient_bits: u8, v: Self) -> Self {
        compress(coefficient_bits, v)
    }

    fn ntt_layer_1_step(a: Self, zeta1: i32, zeta2: i32) -> Self {
        ntt_layer_1_step(a, zeta1, zeta2)
    }

    fn ntt_layer_2_step(a: Self, zeta: i32) -> Self {
        ntt_layer_2_step(a, zeta)
    }

    fn inv_ntt_layer_1_step(a: Self, zeta1: i32, zeta2: i32) -> Self {
        inv_ntt_layer_1_step(a, zeta1, zeta2)
    }

    fn inv_ntt_layer_2_step(a: Self, zeta: i32) -> Self {
        inv_ntt_layer_2_step(a, zeta)
    }

    fn ntt_multiply(lhs: &Self, rhs: &Self, zeta0: i32, zeta1: i32) -> Self {
        ntt_multiply(lhs, rhs, zeta0, zeta1)
    }

    fn serialize_1(a: Self) -> u8 {
        serialize_1(a)
    }

    fn deserialize_1(a: u8) -> Self {
        deserialize_1(a)
    }

    fn serialize_4(a: Self) -> [u8; 4] {
        serialize_4(a)
    }

    fn deserialize_4(a: &[u8]) -> Self {
        deserialize_4(a)
    }

    fn serialize_5(a: Self) -> [u8; 5] {
        serialize_5(a)
    }

    fn deserialize_5(a: &[u8]) -> Self {
        deserialize_5(a)
    }

    fn serialize_10(a: Self) -> [u8; 10] {
        serialize_10(a)
    }

    fn deserialize_10(a: &[u8]) -> Self {
        deserialize_10(a)
    }

    fn serialize_11(a: Self) -> [u8; 11] {
        serialize_11(a)
    }

    fn deserialize_11(a: &[u8]) -> Self {
        deserialize_11(a)
    }

    fn serialize_12(a: Self) -> [u8; 12] {
        serialize_12(a)
    }

    fn deserialize_12(a: &[u8]) -> Self {
        deserialize_12(a)
    }
}
