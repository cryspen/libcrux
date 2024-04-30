use crate::{
    arithmetic::{
        BARRETT_MULTIPLIER, BARRETT_R, BARRETT_SHIFT, INVERSE_OF_MODULUS_MOD_MONTGOMERY_R,
        MONTGOMERY_SHIFT,
    },
    compress::CIPHERTEXT_COMPRESSION_MULTIPLIER,
    constants::FIELD_MODULUS,
    simd::{portable, simd_trait::*},
};
use core::arch::x86_64::*;

#[derive(Clone, Copy)]
pub(crate) struct SIMD256Vector {
    elements: __m256i,
}

#[allow(dead_code)]
fn print_m256i_as_i32s(a: __m256i, prefix: String) {
    let mut a_bytes = [0i32; 8];
    unsafe { _mm256_store_si256(a_bytes.as_mut_ptr() as *mut __m256i, a) };
    println!("{}: {:?}", prefix, a_bytes);
}

#[allow(non_snake_case)]
#[inline(always)]
fn ZERO() -> SIMD256Vector {
    SIMD256Vector {
        elements: unsafe { _mm256_setzero_si256() },
    }
}

#[inline(always)]
fn to_i32_array(v: SIMD256Vector) -> [i32; 8] {
    let mut out = [0i32; 8];

    unsafe {
        _mm256_storeu_si256(out.as_mut_ptr() as *mut __m256i, v.elements);
    }

    out
}

#[inline(always)]
fn from_i32_array(array: [i32; 8]) -> SIMD256Vector {
    SIMD256Vector {
        elements: unsafe { _mm256_loadu_si256(array.as_ptr() as *const __m256i) },
    }
}

#[inline(always)]
fn add_constant(mut v: SIMD256Vector, c: i32) -> SIMD256Vector {
    let c = unsafe { _mm256_set1_epi32(c) };

    v.elements = unsafe { _mm256_add_epi32(v.elements, c) };

    v
}

#[inline(always)]
fn add(mut lhs: SIMD256Vector, rhs: &SIMD256Vector) -> SIMD256Vector {
    lhs.elements = unsafe { _mm256_add_epi32(lhs.elements, rhs.elements) };

    lhs
}

#[inline(always)]
fn sub(mut lhs: SIMD256Vector, rhs: &SIMD256Vector) -> SIMD256Vector {
    lhs.elements = unsafe { _mm256_sub_epi32(lhs.elements, rhs.elements) };

    lhs
}

#[inline(always)]
fn multiply_by_constant(mut v: SIMD256Vector, c: i32) -> SIMD256Vector {
    let c = unsafe { _mm256_set1_epi32(c) };

    // In theory, we could get the wrong answer if the product occupies
    // more than 32 bits, but so far in the Kyber code that doesn't seem
    // to be the case.
    v.elements = unsafe { _mm256_mullo_epi32(v.elements, c) };

    v
}

#[inline(always)]
fn bitwise_and_with_constant(mut v: SIMD256Vector, c: i32) -> SIMD256Vector {
    let c = unsafe { _mm256_set1_epi32(c) };

    v.elements = unsafe { _mm256_and_si256(v.elements, c) };

    v
}

#[inline(always)]
fn shift_right<const SHIFT_BY: i32>(mut v: SIMD256Vector) -> SIMD256Vector {
    v.elements = unsafe { _mm256_srai_epi32(v.elements, SHIFT_BY) };

    v
}

#[inline(always)]
fn shift_left<const SHIFT_BY: i32>(mut v: SIMD256Vector) -> SIMD256Vector {
    v.elements = unsafe { _mm256_slli_epi32(v.elements, SHIFT_BY) };

    v
}

#[inline(always)]
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

#[inline(always)]
fn barrett_reduce(v: SIMD256Vector) -> SIMD256Vector {
    let reduced = unsafe {
        let barrett_multiplier = _mm256_set1_epi32(BARRETT_MULTIPLIER as i32);
        let barrett_r_halved = _mm256_set1_epi64x(BARRETT_R >> 1);
        let field_modulus = _mm256_set1_epi32(FIELD_MODULUS);

        let mut t_low = _mm256_mul_epi32(v.elements, barrett_multiplier);
        t_low = _mm256_add_epi64(t_low, barrett_r_halved);
        let quotient_low = _mm256_srli_epi64(t_low, BARRETT_SHIFT as i32);

        let mut t_high = _mm256_shuffle_epi32(v.elements, 0b00_11_00_01);
        t_high = _mm256_mul_epi32(t_high, barrett_multiplier);
        t_high = _mm256_add_epi64(t_high, barrett_r_halved);

        // Right shift by 26, then left shift by 32
        let quotient_high = _mm256_slli_epi64(t_high, 6);

        let quotient = _mm256_blend_epi32(quotient_low, quotient_high, 0b1_0_1_0_1_0_1_0);
        let quotient = _mm256_mullo_epi32(quotient, field_modulus);

        _mm256_sub_epi32(v.elements, quotient)
    };

    SIMD256Vector { elements: reduced }
}

#[inline(always)]
fn montgomery_reduce(v: SIMD256Vector) -> SIMD256Vector {
    let reduced = unsafe {
        let montgomery_shift_mask = _mm256_set1_epi32((1 << MONTGOMERY_SHIFT) - 1);
        let field_modulus = _mm256_set1_epi32(FIELD_MODULUS);
        let inverse_of_modulus_mod_montgomery_r =
            _mm256_set1_epi32(INVERSE_OF_MODULUS_MOD_MONTGOMERY_R as i32);

        let t = _mm256_and_si256(v.elements, montgomery_shift_mask);
        let t = _mm256_mullo_epi32(t, inverse_of_modulus_mod_montgomery_r);

        let k = _mm256_and_si256(t, montgomery_shift_mask);
        let k = _mm256_slli_epi32(k, 16);
        let k = _mm256_srai_epi32(k, 16);

        let k_times_modulus = _mm256_mullo_epi32(k, field_modulus);
        let c = _mm256_srai_epi32(k_times_modulus, MONTGOMERY_SHIFT as i32);
        let value_high = _mm256_srai_epi32(v.elements, MONTGOMERY_SHIFT as i32);

        _mm256_sub_epi32(value_high, c)
    };

    SIMD256Vector { elements: reduced }
}

#[inline(always)]
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

#[inline(always)]
fn compress<const COEFFICIENT_BITS: i32>(mut v: SIMD256Vector) -> SIMD256Vector {
    let compressed = unsafe {
        let field_modulus_halved = _mm256_set1_epi32((FIELD_MODULUS - 1) / 2);
        let coefficient_bits_mask = _mm256_set1_epi32((1 << COEFFICIENT_BITS) - 1);
        let multiplier = _mm256_set1_epi32(CIPHERTEXT_COMPRESSION_MULTIPLIER);

        v.elements = _mm256_slli_epi32(v.elements, COEFFICIENT_BITS);
        v.elements = _mm256_add_epi32(v.elements, field_modulus_halved);

        let compressed_half_1 = _mm256_mul_epu32(v.elements, multiplier);
        let compressed_half_1 = _mm256_srli_epi64(compressed_half_1, 35);

        let compressed_half_2 = _mm256_shuffle_epi32(v.elements, 0b00_11_00_01);
        let compressed_half_2 = _mm256_mul_epu32(compressed_half_2, multiplier);
        // Right shift by 35, and then left shift by 32
        let compressed_half_2 = _mm256_srli_epi64(compressed_half_2, 3);

        let compressed =
            _mm256_blend_epi32(compressed_half_1, compressed_half_2, 0b1_0_1_0_1_0_1_0);

        _mm256_and_si256(compressed, coefficient_bits_mask)
    };

    SIMD256Vector {
        elements: compressed,
    }
}

#[inline(always)]
fn ntt_layer_1_step(v: SIMD256Vector, zeta1: i32, zeta2: i32) -> SIMD256Vector {
    let result = unsafe {
        let zetas = _mm256_set_epi32(-zeta2, -zeta2, zeta2, zeta2, -zeta1, -zeta1, zeta1, zeta1);
        let zeta_multipliers = _mm256_shuffle_epi32(v.elements, 0b11_10_11_10);

        let rhs = _mm256_mullo_epi32(zeta_multipliers, zetas);
        let rhs = montgomery_reduce(SIMD256Vector { elements: rhs}).elements;

        let lhs = _mm256_shuffle_epi32(v.elements, 0b01_00_01_00);

        _mm256_add_epi32(rhs, lhs)
    };

    SIMD256Vector {
        elements: result
    }
}

#[inline(always)]
fn ntt_layer_2_step(v: SIMD256Vector, zeta: i32) -> SIMD256Vector {
    let result = unsafe {
        let zetas = _mm256_set_epi32(-zeta, -zeta, -zeta, -zeta, zeta, zeta, zeta, zeta);
        let zeta_multipliers = _mm256_permute4x64_epi64(v.elements, 0b11_10_11_10);

        let rhs = _mm256_mullo_epi32(zeta_multipliers, zetas);
        let rhs = montgomery_reduce(SIMD256Vector { elements: rhs}).elements;

        let lhs = _mm256_permute4x64_epi64(v.elements, 0b01_00_01_00);

        _mm256_add_epi32(rhs, lhs)
    };

    SIMD256Vector {
        elements: result
    }
}

#[inline(always)]
fn inv_ntt_layer_1_step(v: SIMD256Vector, zeta1: i32, zeta2: i32) -> SIMD256Vector {
    let result = unsafe {
        let zetas = _mm256_set_epi32(zeta2, zeta2, 0, 0, zeta1, zeta1, 0, 0);

        let add_by_signs = _mm256_set_epi32(-1, -1, 1, 1, -1, -1, 1, 1);

        //print_m256i_as_i32s(v.elements, String::from("Before shuffle."));
        let add_by = _mm256_shuffle_epi32(v.elements, 0b01_00_11_10);

        let add_by = _mm256_mullo_epi32(add_by, add_by_signs);

        let sums = _mm256_add_epi32(v.elements, add_by);

        let products = _mm256_mullo_epi32(sums, zetas);
        let products_reduced = montgomery_reduce(SIMD256Vector { elements: products }).elements;

        _mm256_blend_epi32(sums, products_reduced, 0b1_1_0_0_1_1_0_0)
    };

    SIMD256Vector {
        elements: result
    }
}

#[inline(always)]
fn inv_ntt_layer_2_step(v: SIMD256Vector, zeta: i32) -> SIMD256Vector {
    let input = portable::PortableVector::from_i32_array(to_i32_array(v));
    let output = portable::PortableVector::inv_ntt_layer_2_step(input, zeta);

    from_i32_array(portable::PortableVector::to_i32_array(output))
}

#[inline(always)]
fn ntt_multiply(lhs: &SIMD256Vector, rhs: &SIMD256Vector, zeta0: i32, zeta1: i32) -> SIMD256Vector {
    let result = unsafe {
        // Calculate the first element of the output binomial
        let zetas = _mm256_set_epi32(-zeta1, 0, zeta1, 0, -zeta0, 0, zeta0, 0);

        let left = _mm256_mullo_epi32(lhs.elements, rhs.elements);
        let right = montgomery_reduce(SIMD256Vector { elements: left });

        let right = _mm256_mullo_epi32(right.elements, zetas);

        let right = _mm256_shuffle_epi32(right, 0b00_11_00_01);

        let result_0 = _mm256_add_epi32(left, right);

        // Calculate the second element in the output binomial
        let rhs_adjacent_swapped = _mm256_shuffle_epi32(rhs.elements, 0b10_11_00_01);
        let result_1 = _mm256_mullo_epi32(lhs.elements, rhs_adjacent_swapped);

        let swapped = _mm256_shuffle_epi32(result_1, 0b10_00_00_00);
        let result_1 = _mm256_add_epi32(result_1, swapped);

        // Put them together
        _mm256_blend_epi32(result_0, result_1, 0b1_0_1_0_1_0_1_0)
    };

    montgomery_reduce(SIMD256Vector { elements: result })
}

#[inline(always)]
fn serialize_1(v: SIMD256Vector) -> u8 {
    let mut v_bytes = [0i32; 8];

    unsafe {
        _mm256_store_si256(v_bytes.as_mut_ptr() as *mut __m256i, v.elements);
    }

    (v_bytes[0]
        | (v_bytes[1] << 1)
        | (v_bytes[2] << 2)
        | (v_bytes[3] << 3)
        | (v_bytes[4] << 4)
        | (v_bytes[5] << 5)
        | (v_bytes[6] << 6)
        | (v_bytes[7] << 7)) as u8
}

#[inline(always)]
fn deserialize_1(a: u8) -> SIMD256Vector {
    let deserialized = unsafe {
        let a = a as i32;

        _mm256_set_epi32(
            (a >> 7) & 1,
            (a >> 6) & 1,
            (a >> 5) & 1,
            (a >> 4) & 1,
            (a >> 3) & 1,
            (a >> 2) & 1,
            (a >> 1) & 1,
            a & 1,
        )
    };

    SIMD256Vector {
        elements: deserialized,
    }
}

#[inline(always)]
fn serialize_4(mut v: SIMD256Vector) -> [u8; 4] {
    let mut out = [0u8; 4];

    unsafe {
        let shifts = _mm256_set_epi32(0, 4, 0, 4, 0, 4, 0, 4);
        let shuffle_to = _mm256_set_epi8(
            31, 30, 29, 28, 27, 26, 25, 24, 23, 22, 21, 20, 12, 8, 4, 0, 15, 14, 13, 12, 11, 10, 9,
            8, 7, 6, 5, 4, 12, 8, 4, 0,
        );

        v.elements = _mm256_sllv_epi32(v.elements, shifts);
        v.elements = _mm256_shuffle_epi8(v.elements, shuffle_to);
        v.elements = _mm256_srli_epi16(v.elements, 4);

        out[0] = _mm256_extract_epi16(v.elements, 0) as u8;
        out[1] = _mm256_extract_epi16(v.elements, 1) as u8;
        out[2] = _mm256_extract_epi16(v.elements, 8) as u8;
        out[3] = _mm256_extract_epi16(v.elements, 9) as u8;
    }

    out
}

#[inline(always)]
fn deserialize_4(v: &[u8]) -> SIMD256Vector {
    let deserialized = unsafe {
        let mut deserialized = _mm256_set_epi32(
            v[3] as i32,
            v[3] as i32,
            v[2] as i32,
            v[2] as i32,
            v[1] as i32,
            v[1] as i32,
            v[0] as i32,
            v[0] as i32,
        );

        let shifts = _mm256_set_epi32(4, 0, 4, 0, 4, 0, 4, 0);
        let last_4_bits_mask = _mm256_set1_epi32(0xF);
        deserialized = _mm256_srlv_epi32(deserialized, shifts);
        deserialized = _mm256_and_si256(deserialized, last_4_bits_mask);

        deserialized
    };

    SIMD256Vector {
        elements: deserialized,
    }
}

#[inline(always)]
fn serialize_5(v: SIMD256Vector) -> [u8; 5] {
    let input = portable::PortableVector::from_i32_array(to_i32_array(v));

    portable::PortableVector::serialize_5(input)
}

#[inline(always)]
fn deserialize_5(v: &[u8]) -> SIMD256Vector {
    let output = portable::PortableVector::deserialize_5(v);

    from_i32_array(portable::PortableVector::to_i32_array(output))
}

#[inline(always)]
fn serialize_10(v: SIMD256Vector) -> [u8; 10] {
    let input = portable::PortableVector::from_i32_array(to_i32_array(v));
    portable::PortableVector::serialize_10(input)
}

#[inline(always)]
fn deserialize_10(v: &[u8]) -> SIMD256Vector {
    let output = portable::PortableVector::deserialize_10(v);

    from_i32_array(portable::PortableVector::to_i32_array(output))
}

#[inline(always)]
fn serialize_11(v: SIMD256Vector) -> [u8; 11] {
    let input = portable::PortableVector::from_i32_array(to_i32_array(v));
    portable::PortableVector::serialize_11(input)
}

#[inline(always)]
fn deserialize_11(v: &[u8]) -> SIMD256Vector {
    let output = portable::PortableVector::deserialize_11(v);

    from_i32_array(portable::PortableVector::to_i32_array(output))
}

#[inline(always)]
fn serialize_12(v: SIMD256Vector) -> [u8; 12] {
    let input = portable::PortableVector::from_i32_array(to_i32_array(v));

    portable::PortableVector::serialize_12(input)
}

#[inline(always)]
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

    fn compress<const COEFFICIENT_BITS: i32>(v: Self) -> Self {
        compress::<COEFFICIENT_BITS>(v)
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
