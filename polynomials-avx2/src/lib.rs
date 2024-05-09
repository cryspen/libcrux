use core::arch::x86_64::*;
use libcrux_traits::{Operations, FIELD_MODULUS, INVERSE_OF_MODULUS_MOD_MONTGOMERY_R};

mod debug;
mod portable;

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
fn from_i16_array(array: [i16; 16]) -> SIMD256Vector {
    SIMD256Vector {
        elements: unsafe { _mm256_loadu_si256(array.as_ptr() as *const __m256i) },
    }
}

#[inline(always)]
fn add(mut lhs: SIMD256Vector, rhs: &SIMD256Vector) -> SIMD256Vector {
    lhs.elements = unsafe { _mm256_add_epi16(lhs.elements, rhs.elements) };

    lhs
}

#[inline(always)]
fn sub(mut lhs: SIMD256Vector, rhs: &SIMD256Vector) -> SIMD256Vector {
    lhs.elements = unsafe { _mm256_sub_epi16(lhs.elements, rhs.elements) };

    lhs
}

#[inline(always)]
fn multiply_by_constant(mut v: SIMD256Vector, c: i16) -> SIMD256Vector {
    v.elements = unsafe {
        let c = _mm256_set1_epi16(c);

        _mm256_mullo_epi16(v.elements, c)
    };

    v
}

#[inline(always)]
fn bitwise_and_with_constant(mut v: SIMD256Vector, c: i16) -> SIMD256Vector {
    v.elements = unsafe {
        let c = _mm256_set1_epi16(c);

        _mm256_and_si256(v.elements, c)
    };

    v
}

#[inline(always)]
fn shift_right<const SHIFT_BY: i32>(mut v: SIMD256Vector) -> SIMD256Vector {
    v.elements = unsafe { _mm256_srai_epi16(v.elements, SHIFT_BY) };

    v
}

#[inline(always)]
fn shift_left<const SHIFT_BY: i32>(mut v: SIMD256Vector) -> SIMD256Vector {
    v.elements = unsafe { _mm256_slli_epi16(v.elements, SHIFT_BY) };

    v
}

#[inline(always)]
fn cond_subtract_3329(mut v: SIMD256Vector) -> SIMD256Vector {
    v.elements = unsafe {
        let field_modulus = _mm256_set1_epi16(FIELD_MODULUS);

        let v_minus_field_modulus = _mm256_sub_epi16(v.elements, field_modulus);

        let sign_mask = _mm256_srai_epi16(v_minus_field_modulus, 15);
        let conditional_add_field_modulus = _mm256_and_si256(sign_mask, field_modulus);

        _mm256_add_epi16(v_minus_field_modulus, conditional_add_field_modulus)
    };

    v
}

#[inline(always)]
fn barrett_reduce(v: SIMD256Vector) -> SIMD256Vector {
    let input = portable::from_i16_array(to_i16_array(v));
    let output = portable::barrett_reduce(input);

    from_i16_array(portable::to_i16_array(output))
}

#[inline(always)]
fn montgomery_multiply_by_constant(mut v: SIMD256Vector, c: i16) -> SIMD256Vector {
    v.elements = unsafe {
        let c = _mm256_set1_epi16(c);
        let value_low = _mm256_mullo_epi16(v.elements, c);

        let k = _mm256_mullo_epi16(
            value_low,
            _mm256_set1_epi16(INVERSE_OF_MODULUS_MOD_MONTGOMERY_R as i16),
        );
        let k_times_modulus = _mm256_mulhi_epi16(k, _mm256_set1_epi16(FIELD_MODULUS));

        let value_high = _mm256_mulhi_epi16(v.elements, c);

        _mm256_sub_epi16(value_high, k_times_modulus)
    };

    v
}

#[inline(always)]
fn compress_1(mut v: SIMD256Vector) -> SIMD256Vector {
    v.elements = unsafe {
        let field_modulus_halved = _mm256_set1_epi16((FIELD_MODULUS - 1) / 2);
        let field_modulus_quartered = _mm256_set1_epi16((FIELD_MODULUS - 1) / 4);

        let shifted = _mm256_sub_epi16(field_modulus_halved, v.elements);
        let mask = _mm256_srai_epi16(shifted, 15);

        let shifted_to_positive = _mm256_xor_si256(mask, shifted);
        let shifted_to_positive_in_range =
            _mm256_sub_epi16(shifted_to_positive, field_modulus_quartered);

        _mm256_srli_epi16(shifted_to_positive_in_range, 15)
    };

    v
}

#[inline(always)]
fn compress<const COEFFICIENT_BITS: i32>(v: SIMD256Vector) -> SIMD256Vector {
    let input = portable::from_i16_array(to_i16_array(v));
    let output = portable::compress::<{ COEFFICIENT_BITS }>(input);

    from_i16_array(portable::to_i16_array(output))
}

#[inline(always)]
fn decompress<const COEFFICIENT_BITS: i32>(v: SIMD256Vector) -> SIMD256Vector {
    let input = portable::from_i16_array(to_i16_array(v));
    let output = portable::decompress::<{ COEFFICIENT_BITS }>(input);

    from_i16_array(portable::to_i16_array(output))
}

#[inline(always)]
fn ntt_layer_1_step(
    v: SIMD256Vector,
    zeta0: i16,
    zeta1: i16,
    zeta2: i16,
    zeta3: i16,
) -> SIMD256Vector {
    let input = portable::from_i16_array(to_i16_array(v));
    let output = portable::ntt_layer_1_step(input, zeta0, zeta1, zeta2, zeta3);

    from_i16_array(portable::to_i16_array(output))
}

#[inline(always)]
fn ntt_layer_2_step(v: SIMD256Vector, zeta0: i16, zeta1: i16) -> SIMD256Vector {
    let input = portable::from_i16_array(to_i16_array(v));
    let output = portable::ntt_layer_2_step(input, zeta0, zeta1);

    from_i16_array(portable::to_i16_array(output))
}

#[inline(always)]
fn ntt_layer_3_step(v: SIMD256Vector, zeta: i16) -> SIMD256Vector {
    let input = portable::from_i16_array(to_i16_array(v));
    let output = portable::ntt_layer_3_step(input, zeta);

    from_i16_array(portable::to_i16_array(output))
}

#[inline(always)]
fn inv_ntt_layer_1_step(
    v: SIMD256Vector,
    zeta0: i16,
    zeta1: i16,
    zeta2: i16,
    zeta3: i16,
) -> SIMD256Vector {
    let input = portable::from_i16_array(to_i16_array(v));
    let output = portable::inv_ntt_layer_1_step(input, zeta0, zeta1, zeta2, zeta3);

    from_i16_array(portable::to_i16_array(output))
}

#[inline(always)]
fn inv_ntt_layer_2_step(v: SIMD256Vector, zeta0: i16, zeta1: i16) -> SIMD256Vector {
    let input = portable::from_i16_array(to_i16_array(v));
    let output = portable::inv_ntt_layer_2_step(input, zeta0, zeta1);

    from_i16_array(portable::to_i16_array(output))
}

#[inline(always)]
fn inv_ntt_layer_3_step(v: SIMD256Vector, zeta: i16) -> SIMD256Vector {
    let input = portable::from_i16_array(to_i16_array(v));
    let output = portable::inv_ntt_layer_3_step(input, zeta);

    from_i16_array(portable::to_i16_array(output))
}

#[inline(always)]
fn ntt_multiply(
    lhs: &SIMD256Vector,
    rhs: &SIMD256Vector,
    zeta0: i16,
    zeta1: i16,
    zeta2: i16,
    zeta3: i16,
) -> SIMD256Vector {
    let input0 = portable::from_i16_array(to_i16_array(*lhs));
    let input1 = portable::from_i16_array(to_i16_array(*rhs));

    let output = portable::ntt_multiply(&input0, &input1, zeta0, zeta1, zeta2, zeta3);

    from_i16_array(portable::to_i16_array(output))
}

#[inline(always)]
fn serialize_1(v: SIMD256Vector) -> [u8; 2] {
    let mut serialized = [0u8; 2];

    let bits_packed = unsafe {
        let lsb_shifted_up = _mm256_slli_epi16(v.elements, 7);

        let low_lanes = _mm256_castsi256_si128(lsb_shifted_up);
        let high_lanes = _mm256_extracti128_si256(lsb_shifted_up, 1);

        let msbs = _mm_packus_epi16(low_lanes, high_lanes);

        _mm_movemask_epi8(msbs)
    };

    serialized[0] = bits_packed as u8;
    serialized[1] = (bits_packed >> 8) as u8;

    serialized
}

#[inline(always)]
fn deserialize_1(a: &[u8]) -> SIMD256Vector {
    let output = portable::deserialize_1(a);

    from_i16_array(portable::to_i16_array(output))
}

#[inline(always)]
fn serialize_4(v: SIMD256Vector) -> [u8; 8] {
    let mut serialized = [0u8; 16];

    unsafe {
        let adjacent_2_combined = _mm256_madd_epi16(
            v.elements,
            _mm256_set_epi16(
                1 << 4,
                1,
                1 << 4,
                1,
                1 << 4,
                1,
                1 << 4,
                1,
                1 << 4,
                1,
                1 << 4,
                1,
                1 << 4,
                1,
                1 << 4,
                1,
            ),
        );

        let adjacent_8_combined = _mm256_shuffle_epi8(
            adjacent_2_combined,
            _mm256_set_epi8(
                -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, 12, 8, 4, 0, -1, -1, -1, -1, -1,
                -1, -1, -1, -1, -1, -1, -1, 12, 8, 4, 0,
            ),
        );

        let combined = _mm256_permutevar8x32_epi32(
            adjacent_8_combined,
            _mm256_set_epi32(0, 0, 0, 0, 0, 0, 4, 0),
        );
        let combined = _mm256_castsi256_si128(combined);

        _mm_storeu_si128(serialized.as_mut_ptr() as *mut __m128i, combined);
    }

    serialized[0..8].try_into().unwrap()
}

#[inline(always)]
fn deserialize_4(v: &[u8]) -> SIMD256Vector {
    let output = portable::deserialize_4(v);

    from_i16_array(portable::to_i16_array(output))
}

#[inline(always)]
fn serialize_5(v: SIMD256Vector) -> [u8; 10] {
    let input = portable::from_i16_array(to_i16_array(v));

    portable::serialize_5(input)
}

#[inline(always)]
fn deserialize_5(v: &[u8]) -> SIMD256Vector {
    let output = portable::deserialize_5(v);

    from_i16_array(portable::to_i16_array(output))
}

#[inline(always)]
fn serialize_10(v: SIMD256Vector) -> [u8; 20] {
    let mut serialized = [0u8; 32];

    unsafe {
        let adjacent_2_combined = _mm256_madd_epi16(
            v.elements,
            _mm256_set_epi16(
                1 << 10,
                1,
                1 << 10,
                1,
                1 << 10,
                1,
                1 << 10,
                1,
                1 << 10,
                1,
                1 << 10,
                1,
                1 << 10,
                1,
                1 << 10,
                1,
            ),
        );

        let adjacent_4_combined = _mm256_sllv_epi32(
            adjacent_2_combined,
            _mm256_set_epi32(0, 12, 0, 12, 0, 12, 0, 12),
        );
        let adjacent_4_combined = _mm256_srli_epi64(adjacent_4_combined, 12);

        let adjacent_8_combined = _mm256_shuffle_epi8(
            adjacent_4_combined,
            _mm256_set_epi8(
                -1, -1, -1, -1, -1, -1, 12, 11, 10, 9, 8, 4, 3, 2, 1, 0, -1, -1, -1, -1, -1, -1,
                12, 11, 10, 9, 8, 4, 3, 2, 1, 0,
            ),
        );

        let lower_8 = _mm256_castsi256_si128(adjacent_8_combined);
        let upper_8 = _mm256_extracti128_si256(adjacent_8_combined, 1);

        _mm_storeu_si128(serialized.as_mut_ptr() as *mut __m128i, lower_8);
        _mm_storeu_si128(serialized.as_mut_ptr().offset(10) as *mut __m128i, upper_8);
    }

    serialized[0..20].try_into().unwrap()
}

#[inline(always)]
fn deserialize_10(v: &[u8]) -> SIMD256Vector {
    let output = portable::deserialize_10(v);

    from_i16_array(portable::to_i16_array(output))
}

#[inline(always)]
fn serialize_11(v: SIMD256Vector) -> [u8; 22] {
    let input = portable::from_i16_array(to_i16_array(v));

    portable::serialize_11(input)
}

#[inline(always)]
fn deserialize_11(v: &[u8]) -> SIMD256Vector {
    let output = portable::deserialize_11(v);

    from_i16_array(portable::to_i16_array(output))
}

#[inline(always)]
fn serialize_12(v: SIMD256Vector) -> [u8; 24] {
    let mut serialized = [0u8; 32];

    unsafe {
        let adjacent_2_combined = _mm256_madd_epi16(
            v.elements,
            _mm256_set_epi16(
                1 << 12,
                1,
                1 << 12,
                1,
                1 << 12,
                1,
                1 << 12,
                1,
                1 << 12,
                1,
                1 << 12,
                1,
                1 << 12,
                1,
                1 << 12,
                1,
            ),
        );

        let adjacent_4_combined = _mm256_sllv_epi32(
            adjacent_2_combined,
            _mm256_set_epi32(0, 8, 0, 8, 0, 8, 0, 8),
        );
        let adjacent_4_combined = _mm256_srli_epi64(adjacent_4_combined, 8);

        let adjacent_8_combined = _mm256_shuffle_epi8(
            adjacent_4_combined,
            _mm256_set_epi8(
                -1, -1, -1, -1, 13, 12, 11, 10, 9, 8, 5, 4, 3, 2, 1, 0, -1, -1, -1, -1, 13, 12, 11,
                10, 9, 8, 5, 4, 3, 2, 1, 0,
            ),
        );

        let lower_8 = _mm256_castsi256_si128(adjacent_8_combined);
        let upper_8 = _mm256_extracti128_si256(adjacent_8_combined, 1);

        _mm_storeu_si128(serialized.as_mut_ptr() as *mut __m128i, lower_8);
        _mm_storeu_si128(serialized.as_mut_ptr().offset(12) as *mut __m128i, upper_8);
    }

    serialized[0..24].try_into().unwrap()
}

#[inline(always)]
fn deserialize_12(v: &[u8]) -> SIMD256Vector {
    let output = portable::deserialize_12(v);

    from_i16_array(portable::to_i16_array(output))
}

#[inline(always)]
fn rej_sample(a: &[u8]) -> (usize, [i16; 16]) {
    portable::rej_sample(a)
}

impl Operations for SIMD256Vector {
    fn ZERO() -> Self {
        zero()
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

    fn montgomery_multiply_by_constant(v: Self, r: i16) -> Self {
        montgomery_multiply_by_constant(v, r)
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

    fn ntt_layer_1_step(a: Self, zeta0: i16, zeta1: i16, zeta2: i16, zeta3: i16) -> Self {
        ntt_layer_1_step(a, zeta0, zeta1, zeta2, zeta3)
    }

    fn ntt_layer_2_step(a: Self, zeta0: i16, zeta1: i16) -> Self {
        ntt_layer_2_step(a, zeta0, zeta1)
    }

    fn ntt_layer_3_step(a: Self, zeta: i16) -> Self {
        ntt_layer_3_step(a, zeta)
    }

    fn inv_ntt_layer_1_step(a: Self, zeta0: i16, zeta1: i16, zeta2: i16, zeta3: i16) -> Self {
        inv_ntt_layer_1_step(a, zeta0, zeta1, zeta2, zeta3)
    }

    fn inv_ntt_layer_2_step(a: Self, zeta0: i16, zeta1: i16) -> Self {
        inv_ntt_layer_2_step(a, zeta0, zeta1)
    }

    fn inv_ntt_layer_3_step(a: Self, zeta: i16) -> Self {
        inv_ntt_layer_3_step(a, zeta)
    }

    fn ntt_multiply(
        lhs: &Self,
        rhs: &Self,
        zeta0: i16,
        zeta1: i16,
        zeta2: i16,
        zeta3: i16,
    ) -> Self {
        ntt_multiply(lhs, rhs, zeta0, zeta1, zeta2, zeta3)
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
        rej_sample(a)
    }
}
