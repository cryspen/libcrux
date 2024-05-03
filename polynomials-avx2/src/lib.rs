use libcrux_traits::{Operations, FIELD_ELEMENTS_IN_VECTOR, FIELD_MODULUS};

pub(crate) const BARRETT_MULTIPLIER: i64 = 20159;
pub(crate) const BARRETT_SHIFT: i64 = 26;
pub(crate) const BARRETT_R: i64 = 1 << BARRETT_SHIFT;
pub(crate) const MONTGOMERY_SHIFT: u8 = 16;
pub(crate) const INVERSE_OF_MODULUS_MOD_MONTGOMERY_R: u32 = 62209; // FIELD_MODULUS^{-1} mod MONTGOMERY_R

use core::arch::x86_64::*;

#[derive(Clone, Copy)]
pub struct SIMD256Vector {
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
        let field_modulus = _mm256_set1_epi32(FIELD_MODULUS);
        let inverse_of_modulus_mod_montgomery_r =
            _mm256_set1_epi32(INVERSE_OF_MODULUS_MOD_MONTGOMERY_R as i32);

        let t = _mm256_mullo_epi16(v.elements, inverse_of_modulus_mod_montgomery_r);
        let k_times_modulus = _mm256_mulhi_epi16(t, field_modulus);
        let value_high = _mm256_srli_epi32(v.elements, MONTGOMERY_SHIFT as i32);
        let res = _mm256_sub_epi16(value_high, k_times_modulus);
        let res = _mm256_slli_epi32(res, 16);
        _mm256_srai_epi32(res, 16)
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
        let multiplier = _mm256_set1_epi32(10_321_340);

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
        let rhs = montgomery_reduce(SIMD256Vector { elements: rhs }).elements;

        let lhs = _mm256_shuffle_epi32(v.elements, 0b01_00_01_00);

        _mm256_add_epi32(rhs, lhs)
    };

    SIMD256Vector { elements: result }
}

#[inline(always)]
fn ntt_layer_2_step(v: SIMD256Vector, zeta: i32) -> SIMD256Vector {
    let result = unsafe {
        let zetas = _mm256_set_epi32(-zeta, -zeta, -zeta, -zeta, zeta, zeta, zeta, zeta);
        let zeta_multipliers = _mm256_permute4x64_epi64(v.elements, 0b11_10_11_10);

        let rhs = _mm256_mullo_epi32(zeta_multipliers, zetas);
        let rhs = montgomery_reduce(SIMD256Vector { elements: rhs }).elements;

        let lhs = _mm256_permute4x64_epi64(v.elements, 0b01_00_01_00);

        _mm256_add_epi32(rhs, lhs)
    };

    SIMD256Vector { elements: result }
}

#[inline(always)]
fn inv_ntt_layer_1_step(v: SIMD256Vector, zeta1: i32, zeta2: i32) -> SIMD256Vector {
    let result = unsafe {
        let zetas = _mm256_set_epi32(zeta2, zeta2, 0, 0, zeta1, zeta1, 0, 0);

        let add_by_signs = _mm256_set_epi32(-1, -1, 1, 1, -1, -1, 1, 1);
        let add_by = _mm256_shuffle_epi32(v.elements, 0b01_00_11_10);
        let add_by = _mm256_mullo_epi32(add_by, add_by_signs);

        let sums = _mm256_add_epi32(v.elements, add_by);

        let products = _mm256_mullo_epi32(sums, zetas);
        let products_reduced = montgomery_reduce(SIMD256Vector { elements: products }).elements;

        _mm256_blend_epi32(sums, products_reduced, 0b1_1_0_0_1_1_0_0)
    };

    SIMD256Vector { elements: result }
}

#[inline(always)]
fn inv_ntt_layer_2_step(v: SIMD256Vector, zeta: i32) -> SIMD256Vector {
    let result = unsafe {
        let zetas = _mm256_set_epi32(zeta, zeta, zeta, zeta, 0, 0, 0, 0);

        let add_by_signs = _mm256_set_epi32(-1, -1, -1, -1, 1, 1, 1, 1);
        let add_by = _mm256_permute4x64_epi64(v.elements, 0b01_00_11_10);
        let add_by = _mm256_mullo_epi32(add_by, add_by_signs);

        let sums = _mm256_add_epi32(v.elements, add_by);

        let products = _mm256_mullo_epi32(sums, zetas);
        let products_reduced = montgomery_reduce(SIMD256Vector { elements: products }).elements;

        _mm256_blend_epi32(sums, products_reduced, 0b1_1_1_1_0_0_0_0)
    };

    SIMD256Vector { elements: result }
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
    let input = PortableVector::from_i32_array(to_i32_array(v));

    PortableVector::serialize_5(input)
}

#[inline(always)]
fn deserialize_5(v: &[u8]) -> SIMD256Vector {
    let output = PortableVector::deserialize_5(v);

    from_i32_array(PortableVector::to_i32_array(output))
}

#[inline(always)]
fn serialize_10(v: SIMD256Vector) -> [u8; 10] {
    let input = PortableVector::from_i32_array(to_i32_array(v));
    PortableVector::serialize_10(input)
}

#[inline(always)]
fn deserialize_10(v: &[u8]) -> SIMD256Vector {
    let output = PortableVector::deserialize_10(v);

    from_i32_array(PortableVector::to_i32_array(output))
}

#[inline(always)]
fn serialize_11(v: SIMD256Vector) -> [u8; 11] {
    let input = PortableVector::from_i32_array(to_i32_array(v));
    PortableVector::serialize_11(input)
}

#[inline(always)]
fn deserialize_11(v: &[u8]) -> SIMD256Vector {
    let output = PortableVector::deserialize_11(v);

    from_i32_array(PortableVector::to_i32_array(output))
}

#[inline(always)]
fn serialize_12(v: SIMD256Vector) -> [u8; 12] {
    let input = PortableVector::from_i32_array(to_i32_array(v));

    PortableVector::serialize_12(input)
}

#[inline(always)]
fn deserialize_12(v: &[u8]) -> SIMD256Vector {
    let output = PortableVector::deserialize_12(v);

    from_i32_array(PortableVector::to_i32_array(output))
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

// --- XXX: DELETE

#[derive(Clone, Copy)]
pub(crate) struct PortableVector {
    pub(crate) elements: [i32; 8],
}
impl PortableVector {
    #[inline(always)]
    pub(crate) fn zero() -> PortableVector {
        PortableVector {
            elements: [0i32; FIELD_ELEMENTS_IN_VECTOR],
        }
    }

    #[inline(always)]
    pub(crate) fn deserialize_12(bytes: &[u8]) -> PortableVector {
        let mut re = PortableVector::zero();

        let byte0 = bytes[0] as i32;
        let byte1 = bytes[1] as i32;
        let byte2 = bytes[2] as i32;
        let byte3 = bytes[3] as i32;
        let byte4 = bytes[4] as i32;
        let byte5 = bytes[5] as i32;
        let byte6 = bytes[6] as i32;
        let byte7 = bytes[7] as i32;
        let byte8 = bytes[8] as i32;
        let byte9 = bytes[9] as i32;
        let byte10 = bytes[10] as i32;
        let byte11 = bytes[11] as i32;

        re.elements[0] = (byte1 & 0x0F) << 8 | (byte0 & 0xFF);
        re.elements[1] = (byte2 << 4) | ((byte1 >> 4) & 0x0F);

        re.elements[2] = (byte4 & 0x0F) << 8 | (byte3 & 0xFF);
        re.elements[3] = (byte5 << 4) | ((byte4 >> 4) & 0x0F);

        re.elements[4] = (byte7 & 0x0F) << 8 | (byte6 & 0xFF);
        re.elements[5] = (byte8 << 4) | ((byte7 >> 4) & 0x0F);

        re.elements[6] = (byte10 & 0x0F) << 8 | (byte9 & 0xFF);
        re.elements[7] = (byte11 << 4) | ((byte10 >> 4) & 0x0F);

        re
    }

    #[inline(always)]
    pub(crate) fn to_i32_array(v: PortableVector) -> [i32; 8] {
        v.elements
    }

    #[inline(always)]
    pub(crate) fn from_i32_array(array: [i32; 8]) -> PortableVector {
        PortableVector { elements: array }
    }

    #[inline(always)]
    pub(crate) fn deserialize_5(bytes: &[u8]) -> PortableVector {
        let mut v = PortableVector::zero();

        v.elements[0] = (bytes[0] & 0x1F) as i32;
        v.elements[1] = ((bytes[1] & 0x3) << 3 | (bytes[0] >> 5)) as i32;
        v.elements[2] = ((bytes[1] >> 2) & 0x1F) as i32;
        v.elements[3] = (((bytes[2] & 0xF) << 1) | (bytes[1] >> 7)) as i32;
        v.elements[4] = (((bytes[3] & 1) << 4) | (bytes[2] >> 4)) as i32;
        v.elements[5] = ((bytes[3] >> 1) & 0x1F) as i32;
        v.elements[6] = (((bytes[4] & 0x7) << 2) | (bytes[3] >> 6)) as i32;
        v.elements[7] = (bytes[4] >> 3) as i32;

        v
    }

    #[inline(always)]
    pub(crate) fn deserialize_10(bytes: &[u8]) -> PortableVector {
        let mut result = PortableVector::zero();

        result.elements[0] = ((bytes[1] as i32 & 0x03) << 8 | (bytes[0] as i32 & 0xFF)) as i32;
        result.elements[1] = ((bytes[2] as i32 & 0x0F) << 6 | (bytes[1] as i32 >> 2)) as i32;
        result.elements[2] = ((bytes[3] as i32 & 0x3F) << 4 | (bytes[2] as i32 >> 4)) as i32;
        result.elements[3] = (((bytes[4] as i32) << 2) | (bytes[3] as i32 >> 6)) as i32;

        result.elements[4] = ((bytes[6] as i32 & 0x03) << 8 | (bytes[5] as i32 & 0xFF)) as i32;
        result.elements[5] = ((bytes[7] as i32 & 0x0F) << 6 | (bytes[6] as i32 >> 2)) as i32;
        result.elements[6] = ((bytes[8] as i32 & 0x3F) << 4 | (bytes[7] as i32 >> 4)) as i32;
        result.elements[7] = (((bytes[9] as i32) << 2) | (bytes[8] as i32 >> 6)) as i32;

        result
    }

    #[inline(always)]
    pub(crate) fn deserialize_11(bytes: &[u8]) -> PortableVector {
        let mut result = PortableVector::zero();
        result.elements[0] = ((bytes[1] as i32 & 0x7) << 8 | bytes[0] as i32) as i32;
        result.elements[1] = ((bytes[2] as i32 & 0x3F) << 5 | (bytes[1] as i32 >> 3)) as i32;
        result.elements[2] = ((bytes[4] as i32 & 0x1) << 10
            | ((bytes[3] as i32) << 2)
            | ((bytes[2] as i32) >> 6)) as i32;
        result.elements[3] = ((bytes[5] as i32 & 0xF) << 7 | (bytes[4] as i32 >> 1)) as i32;
        result.elements[4] = ((bytes[6] as i32 & 0x7F) << 4 | (bytes[5] as i32 >> 4)) as i32;
        result.elements[5] = ((bytes[8] as i32 & 0x3) << 9
            | ((bytes[7] as i32) << 1)
            | ((bytes[6] as i32) >> 7)) as i32;
        result.elements[6] = ((bytes[9] as i32 & 0x1F) << 6 | (bytes[8] as i32 >> 2)) as i32;
        result.elements[7] = (((bytes[10] as i32) << 3) | (bytes[9] as i32 >> 5)) as i32;
        result
    }

    #[inline(always)]
    pub(crate) fn serialize_11(v: PortableVector) -> [u8; 11] {
        let mut result = [0u8; 11];
        result[0] = v.elements[0] as u8;
        result[1] = ((v.elements[1] & 0x1F) as u8) << 3 | ((v.elements[0] >> 8) as u8);
        result[2] = ((v.elements[2] & 0x3) as u8) << 6 | ((v.elements[1] >> 5) as u8);
        result[3] = ((v.elements[2] >> 2) & 0xFF) as u8;
        result[4] = ((v.elements[3] & 0x7F) as u8) << 1 | (v.elements[2] >> 10) as u8;
        result[5] = ((v.elements[4] & 0xF) as u8) << 4 | (v.elements[3] >> 7) as u8;
        result[6] = ((v.elements[5] & 0x1) as u8) << 7 | (v.elements[4] >> 4) as u8;
        result[7] = ((v.elements[5] >> 1) & 0xFF) as u8;
        result[8] = ((v.elements[6] & 0x3F) as u8) << 2 | (v.elements[5] >> 9) as u8;
        result[9] = ((v.elements[7] & 0x7) as u8) << 5 | (v.elements[6] >> 6) as u8;
        result[10] = (v.elements[7] >> 3) as u8;
        result
    }

    #[inline(always)]
    fn serialize_12(v: PortableVector) -> [u8; 12] {
        let mut result = [0u8; 12];

        result[0] = (v.elements[0] & 0xFF) as u8;
        result[1] = ((v.elements[0] >> 8) | ((v.elements[1] & 0x0F) << 4)) as u8;
        result[2] = ((v.elements[1] >> 4) & 0xFF) as u8;

        result[3] = (v.elements[2] & 0xFF) as u8;
        result[4] = ((v.elements[2] >> 8) | ((v.elements[3] & 0x0F) << 4)) as u8;
        result[5] = ((v.elements[3] >> 4) & 0xFF) as u8;

        result[6] = (v.elements[4] & 0xFF) as u8;
        result[7] = ((v.elements[4] >> 8) | ((v.elements[5] & 0x0F) << 4)) as u8;
        result[8] = ((v.elements[5] >> 4) & 0xFF) as u8;

        result[9] = (v.elements[6] & 0xFF) as u8;
        result[10] = ((v.elements[6] >> 8) | ((v.elements[7] & 0x0F) << 4)) as u8;
        result[11] = ((v.elements[7] >> 4) & 0xFF) as u8;

        result
    }

    #[inline(always)]
    fn serialize_10(v: PortableVector) -> [u8; 10] {
        let mut result = [0u8; 10];

        result[0] = (v.elements[0] & 0xFF) as u8;
        result[1] = ((v.elements[1] & 0x3F) as u8) << 2 | ((v.elements[0] >> 8) & 0x03) as u8;
        result[2] = ((v.elements[2] & 0x0F) as u8) << 4 | ((v.elements[1] >> 6) & 0x0F) as u8;
        result[3] = ((v.elements[3] & 0x03) as u8) << 6 | ((v.elements[2] >> 4) & 0x3F) as u8;
        result[4] = ((v.elements[3] >> 2) & 0xFF) as u8;

        result[5] = (v.elements[4] & 0xFF) as u8;
        result[6] = ((v.elements[5] & 0x3F) as u8) << 2 | ((v.elements[4] >> 8) & 0x03) as u8;
        result[7] = ((v.elements[6] & 0x0F) as u8) << 4 | ((v.elements[5] >> 6) & 0x0F) as u8;
        result[8] = ((v.elements[7] & 0x03) as u8) << 6 | ((v.elements[6] >> 4) & 0x3F) as u8;
        result[9] = ((v.elements[7] >> 2) & 0xFF) as u8;

        result
    }

    #[inline(always)]
    fn serialize_5(v: PortableVector) -> [u8; 5] {
        let mut result = [0u8; 5];

        result[0] = ((v.elements[1] & 0x7) << 5 | v.elements[0]) as u8;
        result[1] =
            (((v.elements[3] & 1) << 7) | (v.elements[2] << 2) | (v.elements[1] >> 3)) as u8;
        result[2] = (((v.elements[4] & 0xF) << 4) | (v.elements[3] >> 1)) as u8;
        result[3] =
            (((v.elements[6] & 0x3) << 6) | (v.elements[5] << 1) | (v.elements[4] >> 4)) as u8;
        result[4] = ((v.elements[7] << 3) | (v.elements[6] >> 2)) as u8;

        result
    }
}
