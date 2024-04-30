use core::arch::x86_64::*;

pub(super) type Vec = __m256i;

#[inline(always)]
pub(super) fn zero() -> Vec {
    unsafe { _mm256_setzero_si256() }
}

#[inline(always)]
pub(super) fn store(v: Vec) -> [i32; 8] {
    let mut out = [0i32; 8];

    unsafe {
        _mm256_storeu_si256(out.as_mut_ptr() as *mut __m256i, v);
    }

    out
}

#[inline(always)]
pub(super) fn storei16<const INDEX: i32>(v: Vec) -> i32 {
    unsafe { _mm256_extract_epi16::<INDEX>(v) }
}

#[inline(always)]
pub(super) fn load_vec(array: [i32; 8]) -> Vec {
    unsafe { _mm256_loadu_si256(array.as_ptr() as *const __m256i) }
}

#[inline(always)]
pub(super) fn load_i32s(
    e0: i32,
    e1: i32,
    e2: i32,
    e3: i32,
    e4: i32,
    e5: i32,
    e6: i32,
    e7: i32,
) -> Vec {
    unsafe { _mm256_set_epi32(e0, e1, e2, e3, e4, e5, e6, e7) }
}

#[inline(always)]
pub(super) fn load_i8s(
    e00: i8,
    e01: i8,
    e02: i8,
    e03: i8,
    e04: i8,
    e05: i8,
    e06: i8,
    e07: i8,
    e08: i8,
    e09: i8,
    e10: i8,
    e11: i8,
    e12: i8,
    e13: i8,
    e14: i8,
    e15: i8,
    e16: i8,
    e17: i8,
    e18: i8,
    e19: i8,
    e20: i8,
    e21: i8,
    e22: i8,
    e23: i8,
    e24: i8,
    e25: i8,
    e26: i8,
    e27: i8,
    e28: i8,
    e29: i8,
    e30: i8,
    e31: i8,
) -> Vec {
    unsafe {
        _mm256_set_epi8(
            e00, e01, e02, e03, e04, e05, e06, e07, e08, e09, e10, e11, e12, e13, e14, e15, e16,
            e17, e18, e19, e20, e21, e22, e23, e24, e25, e26, e27, e28, e29, e30, e31,
        )
    }
}

#[inline(always)]
pub(super) fn load(v: i32) -> Vec {
    unsafe { _mm256_set1_epi32(v) }
}

#[inline(always)]
pub(super) fn add(a: Vec, b: Vec) -> Vec {
    unsafe { _mm256_add_epi32(a, b) }
}

#[inline(always)]
pub(super) fn sub(a: Vec, b: Vec) -> Vec {
    unsafe { _mm256_sub_epi32(a, b) }
}

#[inline(always)]
pub(super) fn mul(a: Vec, b: Vec) -> Vec {
    unsafe { _mm256_mullo_epi32(a, b) }
}

#[inline(always)]
pub(super) fn and(a: Vec, b: Vec) -> Vec {
    unsafe { _mm256_and_si256(a, b) }
}

/// Signed shift
#[inline(always)]
pub(super) fn shr<const SHIFT_BY: i32>(a: Vec) -> Vec {
    unsafe { _mm256_srai_epi32::<SHIFT_BY>(a) }
}

/// Shifting in 0
#[inline(always)]
pub(super) fn shrli<const SHIFT_BY: i32>(a: Vec) -> Vec {
    unsafe { _mm256_srli_epi32::<SHIFT_BY>(a) }
}

/// Shifting in 0
#[inline(always)]
pub(super) fn shrli16<const SHIFT_BY: i32>(a: Vec) -> Vec {
    unsafe { _mm256_srli_epi16::<SHIFT_BY>(a) }
}

/// Shifting in 0
#[inline(always)]
pub(super) fn shrllv(a: Vec, count: Vec) -> Vec {
    unsafe { _mm256_srlv_epi32(a, count) }
}

/// Shifting in 0
#[inline(always)]
pub(super) fn shlli<const SHIFT_BY: i32>(a: Vec) -> Vec {
    unsafe { _mm256_slli_epi32::<SHIFT_BY>(a) }
}

/// Shifting in 0
#[inline(always)]
pub(super) fn shllv(a: Vec, count: Vec) -> Vec {
    unsafe { _mm256_sllv_epi32(a, count) }
}

#[inline(always)]
pub(super) fn xor(a: Vec, b: Vec) -> Vec {
    unsafe { _mm256_xor_si256(a, b) }
}

#[inline(always)]
pub(super) fn shuffle(a: Vec, b: Vec) -> Vec {
    unsafe { _mm256_shuffle_epi8(a, b) }
}
