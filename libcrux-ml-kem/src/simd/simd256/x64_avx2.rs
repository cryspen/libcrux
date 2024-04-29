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
pub(super) fn load_vec(array: [i32; 8]) -> Vec {
    unsafe { _mm256_loadu_si256(array.as_ptr() as *const __m256i) }
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
