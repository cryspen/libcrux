//! AVX2 implementation of the operations trait for vector operations in libcrux

mod intrinsics;
pub(crate) use intrinsics::*;

pub mod sha3;
pub mod ml_kem;

#[derive(Clone, Copy)]
pub struct SIMD256Vector {
    elements: Vec256,
}

#[inline(always)]
fn zero() -> SIMD256Vector {
    SIMD256Vector {
        elements: mm256_setzero_si256(),
    }
}

#[inline(always)]
fn to_i16_array(v: SIMD256Vector) -> [i16; 16] {
    let mut output = [0i16; 16];
    mm256_storeu_si256_i16(&mut output, v.elements);

    output
}

#[inline(always)]
fn from_i16_array(array: &[i16]) -> SIMD256Vector {
    SIMD256Vector {
        elements: mm256_loadu_si256_i16(array),
    }
}

