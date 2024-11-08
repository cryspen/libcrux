#[derive(Clone, Copy)]
pub struct AVX2SIMDUnit {
    pub(crate) coefficients: libcrux_intrinsics::avx2::Vec256,
}

impl From<libcrux_intrinsics::avx2::Vec256> for AVX2SIMDUnit {
    fn from(coefficients: libcrux_intrinsics::avx2::Vec256) -> Self {
        Self { coefficients }
    }
}

#[allow(non_snake_case)]
pub(crate) fn ZERO() -> AVX2SIMDUnit {
    libcrux_intrinsics::avx2::mm256_setzero_si256().into()
}

pub(crate) fn from_coefficient_array(coefficient_array: &[i32]) -> AVX2SIMDUnit {
    libcrux_intrinsics::avx2::mm256_loadu_si256_i32(coefficient_array).into()
}

pub(crate) fn to_coefficient_array(x: &AVX2SIMDUnit) -> [i32; 8] {
    let mut coefficient_array = [0i32; 8];
    libcrux_intrinsics::avx2::mm256_storeu_si256_i32(&mut coefficient_array, x.coefficients);
    coefficient_array
}
