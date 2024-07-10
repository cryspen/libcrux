use crate::simd::traits::Operations;

mod arithmetic;
mod ntt;
mod simd_unit_type;

pub(crate) use simd_unit_type::PortableSIMDUnit;

impl Operations for PortableSIMDUnit {
    fn ZERO() -> Self {
        simd_unit_type::ZERO()
    }

    fn from_i32_array(array: &[i32]) -> Self {
        simd_unit_type::from_i32_array(array)
    }

    fn to_i32_array(simd_unit: Self) -> [i32; 8] {
        simd_unit_type::to_i32_array(simd_unit)
    }

    fn add(lhs: &Self, rhs: &Self) -> Self {
        arithmetic::add(lhs, rhs)
    }

    fn subtract(lhs: &Self, rhs: &Self) -> Self {
        arithmetic::subtract(lhs, rhs)
    }

    fn montgomery_multiply_by_constant(simd_unit: Self, c: i32) -> Self {
        arithmetic::montgomery_multiply_by_constant(simd_unit, c)
    }
    fn montgomery_multiply(lhs: Self, rhs: Self) -> Self {
        arithmetic::montgomery_multiply(&lhs, &rhs)
    }

    fn power2round(simd_unit: Self) -> (Self, Self) {
        arithmetic::power2round(simd_unit)
    }

    fn infinity_norm_exceeds(simd_unit: Self, bound: i32) -> bool {
        arithmetic::infinity_norm_exceeds(simd_unit, bound)
    }

    fn ntt_at_layer_0(simd_unit: Self, zeta0: i32, zeta1: i32, zeta2: i32, zeta3: i32) -> Self {
        ntt::ntt_at_layer_0(simd_unit, zeta0, zeta1, zeta2, zeta3)
    }
    fn ntt_at_layer_1(simd_unit: Self, zeta0: i32, zeta1: i32) -> Self {
        ntt::ntt_at_layer_1(simd_unit, zeta0, zeta1)
    }
    fn ntt_at_layer_2(simd_unit: Self, zeta: i32) -> Self {
        ntt::ntt_at_layer_2(simd_unit, zeta)
    }

    fn invert_ntt_at_layer_0(
        simd_unit: Self,
        zeta0: i32,
        zeta1: i32,
        zeta2: i32,
        zeta3: i32,
    ) -> Self {
        ntt::invert_ntt_at_layer_0(simd_unit, zeta0, zeta1, zeta2, zeta3)
    }
    fn invert_ntt_at_layer_1(simd_unit: Self, zeta0: i32, zeta1: i32) -> Self {
        ntt::invert_ntt_at_layer_1(simd_unit, zeta0, zeta1)
    }
    fn invert_ntt_at_layer_2(simd_unit: Self, zeta: i32) -> Self {
        ntt::invert_ntt_at_layer_2(simd_unit, zeta)
    }
}