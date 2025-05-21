use hax_lib::*;

type SIMDContent = [i32; COEFFICIENTS_IN_SIMD_UNIT];
// Avoiding a recursive bundle
const COEFFICIENTS_IN_SIMD_UNIT: usize = 8;

pub(crate) fn int_is_i32(i: Int) -> bool {
    i <= i32::MAX.to_int() && i >= i32::MIN.to_int()
}

pub(crate) fn add_pre(lhs: &SIMDContent, rhs: &SIMDContent) -> Prop {
    forall(|i: usize| {
        implies(
            i < COEFFICIENTS_IN_SIMD_UNIT,
            int_is_i32(lhs[i].to_int() + rhs[i].to_int()),
        )
    })
}

pub(crate) fn add_post(lhs: &SIMDContent, rhs: &SIMDContent, future_lhs: &SIMDContent) -> Prop {
    forall(|i: usize| {
        implies(
            i < COEFFICIENTS_IN_SIMD_UNIT,
            future_lhs[i].to_int() == (lhs[i].to_int() + rhs[i].to_int()),
        )
    })
}

pub(crate) fn sub_pre(lhs: &SIMDContent, rhs: &SIMDContent) -> Prop {
    forall(|i: usize| {
        implies(
            i < COEFFICIENTS_IN_SIMD_UNIT,
            int_is_i32(lhs[i].to_int() - rhs[i].to_int()),
        )
    })
}

pub(crate) fn sub_post(lhs: &SIMDContent, rhs: &SIMDContent, future_lhs: &SIMDContent) -> Prop {
    forall(|i: usize| {
        implies(
            i < COEFFICIENTS_IN_SIMD_UNIT,
            future_lhs[i].to_int() == (lhs[i].to_int() - rhs[i].to_int()),
        )
    })
}
