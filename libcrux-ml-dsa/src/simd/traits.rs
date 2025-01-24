use crate::constants::{Eta, Gamma2};
use hax_lib::int::*;

// Each field element occupies 32 bits and the size of a simd_unit is 256 bits.
pub(crate) const COEFFICIENTS_IN_SIMD_UNIT: usize = 8;

pub(crate) const SIMD_UNITS_IN_RING_ELEMENT: usize =
    crate::constants::COEFFICIENTS_IN_RING_ELEMENT / COEFFICIENTS_IN_SIMD_UNIT;

pub const FIELD_MODULUS: i32 = 8_380_417;

// FIELD_MODULUS^{-1} mod MONTGOMERY_R
pub const INVERSE_OF_MODULUS_MOD_MONTGOMERY_R: u64 = 58_728_449;

/// If 'x' denotes a value of type `fe`, values having this type hold a
/// representative y ≡ x·MONTGOMERY_R (mod FIELD_MODULUS).
/// We use 'fer' as a shorthand for this type.
pub(crate) type FieldElementTimesMontgomeryR = i32;

type SIMDContent = [i32; COEFFICIENTS_IN_SIMD_UNIT];

#[hax_lib::attributes]
pub(crate) trait Repr: Copy + Clone {
    #[requires(true)]
    fn repr(&self) -> SIMDContent;
}

fn int_in_i32_range(i:hax_lib::int::Int) -> bool {
    i <= i32::MAX.lift() && i >= i32::MIN.lift()
}

#[cfg(not(eurydice))]
#[hax_lib::attributes]
pub(crate) trait Operations: Copy + Clone + Repr {
    #[hax_lib::ensures(|result| result.repr() == [0i32; COEFFICIENTS_IN_SIMD_UNIT])]
    fn zero() -> Self;

    #[hax_lib::requires(array.len() == COEFFICIENTS_IN_SIMD_UNIT)]
    #[hax_lib::ensures(|result| future(out).repr() == array)]
    fn from_coefficient_array(array: &[i32], out: &mut Self);

    #[hax_lib::requires(out.len() == COEFFICIENTS_IN_SIMD_UNIT)]
    #[hax_lib::ensures(|result| future(out) == value.repr())]
    fn to_coefficient_array(value: &Self, out: &mut [i32]);

    // Arithmetic
    #[hax_lib::requires(hax_lib::forall(|i:usize| hax_lib::implies(i < COEFFICIENTS_IN_SIMD_UNIT, || int_in_i32_range (lhs.repr()[i].lift() + rhs.repr()[i].lift()))))]
    #[hax_lib::ensures(|_| hax_lib::forall(|i:usize| hax_lib::implies(i < COEFFICIENTS_IN_SIMD_UNIT, || future(lhs).repr()[i].lift() == (lhs.repr()[i].lift() + rhs.repr()[i].lift()))))]
    fn add(lhs: &mut Self, rhs: &Self);
    
    #[hax_lib::requires(hax_lib::forall(|i:usize| hax_lib::implies(i < COEFFICIENTS_IN_SIMD_UNIT, || int_in_i32_range (lhs.repr()[i].lift() - rhs.repr()[i].lift()))))]
    #[hax_lib::ensures(|_| hax_lib::forall(|i:usize| hax_lib::implies(i < COEFFICIENTS_IN_SIMD_UNIT, || future(lhs).repr()[i].lift() == (lhs.repr()[i].lift() - rhs.repr()[i].lift()))))]
    fn subtract(lhs: &mut Self, rhs: &Self);
    
    fn infinity_norm_exceeds(simd_unit: &Self, bound: i32) -> bool;
    fn decompose(gamma2: Gamma2, simd_unit: &Self, low: &mut Self, high: &mut Self);
    fn compute_hint(low: &Self, high: &Self, gamma2: i32, hint: &mut Self) -> usize;
    fn use_hint(gamma2: Gamma2, simd_unit: &Self, hint: &mut Self);

    // Modular operations
    fn montgomery_multiply(lhs: &mut Self, rhs: &Self);
    fn shift_left_then_reduce<const SHIFT_BY: i32>(simd_unit: &mut Self);

    // Decomposition operations
    fn power2round(t0: &mut Self, t1: &mut Self);

    // Sampling
    //
    // In the sampling functions, since each SIMD unit can hold 8 coefficients,
    // we expect that `out` has the capacity for up to 8 coefficients.

    // Since each coefficient could potentially be sampled with 3 bytes, we expect
    // `randomness` to hold 24 bytes.
    fn rejection_sample_less_than_field_modulus(randomness: &[u8], out: &mut [i32]) -> usize;

    // Since each coefficient could potentially be sampled with half a byte,
    // we expect `randomness` to hold 4 bytes.
    fn rejection_sample_less_than_eta_equals_2(randomness: &[u8], out: &mut [i32]) -> usize;
    fn rejection_sample_less_than_eta_equals_4(randomness: &[u8], out: &mut [i32]) -> usize;

    // Encoding operations

    // Gamma1
    fn gamma1_serialize(simd_unit: &Self, serialized: &mut [u8], gamma1_exponent: usize);
    fn gamma1_deserialize(serialized: &[u8], out: &mut Self, gamma1_exponent: usize);

    // Commitment
    fn commitment_serialize(simd_unit: &Self, serialized: &mut [u8]);

    // Error
    fn error_serialize(eta: Eta, simd_unit: &Self, serialized: &mut [u8]);
    fn error_deserialize(eta: Eta, serialized: &[u8], out: &mut Self);

    // t0
    fn t0_serialize(simd_unit: &Self, out: &mut [u8]); // out len 13
    fn t0_deserialize(serialized: &[u8], out: &mut Self);

    // t1
    fn t1_serialize(simd_unit: &Self, out: &mut [u8]); // out len 10
    fn t1_deserialize(serialized: &[u8], out: &mut Self);

    // NTT
    fn ntt(simd_units: &mut [Self; SIMD_UNITS_IN_RING_ELEMENT]);

    // invert NTT and convert to standard domain
    fn invert_ntt_montgomery(simd_units: &mut [Self; SIMD_UNITS_IN_RING_ELEMENT]);
}

#[cfg(eurydice)]
pub(crate) trait Operations: Copy + Clone + Repr {
    fn zero() -> Self;

    fn from_coefficient_array(array: &[i32], out: &mut Self);
    fn to_coefficient_array(value: &Self, out: &mut [i32]);

    // Arithmetic
    fn add(lhs: &mut Self, rhs: &Self);
    fn subtract(lhs: &mut Self, rhs: &Self);
    fn infinity_norm_exceeds(simd_unit: &Self, bound: i32) -> bool;
    fn decompose(gamma2: Gamma2, simd_unit: &Self, low: &mut Self, high: &mut Self);
    fn compute_hint(low: &Self, high: &Self, gamma2: i32, hint: &mut Self) -> usize;
    fn use_hint(gamma2: Gamma2, simd_unit: &Self, hint: &mut Self);

    // Modular operations
    fn montgomery_multiply(lhs: &mut Self, rhs: &Self);
    fn shift_left_then_reduce<const SHIFT_BY: i32>(simd_unit: &mut Self);

    // Decomposition operations
    fn power2round(t0: &mut Self, t1: &mut Self);

    // Sampling
    //
    // In the sampling functions, since each SIMD unit can hold 8 coefficients,
    // we expect that `out` has the capacity for up to 8 coefficients.

    // Since each coefficient could potentially be sampled with 3 bytes, we expect
    // `randomness` to hold 24 bytes.
    fn rejection_sample_less_than_field_modulus(randomness: &[u8], out: &mut [i32]) -> usize;

    // Since each coefficient could potentially be sampled with half a byte,
    // we expect `randomness` to hold 4 bytes.
    fn rejection_sample_less_than_eta_equals_2(randomness: &[u8], out: &mut [i32]) -> usize;
    fn rejection_sample_less_than_eta_equals_4(randomness: &[u8], out: &mut [i32]) -> usize;

    // Encoding operations

    // Gamma1
    fn gamma1_serialize(simd_unit: &Self, serialized: &mut [u8], gamma1_exponent: usize);
    fn gamma1_deserialize(serialized: &[u8], out: &mut Self, gamma1_exponent: usize);

    // Commitment
    fn commitment_serialize(simd_unit: &Self, serialized: &mut [u8]);

    // Error
    fn error_serialize(eta: Eta, simd_unit: &Self, serialized: &mut [u8]);
    fn error_deserialize(eta: Eta, serialized: &[u8], out: &mut Self);

    // t0
    fn t0_serialize(simd_unit: &Self, out: &mut [u8]); // out len 13
    fn t0_deserialize(serialized: &[u8], out: &mut Self);

    // t1
    fn t1_serialize(simd_unit: &Self, out: &mut [u8]); // out len 10
    fn t1_deserialize(serialized: &[u8], out: &mut Self);

    // NTT
    fn ntt(simd_units: &mut [Self; SIMD_UNITS_IN_RING_ELEMENT]);

    // invert NTT and convert to standard domain
    fn invert_ntt_montgomery(simd_units: &mut [Self; SIMD_UNITS_IN_RING_ELEMENT]);
}
