use crate::constants::{Eta, Gamma2};

/// Specs for the proofs
#[cfg(hax)]
pub(crate) mod specs;

// Each field element occupies 32 bits and the size of a simd_unit is 256 bits.
pub(crate) const COEFFICIENTS_IN_SIMD_UNIT: usize = 8;

// Note: For proofs, it is better to use concrete constants instead of const expressions
//COEFFICIENTS_IN_RING_ELEMENT / COEFFICIENTS_IN_SIMD_UNIT;
pub(crate) const SIMD_UNITS_IN_RING_ELEMENT: usize = 32;

pub const FIELD_MODULUS: i32 = 8_380_417;

// FIELD_MODULUS^{-1} mod MONTGOMERY_R
pub const INVERSE_OF_MODULUS_MOD_MONTGOMERY_R: u64 = 58_728_449;

/// If 'x' denotes a value of type `fe`, values having this type hold a
/// representative y ≡ x·MONTGOMERY_R (mod FIELD_MODULUS).
/// We use 'fer' as a shorthand for this type.
pub(crate) type FieldElementTimesMontgomeryR = i32;

#[cfg(hax)]
#[hax_lib::attributes]
pub(crate) trait Repr: Copy + Clone {
    #[cfg(hax)]
    #[requires(true)]
    fn repr(&self) -> [i32; COEFFICIENTS_IN_SIMD_UNIT];
}

#[cfg(not(hax))]
pub trait Repr {}

#[hax_lib::attributes]
pub(crate) trait Operations: Copy + Clone + Repr {
    #[hax_lib::requires(true)]
    #[hax_lib::ensures(|result| specs::zero_post(&result.repr()))]
    fn zero() -> Self;

    #[hax_lib::requires(specs::from_coefficient_array_pre(array, &out.repr()))]
    #[hax_lib::ensures(|_| specs::from_coefficient_array_post(array, &out.repr(), &future(out).repr()))]
    fn from_coefficient_array(array: &[i32], out: &mut Self);

    #[hax_lib::requires(specs::to_coefficient_array_pre(&value.repr(), out))]
    #[hax_lib::ensures(|_| specs::to_coefficient_array_post(&value.repr(), out, &future(out)))]
    fn to_coefficient_array(value: &Self, out: &mut [i32]);

    // Arithmetic
    #[hax_lib::requires(specs::add_pre(&lhs.repr(), &rhs.repr()))]
    #[hax_lib::ensures(|_| specs::add_post(&lhs.repr(), &rhs.repr(), &future(lhs).repr()))]
    fn add(lhs: &mut Self, rhs: &Self);

    #[hax_lib::requires(specs::subtract_pre(&lhs.repr(), &rhs.repr()))]
    #[hax_lib::ensures(|_| specs::subtract_post(&lhs.repr(), &rhs.repr(), &future(lhs).repr()))]
    fn subtract(lhs: &mut Self, rhs: &Self);

    #[hax_lib::requires(specs::infinity_norm_exceeds_pre(&simd_unit.repr(), bound))]
    #[hax_lib::ensures(|result| specs::infinity_norm_exceeds_post(&simd_unit.repr(), bound, result))]
    fn infinity_norm_exceeds(simd_unit: &Self, bound: i32) -> bool;

    #[hax_lib::requires(specs::decompose_pre(gamma2, &simd_unit.repr(), &low.repr(), &high.repr()))]
    #[hax_lib::ensures(|_| specs::decompose_post(gamma2, &simd_unit.repr(), &low.repr(), &high.repr(), &future(low).repr(), &future(high).repr()))]
    fn decompose(gamma2: Gamma2, simd_unit: &Self, low: &mut Self, high: &mut Self);

    #[hax_lib::requires(specs::compute_hint_pre(&low.repr(), &high.repr(), gamma2, &hint.repr()))]
    #[hax_lib::ensures(|result| specs::compute_hint_post(&low.repr(), &high.repr(), gamma2, &hint.repr(), &future(hint).repr(), result))]
    fn compute_hint(low: &Self, high: &Self, gamma2: i32, hint: &mut Self) -> usize;

    #[hax_lib::requires(specs::use_hint_pre(gamma2, &simd_unit.repr(), &hint.repr()))]
    #[hax_lib::ensures(|_| specs::use_hint_post(gamma2, &simd_unit.repr(), &hint.repr(), &future(hint).repr()))]
    fn use_hint(gamma2: Gamma2, simd_unit: &Self, hint: &mut Self);

    // Modular operations
    #[hax_lib::requires(specs::montgomery_multiply_pre(&lhs.repr(), &rhs.repr()))]
    #[hax_lib::ensures(|_| specs::montgomery_multiply_post(&lhs.repr(), &rhs.repr(), &future(lhs).repr()))]
    fn montgomery_multiply(lhs: &mut Self, rhs: &Self);

    // 261631 is the largest x such that x * pow2 13 <= 2143289343 (the barrett reduce input bound)
    #[hax_lib::requires(specs::shift_left_then_reduce_pre::<SHIFT_BY>(&simd_unit.repr()))]
    #[hax_lib::ensures(|_| specs::shift_left_then_reduce_post::<SHIFT_BY>(&simd_unit.repr(), &future(simd_unit).repr()))]
    fn shift_left_then_reduce<const SHIFT_BY: i32>(simd_unit: &mut Self);

    // Decomposition operations
    #[hax_lib::requires(specs::power2round_pre(&t0.repr(), &t1.repr()))]
    #[hax_lib::ensures(|_| specs::power2round_post(&t0.repr(), &t1.repr(), &future(t0).repr(), &future(t1).repr()))]
    fn power2round(t0: &mut Self, t1: &mut Self);

    // Sampling
    //
    // In the sampling functions, since each SIMD unit can hold 8 coefficients,
    // we expect that `out` has the capacity for up to 8 coefficients.

    // Since each coefficient could potentially be sampled with 3 bytes, we expect
    // `randomness` to hold 24 bytes.
    #[hax_lib::requires(specs::rejection_sample_less_than_field_modulus_pre(randomness, out))]
    #[hax_lib::ensures(|result| specs::rejection_sample_less_than_field_modulus_post(randomness, out, result))]
    fn rejection_sample_less_than_field_modulus(randomness: &[u8], out: &mut [i32]) -> usize;

    // Since each coefficient could potentially be sampled with half a byte,
    // we expect `randomness` to hold 4 bytes.
    #[hax_lib::requires(true)]
    fn rejection_sample_less_than_eta_equals_2(randomness: &[u8], out: &mut [i32]) -> usize;

    #[hax_lib::requires(true)]
    fn rejection_sample_less_than_eta_equals_4(randomness: &[u8], out: &mut [i32]) -> usize;

    // Encoding operations

    // Gamma1
    #[hax_lib::requires(true)]
    fn gamma1_serialize(simd_unit: &Self, serialized: &mut [u8], gamma1_exponent: usize);
    #[hax_lib::requires(true)]
    fn gamma1_deserialize(serialized: &[u8], out: &mut Self, gamma1_exponent: usize);

    // Commitment
    #[hax_lib::requires(serialized.len() == 4 || serialized.len() == 6)]
    #[hax_lib::ensures(|_| future(serialized).len() == serialized.len())]
    fn commitment_serialize(simd_unit: &Self, serialized: &mut [u8]);

    // Error
    #[hax_lib::requires(true)]
    fn error_serialize(eta: Eta, simd_unit: &Self, serialized: &mut [u8]);
    #[hax_lib::requires(true)]
    fn error_deserialize(eta: Eta, serialized: &[u8], out: &mut Self);

    // t0
    #[hax_lib::requires(true)]
    fn t0_serialize(simd_unit: &Self, out: &mut [u8]); // out len 13
    #[hax_lib::requires(true)]
    fn t0_deserialize(serialized: &[u8], out: &mut Self);

    // t1
    #[hax_lib::requires(true)]
    fn t1_serialize(simd_unit: &Self, out: &mut [u8]); // out len 10
    #[hax_lib::requires(true)]
    fn t1_deserialize(serialized: &[u8], out: &mut Self);

    // NTT
    #[hax_lib::requires(fstar!(r#"
        (forall (i:nat). i < 32 ==>
            Spec.Utils.is_i32b_array_opaque
            (v ${specs::NTT_BASE_BOUND})
            (f_repr (Seq.index ${simd_units} i)))
    "#))]
    #[hax_lib::ensures(|_| fstar!(r#"
        (forall (i:nat). i < 32 ==> Spec.Utils.is_i32b_array_opaque (v ${specs::FIELD_MAX})
            (f_repr (Seq.index ${simd_units}_future i)))
    "#))]
    fn ntt(simd_units: &mut [Self; SIMD_UNITS_IN_RING_ELEMENT]);

    // invert NTT and convert to standard domain
    #[hax_lib::requires(fstar!(r#"
        (forall (i:nat). i < 32 ==> Spec.Utils.is_i32b_array_opaque (v ${specs::FIELD_MAX})
            (f_repr (Seq.index ${simd_units} i)))
    "#))]
    #[hax_lib::ensures(|_| fstar!(r#"
        (forall (i:nat). i < 32 ==> Spec.Utils.is_i32b_array_opaque (v ${specs::FIELD_MAX})
            (f_repr (Seq.index ${simd_units}_future i)))
    "#))]
    fn invert_ntt_montgomery(simd_units: &mut [Self; SIMD_UNITS_IN_RING_ELEMENT]);

    // Barrett reduce all coefficients
    fn reduce(simd_units: &mut [Self; SIMD_UNITS_IN_RING_ELEMENT]);
}
