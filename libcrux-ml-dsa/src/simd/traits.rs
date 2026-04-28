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
    #[hax_lib::ensures(|result| result.repr() == [0i32; COEFFICIENTS_IN_SIMD_UNIT])]
    fn zero() -> Self;

    #[hax_lib::requires(array.len() == COEFFICIENTS_IN_SIMD_UNIT)]
    #[hax_lib::ensures(|result| future(out).repr() == array)]
    fn from_coefficient_array(array: &[i32], out: &mut Self);

    #[hax_lib::requires(out.len() == COEFFICIENTS_IN_SIMD_UNIT)]
    #[hax_lib::ensures(|result| future(out) == value.repr())]
    fn to_coefficient_array(value: &Self, out: &mut [i32]);

    // Arithmetic
    #[hax_lib::requires(specs::add_pre(&lhs.repr(), &rhs.repr()))]
    #[hax_lib::ensures(|_| specs::add_post(&lhs.repr(), &rhs.repr(), &future(lhs).repr()))]
    fn add(lhs: &mut Self, rhs: &Self);

    #[hax_lib::requires(specs::sub_pre(&lhs.repr(), &rhs.repr()))]
    #[hax_lib::ensures(|_| specs::sub_post(&lhs.repr(), &rhs.repr(), &future(lhs).repr()))]
    fn subtract(lhs: &mut Self, rhs: &Self);

    #[hax_lib::requires(fstar!(r#"v $bound > 0 /\
        Spec.Utils.is_i32b_array_opaque (v ${specs::FIELD_MAX}) (f_repr ${simd_unit})"#))]
    #[hax_lib::ensures(|result| fstar!(r#"
        Libcrux_ml_dsa.Simd.Traits.Specs.infinity_norm_exceeds_post
            (f_repr ${simd_unit}) $bound $result"#))]
    fn infinity_norm_exceeds(simd_unit: &Self, bound: i32) -> bool;

    #[hax_lib::requires(fstar!(r#"
        (v $gamma2 == v ${crate::constants::GAMMA2_V261_888} \/
         v $gamma2 == v ${crate::constants::GAMMA2_V95_232}) /\
        Spec.Utils.is_i32b_array_opaque (v ${specs::FIELD_MAX}) (f_repr ${simd_unit})"#))]
    #[hax_lib::ensures(|_| fstar!(r#"
        ((v $gamma2 == v ${crate::constants::GAMMA2_V95_232} ==>
            Spec.Utils.is_i32b_array_opaque 95232 (f_repr ${low}_future) /\
            Spec.Utils.is_i32b_array_opaque 44 (f_repr ${high}_future)) /\
         (v $gamma2 == v ${crate::constants::GAMMA2_V261_888} ==>
            Spec.Utils.is_i32b_array_opaque 261888 (f_repr ${low}_future) /\
            Spec.Utils.is_i32b_array_opaque 16 (f_repr ${high}_future))) /\
        Spec.Utils.forall8 (fun (i: nat{i < 8}) ->
          Libcrux_ml_dsa.Simd.Traits.Specs.decompose_lane_post
            $gamma2
            (Seq.index (f_repr ${simd_unit}) i)
            (Seq.index (f_repr ${low}_future) i)
            (Seq.index (f_repr ${high}_future) i))"#))]
    fn decompose(gamma2: Gamma2, simd_unit: &Self, low: &mut Self, high: &mut Self);

    #[hax_lib::requires(fstar!(r#"
        (v $gamma2 == v ${crate::constants::GAMMA2_V261_888} \/
         v $gamma2 == v ${crate::constants::GAMMA2_V95_232}) /\
        Spec.Utils.is_i32b_array_opaque (v ${specs::FIELD_MAX}) (f_repr ${low}) /\
        Spec.Utils.is_i32b_array_opaque (v ${specs::FIELD_MAX}) (f_repr ${high})"#))]
    #[hax_lib::ensures(|result| fstar!(r#"v $result <= 8 /\
        Libcrux_ml_dsa.Simd.Traits.Specs.is_binary_array_8_opaque
          (f_repr ${hint}_future) /\
        Spec.Utils.forall8 (fun (i: nat{i < 8}) ->
          Libcrux_ml_dsa.Simd.Traits.Specs.compute_hint_lane_post
            $gamma2
            (Seq.index (f_repr ${low}) i)
            (Seq.index (f_repr ${high}) i)
            (Seq.index (f_repr ${hint}_future) i))"#))]
    fn compute_hint(low: &Self, high: &Self, gamma2: i32, hint: &mut Self) -> usize;

    #[hax_lib::requires(fstar!(r#"
        (v $gamma2 == v ${crate::constants::GAMMA2_V261_888} \/
         v $gamma2 == v ${crate::constants::GAMMA2_V95_232}) /\
        Spec.Utils.is_i32b_array_opaque (v ${specs::FIELD_MAX}) (f_repr ${simd_unit}) /\
        Libcrux_ml_dsa.Simd.Traits.Specs.is_binary_array_8_opaque (f_repr ${hint})"#))]
    #[hax_lib::ensures(|_| fstar!(r#"
        ((v $gamma2 == v ${crate::constants::GAMMA2_V95_232} ==>
            Spec.Utils.is_i32b_array_opaque 44 (f_repr ${hint}_future)) /\
         (v $gamma2 == v ${crate::constants::GAMMA2_V261_888} ==>
            Spec.Utils.is_i32b_array_opaque 16 (f_repr ${hint}_future))) /\
        Spec.Utils.forall8 (fun (i: nat{i < 8}) ->
          Libcrux_ml_dsa.Simd.Traits.Specs.use_hint_lane_post
            $gamma2
            (Seq.index (f_repr ${simd_unit}) i)
            (Seq.index (f_repr ${hint}) i)
            (Seq.index (f_repr ${hint}_future) i))"#))]
    fn use_hint(gamma2: Gamma2, simd_unit: &Self, hint: &mut Self);

    // Modular operations
    #[hax_lib::requires(fstar!(r#"
        Spec.Utils.is_i32b_array_opaque (v ${specs::FIELD_MAX}) (${rhs.repr()})"#))]
    #[hax_lib::ensures(|result| fstar!(r#"
        Spec.Utils.is_i32b_array_opaque (v ${specs::FIELD_MAX}) (f_repr ${lhs}_future) /\
        Spec.MLDSA.Math.(forall i. i < 8 ==>
            mod_q (v (Seq.index (f_repr ${lhs}_future) i)) ==
            mod_q (v (Seq.index (${lhs.repr()}) i) * v (Seq.index (${rhs.repr()}) i) * 8265825)) /\
        Spec.Utils.forall8 (fun (i: nat{i < 8}) ->
          Libcrux_ml_dsa.Simd.Traits.Specs.montgomery_multiply_lane_post
            (Seq.index (${lhs.repr()}) i)
            (Seq.index (${rhs.repr()}) i)
            (Seq.index (f_repr ${lhs}_future) i))"#))]
    fn montgomery_multiply(lhs: &mut Self, rhs: &Self);

    // 261631 is the largest x such that x * pow2 13 <= 2143289343 (the barrett reduce input bound)
    #[hax_lib::requires(fstar!(r#"v $SHIFT_BY == 13 /\
        (forall i. i < 8 ==> v (Seq.index (f_repr ${simd_unit}) i) >= 0 /\
            v (Seq.index (f_repr ${simd_unit}) i) <= 261631)"#))]
    #[hax_lib::ensures(|_| fstar!(r#"
        Spec.Utils.forall8 (fun (i: nat{i < 8}) ->
          Libcrux_ml_dsa.Simd.Traits.Specs.shift_left_then_reduce_lane_post
            (Seq.index (f_repr ${simd_unit}) i)
            (Seq.index (f_repr ${simd_unit}_future) i))"#))]
    fn shift_left_then_reduce<const SHIFT_BY: i32>(simd_unit: &mut Self);

    // Decomposition operations
    #[hax_lib::requires(fstar!(r#"
        Spec.Utils.is_i32b_array_opaque (v ${specs::FIELD_MAX}) (f_repr ${t0})"#))]
    #[hax_lib::ensures(|_| fstar!(r#"
        Spec.Utils.is_i32b_array_opaque (pow2 12) (f_repr ${t0}_future) /\
        Spec.Utils.forall8 (fun (i: nat{i < 8}) ->
          v (Seq.index (f_repr ${t1}_future) i) >= 0 /\
          v (Seq.index (f_repr ${t1}_future) i) < pow2 10) /\
        Spec.Utils.forall8 (fun (i: nat{i < 8}) ->
          Libcrux_ml_dsa.Simd.Traits.Specs.power2round_lane_post
            (Seq.index (f_repr ${t0}) i)
            (Seq.index (f_repr ${t1}_future) i)
            (Seq.index (f_repr ${t0}_future) i))"#))]
    fn power2round(t0: &mut Self, t1: &mut Self);

    // Sampling
    //
    // In the sampling functions, since each SIMD unit can hold 8 coefficients,
    // we expect that `out` has the capacity for up to 8 coefficients.

    // Since each coefficient could potentially be sampled with 3 bytes, we expect
    // `randomness` to hold 24 bytes.
    #[hax_lib::requires(fstar!(r#"
        Seq.length $randomness / 3 <= 4294967295 /\
        Seq.length $randomness / 3 <= Seq.length $out"#))]
    #[hax_lib::ensures(|result| fstar!(r#"v $result <= 8 /\
        (forall (i:nat{i < Seq.length ${out}_future}). i < v $result ==>
          v (Seq.index ${out}_future i) >= 0 /\
          v (Seq.index ${out}_future i) < 8380417)"#))]
    fn rejection_sample_less_than_field_modulus(randomness: &[u8], out: &mut [i32]) -> usize;

    // Since each coefficient could potentially be sampled with half a byte,
    // we expect `randomness` to hold 4 bytes.
    #[hax_lib::requires(fstar!(r#"
        Seq.length $randomness * 2 <= 4294967295 /\
        Seq.length $randomness * 2 <= Seq.length $out"#))]
    #[hax_lib::ensures(|result| fstar!(r#"v $result <= 8 /\
        (forall (i:nat{i < Seq.length ${out}_future}). i < v $result ==>
          v (Seq.index ${out}_future i) >= -2 /\ v (Seq.index ${out}_future i) <= 2)"#))]
    fn rejection_sample_less_than_eta_equals_2(randomness: &[u8], out: &mut [i32]) -> usize;

    #[hax_lib::requires(fstar!(r#"
        Seq.length $randomness * 2 <= 4294967295 /\
        Seq.length $randomness * 2 <= Seq.length $out"#))]
    #[hax_lib::ensures(|result| fstar!(r#"v $result <= 8 /\
        (forall (i:nat{i < Seq.length ${out}_future}). i < v $result ==>
          v (Seq.index ${out}_future i) >= -4 /\ v (Seq.index ${out}_future i) <= 4)"#))]
    fn rejection_sample_less_than_eta_equals_4(randomness: &[u8], out: &mut [i32]) -> usize;

    // Encoding operations

    // Gamma1: serialized length is 8 * (gamma1_exponent + 1) / 8 = gamma1_exponent + 1 bytes
    // per 8-coefficient SIMD unit, but with each coefficient using w = gamma1_exponent + 1 bits
    // (w in {18, 20}). For 8 lanes that's 18 or 20 bytes.
    // F-3 (2026-04-28): pre uses non-negative-bounded `is_pos_array_opaque`
    // since the impl operates on the shifted (non-negative) representation.
    #[hax_lib::requires(fstar!(r#"
        (v $gamma1_exponent == 17 \/ v $gamma1_exponent == 19) /\
        Seq.length $serialized == 1 + v $gamma1_exponent /\
        Libcrux_ml_dsa.Simd.Traits.Specs.is_pos_array_opaque (pow2 (v $gamma1_exponent))
            (f_repr ${simd_unit})"#))]
    #[hax_lib::ensures(|_| fstar!(r#"
        Seq.length ${serialized}_future == Seq.length ${serialized}"#))]
    fn gamma1_serialize(simd_unit: &Self, serialized: &mut [u8], gamma1_exponent: usize);
    #[hax_lib::requires(fstar!(r#"
        (v $gamma1_exponent == 17 \/ v $gamma1_exponent == 19) /\
        Seq.length $serialized == 1 + v $gamma1_exponent"#))]
    #[hax_lib::ensures(|_| fstar!(r#"
        Spec.Utils.is_i32b_array_opaque (pow2 (v $gamma1_exponent))
          (f_repr ${out}_future)"#))]
    fn gamma1_deserialize(serialized: &[u8], out: &mut Self, gamma1_exponent: usize);

    // Commitment: 4 bytes for gamma2 = 261888 (4-bit packing) or 6 for gamma2 = 95232 (6-bit).
    // F-3 (2026-04-28): pre uses non-negative-bounded `is_pos_array_opaque`
    // since commitment values are the high half of decompose, in [0, 16) or [0, 44).
    #[hax_lib::requires(fstar!(r#"
        (Seq.length $serialized == 4 \/ Seq.length $serialized == 6) /\
        Libcrux_ml_dsa.Simd.Traits.Specs.is_pos_array_opaque (pow2 (Seq.length $serialized))
            (f_repr ${simd_unit})"#))]
    #[hax_lib::ensures(|_| fstar!(r#"
        Seq.length ${serialized}_future == Seq.length ${serialized}"#))]
    fn commitment_serialize(simd_unit: &Self, serialized: &mut [u8]);

    // Error: 3 bytes for eta = 2 (3-bit), 4 bytes for eta = 4 (4-bit).
    // F-3 (2026-04-28): pre uses non-negative-bounded `is_pos_array_opaque`
    // since the impl operates on the shifted (non-negative) representation
    // of error values (eta - x).
    #[hax_lib::requires(fstar!(r#"
        Seq.length $serialized == (match $eta with
                                   | Libcrux_ml_dsa.Constants.Eta_Two -> 3
                                   | Libcrux_ml_dsa.Constants.Eta_Four -> 4) /\
        Libcrux_ml_dsa.Simd.Traits.Specs.is_pos_array_opaque
            (match $eta with
             | Libcrux_ml_dsa.Constants.Eta_Two -> 2
             | Libcrux_ml_dsa.Constants.Eta_Four -> 4)
            (f_repr ${simd_unit})"#))]
    #[hax_lib::ensures(|_| fstar!(r#"
        Seq.length ${serialized}_future == Seq.length ${serialized}"#))]
    fn error_serialize(eta: Eta, simd_unit: &Self, serialized: &mut [u8]);
    #[hax_lib::requires(fstar!(r#"
        Seq.length $serialized == (match $eta with
                                   | Libcrux_ml_dsa.Constants.Eta_Two -> 3
                                   | Libcrux_ml_dsa.Constants.Eta_Four -> 4)"#))]
    #[hax_lib::ensures(|_| fstar!(r#"
        Spec.Utils.forall8 (fun (i: nat{i < 8}) ->
          ($eta == Libcrux_ml_dsa.Constants.Eta_Two ==>
              v (Seq.index (f_repr ${out}_future) i) >= -2 /\
              v (Seq.index (f_repr ${out}_future) i) <= 2) /\
          ($eta == Libcrux_ml_dsa.Constants.Eta_Four ==>
              v (Seq.index (f_repr ${out}_future) i) >= -4 /\
              v (Seq.index (f_repr ${out}_future) i) <= 4))"#))]
    fn error_deserialize(eta: Eta, serialized: &[u8], out: &mut Self);

    // t0: bit_pack with width 13.
    // F-3 (2026-04-28): pre uses non-negative-bounded `is_pos_array_opaque`
    // since the impl operates on the shifted (non-negative) t0 representation.
    #[hax_lib::requires(fstar!(r#"
        Seq.length $out == 13 /\
        Libcrux_ml_dsa.Simd.Traits.Specs.is_pos_array_opaque (pow2 13)
            (f_repr ${simd_unit})"#))]
    #[hax_lib::ensures(|_| fstar!(r#"
        Seq.length ${out}_future == Seq.length ${out}"#))]
    fn t0_serialize(simd_unit: &Self, out: &mut [u8]); // out len 13
    #[hax_lib::requires(serialized.len() == 13)]
    #[hax_lib::ensures(|_| fstar!(r#"
        Spec.Utils.is_i32b_array_opaque (pow2 12) (f_repr ${out}_future)"#))]
    fn t0_deserialize(serialized: &[u8], out: &mut Self);

    // t1: simple_bit_pack with width 10.
    #[hax_lib::requires(fstar!(r#"
        Seq.length $out == 10 /\
        (forall (i: nat). i < 8 ==>
          v (Seq.index (f_repr ${simd_unit}) i) >= 0 /\
          v (Seq.index (f_repr ${simd_unit}) i) < pow2 10)"#))]
    #[hax_lib::ensures(|_| fstar!(r#"
        Seq.length ${out}_future == Seq.length ${out}"#))]
    fn t1_serialize(simd_unit: &Self, out: &mut [u8]); // out len 10
    #[hax_lib::requires(serialized.len() == 10)]
    #[hax_lib::ensures(|_| fstar!(r#"
        Spec.Utils.forall8 (fun (i: nat{i < 8}) ->
          v (Seq.index (f_repr ${out}_future) i) >= 0 /\
          v (Seq.index (f_repr ${out}_future) i) < pow2 10)"#))]
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
    #[hax_lib::requires(fstar!(r#"
        (forall (i:nat). i < 32 ==>
            Spec.Utils.is_i32b_array_opaque 2143289343
                (f_repr (Seq.index ${simd_units} i)))"#))]
    #[hax_lib::ensures(|_| fstar!(r#"
        (forall (j:nat). j < 32 ==>
          Spec.Utils.is_i32b_array_opaque (v ${specs::FIELD_MAX})
            (f_repr (Seq.index ${simd_units}_future j)) /\
          Spec.Utils.forall8 (fun (i: nat{i < 8}) ->
            Libcrux_ml_dsa.Simd.Traits.Specs.reduce_lane_post
              (Seq.index (f_repr (Seq.index ${simd_units} j)) i)
              (Seq.index (f_repr (Seq.index ${simd_units}_future j)) i)))"#))]
    fn reduce(simd_units: &mut [Self; SIMD_UNITS_IN_RING_ELEMENT]);
}
