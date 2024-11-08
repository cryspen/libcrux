module Libcrux_ml_dsa.Simd.Traits
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

class t_Operations (v_Self: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_11581440318597584651:Core.Marker.t_Copy v_Self;
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_9442900250278684536:Core.Clone.t_Clone v_Self;
  f_ZERO_pre:Prims.unit -> Type0;
  f_ZERO_post:Prims.unit -> v_Self -> Type0;
  f_ZERO:x0: Prims.unit -> Prims.Pure v_Self (f_ZERO_pre x0) (fun result -> f_ZERO_post x0 result);
  f_from_coefficient_array_pre:t_Slice i32 -> Type0;
  f_from_coefficient_array_post:t_Slice i32 -> v_Self -> Type0;
  f_from_coefficient_array:x0: t_Slice i32
    -> Prims.Pure v_Self
        (f_from_coefficient_array_pre x0)
        (fun result -> f_from_coefficient_array_post x0 result);
  f_to_coefficient_array_pre:v_Self -> Type0;
  f_to_coefficient_array_post:v_Self -> t_Array i32 (sz 8) -> Type0;
  f_to_coefficient_array:x0: v_Self
    -> Prims.Pure (t_Array i32 (sz 8))
        (f_to_coefficient_array_pre x0)
        (fun result -> f_to_coefficient_array_post x0 result);
  f_add_pre:v_Self -> v_Self -> Type0;
  f_add_post:v_Self -> v_Self -> v_Self -> Type0;
  f_add:x0: v_Self -> x1: v_Self
    -> Prims.Pure v_Self (f_add_pre x0 x1) (fun result -> f_add_post x0 x1 result);
  f_subtract_pre:v_Self -> v_Self -> Type0;
  f_subtract_post:v_Self -> v_Self -> v_Self -> Type0;
  f_subtract:x0: v_Self -> x1: v_Self
    -> Prims.Pure v_Self (f_subtract_pre x0 x1) (fun result -> f_subtract_post x0 x1 result);
  f_infinity_norm_exceeds_pre:v_Self -> i32 -> Type0;
  f_infinity_norm_exceeds_post:v_Self -> i32 -> bool -> Type0;
  f_infinity_norm_exceeds:x0: v_Self -> x1: i32
    -> Prims.Pure bool
        (f_infinity_norm_exceeds_pre x0 x1)
        (fun result -> f_infinity_norm_exceeds_post x0 x1 result);
  f_decompose_pre:v_GAMMA2: i32 -> v_Self -> Type0;
  f_decompose_post:v_GAMMA2: i32 -> v_Self -> (v_Self & v_Self) -> Type0;
  f_decompose:v_GAMMA2: i32 -> x0: v_Self
    -> Prims.Pure (v_Self & v_Self)
        (f_decompose_pre v_GAMMA2 x0)
        (fun result -> f_decompose_post v_GAMMA2 x0 result);
  f_compute_hint_pre:v_GAMMA2: i32 -> v_Self -> v_Self -> Type0;
  f_compute_hint_post:v_GAMMA2: i32 -> v_Self -> v_Self -> (usize & v_Self) -> Type0;
  f_compute_hint:v_GAMMA2: i32 -> x0: v_Self -> x1: v_Self
    -> Prims.Pure (usize & v_Self)
        (f_compute_hint_pre v_GAMMA2 x0 x1)
        (fun result -> f_compute_hint_post v_GAMMA2 x0 x1 result);
  f_use_hint_pre:v_GAMMA2: i32 -> v_Self -> v_Self -> Type0;
  f_use_hint_post:v_GAMMA2: i32 -> v_Self -> v_Self -> v_Self -> Type0;
  f_use_hint:v_GAMMA2: i32 -> x0: v_Self -> x1: v_Self
    -> Prims.Pure v_Self
        (f_use_hint_pre v_GAMMA2 x0 x1)
        (fun result -> f_use_hint_post v_GAMMA2 x0 x1 result);
  f_montgomery_multiply_pre:v_Self -> v_Self -> Type0;
  f_montgomery_multiply_post:v_Self -> v_Self -> v_Self -> Type0;
  f_montgomery_multiply:x0: v_Self -> x1: v_Self
    -> Prims.Pure v_Self
        (f_montgomery_multiply_pre x0 x1)
        (fun result -> f_montgomery_multiply_post x0 x1 result);
  f_montgomery_multiply_by_constant_pre:v_Self -> i32 -> Type0;
  f_montgomery_multiply_by_constant_post:v_Self -> i32 -> v_Self -> Type0;
  f_montgomery_multiply_by_constant:x0: v_Self -> x1: i32
    -> Prims.Pure v_Self
        (f_montgomery_multiply_by_constant_pre x0 x1)
        (fun result -> f_montgomery_multiply_by_constant_post x0 x1 result);
  f_shift_left_then_reduce_pre:v_SHIFT_BY: i32 -> v_Self -> Type0;
  f_shift_left_then_reduce_post:v_SHIFT_BY: i32 -> v_Self -> v_Self -> Type0;
  f_shift_left_then_reduce:v_SHIFT_BY: i32 -> x0: v_Self
    -> Prims.Pure v_Self
        (f_shift_left_then_reduce_pre v_SHIFT_BY x0)
        (fun result -> f_shift_left_then_reduce_post v_SHIFT_BY x0 result);
  f_power2round_pre:v_Self -> Type0;
  f_power2round_post:v_Self -> (v_Self & v_Self) -> Type0;
  f_power2round:x0: v_Self
    -> Prims.Pure (v_Self & v_Self)
        (f_power2round_pre x0)
        (fun result -> f_power2round_post x0 result);
  f_rejection_sample_less_than_field_modulus_pre:t_Slice u8 -> t_Slice i32 -> Type0;
  f_rejection_sample_less_than_field_modulus_post:t_Slice u8 -> t_Slice i32 -> (t_Slice i32 & usize)
    -> Type0;
  f_rejection_sample_less_than_field_modulus:x0: t_Slice u8 -> x1: t_Slice i32
    -> Prims.Pure (t_Slice i32 & usize)
        (f_rejection_sample_less_than_field_modulus_pre x0 x1)
        (fun result -> f_rejection_sample_less_than_field_modulus_post x0 x1 result);
  f_rejection_sample_less_than_eta_equals_2_pre:t_Slice u8 -> t_Slice i32 -> Type0;
  f_rejection_sample_less_than_eta_equals_2_post:t_Slice u8 -> t_Slice i32 -> (t_Slice i32 & usize)
    -> Type0;
  f_rejection_sample_less_than_eta_equals_2_:x0: t_Slice u8 -> x1: t_Slice i32
    -> Prims.Pure (t_Slice i32 & usize)
        (f_rejection_sample_less_than_eta_equals_2_pre x0 x1)
        (fun result -> f_rejection_sample_less_than_eta_equals_2_post x0 x1 result);
  f_rejection_sample_less_than_eta_equals_4_pre:t_Slice u8 -> t_Slice i32 -> Type0;
  f_rejection_sample_less_than_eta_equals_4_post:t_Slice u8 -> t_Slice i32 -> (t_Slice i32 & usize)
    -> Type0;
  f_rejection_sample_less_than_eta_equals_4_:x0: t_Slice u8 -> x1: t_Slice i32
    -> Prims.Pure (t_Slice i32 & usize)
        (f_rejection_sample_less_than_eta_equals_4_pre x0 x1)
        (fun result -> f_rejection_sample_less_than_eta_equals_4_post x0 x1 result);
  f_gamma1_serialize_pre:v_OUTPUT_SIZE: usize -> v_Self -> Type0;
  f_gamma1_serialize_post:v_OUTPUT_SIZE: usize -> v_Self -> t_Array u8 v_OUTPUT_SIZE -> Type0;
  f_gamma1_serialize:v_OUTPUT_SIZE: usize -> x0: v_Self
    -> Prims.Pure (t_Array u8 v_OUTPUT_SIZE)
        (f_gamma1_serialize_pre v_OUTPUT_SIZE x0)
        (fun result -> f_gamma1_serialize_post v_OUTPUT_SIZE x0 result);
  f_gamma1_deserialize_pre:v_GAMMA1_EXPONENT: usize -> t_Slice u8 -> Type0;
  f_gamma1_deserialize_post:v_GAMMA1_EXPONENT: usize -> t_Slice u8 -> v_Self -> Type0;
  f_gamma1_deserialize:v_GAMMA1_EXPONENT: usize -> x0: t_Slice u8
    -> Prims.Pure v_Self
        (f_gamma1_deserialize_pre v_GAMMA1_EXPONENT x0)
        (fun result -> f_gamma1_deserialize_post v_GAMMA1_EXPONENT x0 result);
  f_commitment_serialize_pre:v_OUTPUT_SIZE: usize -> v_Self -> Type0;
  f_commitment_serialize_post:v_OUTPUT_SIZE: usize -> v_Self -> t_Array u8 v_OUTPUT_SIZE -> Type0;
  f_commitment_serialize:v_OUTPUT_SIZE: usize -> x0: v_Self
    -> Prims.Pure (t_Array u8 v_OUTPUT_SIZE)
        (f_commitment_serialize_pre v_OUTPUT_SIZE x0)
        (fun result -> f_commitment_serialize_post v_OUTPUT_SIZE x0 result);
  f_error_serialize_pre:v_OUTPUT_SIZE: usize -> v_Self -> Type0;
  f_error_serialize_post:v_OUTPUT_SIZE: usize -> v_Self -> t_Array u8 v_OUTPUT_SIZE -> Type0;
  f_error_serialize:v_OUTPUT_SIZE: usize -> x0: v_Self
    -> Prims.Pure (t_Array u8 v_OUTPUT_SIZE)
        (f_error_serialize_pre v_OUTPUT_SIZE x0)
        (fun result -> f_error_serialize_post v_OUTPUT_SIZE x0 result);
  f_error_deserialize_pre:v_ETA: usize -> t_Slice u8 -> Type0;
  f_error_deserialize_post:v_ETA: usize -> t_Slice u8 -> v_Self -> Type0;
  f_error_deserialize:v_ETA: usize -> x0: t_Slice u8
    -> Prims.Pure v_Self
        (f_error_deserialize_pre v_ETA x0)
        (fun result -> f_error_deserialize_post v_ETA x0 result);
  f_t0_serialize_pre:v_Self -> Type0;
  f_t0_serialize_post:v_Self -> t_Array u8 (sz 13) -> Type0;
  f_t0_serialize:x0: v_Self
    -> Prims.Pure (t_Array u8 (sz 13))
        (f_t0_serialize_pre x0)
        (fun result -> f_t0_serialize_post x0 result);
  f_t0_deserialize_pre:t_Slice u8 -> Type0;
  f_t0_deserialize_post:t_Slice u8 -> v_Self -> Type0;
  f_t0_deserialize:x0: t_Slice u8
    -> Prims.Pure v_Self (f_t0_deserialize_pre x0) (fun result -> f_t0_deserialize_post x0 result);
  f_t1_serialize_pre:v_Self -> Type0;
  f_t1_serialize_post:v_Self -> t_Array u8 (sz 10) -> Type0;
  f_t1_serialize:x0: v_Self
    -> Prims.Pure (t_Array u8 (sz 10))
        (f_t1_serialize_pre x0)
        (fun result -> f_t1_serialize_post x0 result);
  f_t1_deserialize_pre:t_Slice u8 -> Type0;
  f_t1_deserialize_post:t_Slice u8 -> v_Self -> Type0;
  f_t1_deserialize:x0: t_Slice u8
    -> Prims.Pure v_Self (f_t1_deserialize_pre x0) (fun result -> f_t1_deserialize_post x0 result);
  f_ntt_pre:t_Array v_Self (sz 32) -> Type0;
  f_ntt_post:t_Array v_Self (sz 32) -> t_Array v_Self (sz 32) -> Type0;
  f_ntt:x0: t_Array v_Self (sz 32)
    -> Prims.Pure (t_Array v_Self (sz 32)) (f_ntt_pre x0) (fun result -> f_ntt_post x0 result);
  f_invert_ntt_at_layer_0_pre:v_Self -> i32 -> i32 -> i32 -> i32 -> Type0;
  f_invert_ntt_at_layer_0_post:v_Self -> i32 -> i32 -> i32 -> i32 -> v_Self -> Type0;
  f_invert_ntt_at_layer_0_:x0: v_Self -> x1: i32 -> x2: i32 -> x3: i32 -> x4: i32
    -> Prims.Pure v_Self
        (f_invert_ntt_at_layer_0_pre x0 x1 x2 x3 x4)
        (fun result -> f_invert_ntt_at_layer_0_post x0 x1 x2 x3 x4 result);
  f_invert_ntt_at_layer_1_pre:v_Self -> i32 -> i32 -> Type0;
  f_invert_ntt_at_layer_1_post:v_Self -> i32 -> i32 -> v_Self -> Type0;
  f_invert_ntt_at_layer_1_:x0: v_Self -> x1: i32 -> x2: i32
    -> Prims.Pure v_Self
        (f_invert_ntt_at_layer_1_pre x0 x1 x2)
        (fun result -> f_invert_ntt_at_layer_1_post x0 x1 x2 result);
  f_invert_ntt_at_layer_2_pre:v_Self -> i32 -> Type0;
  f_invert_ntt_at_layer_2_post:v_Self -> i32 -> v_Self -> Type0;
  f_invert_ntt_at_layer_2_:x0: v_Self -> x1: i32
    -> Prims.Pure v_Self
        (f_invert_ntt_at_layer_2_pre x0 x1)
        (fun result -> f_invert_ntt_at_layer_2_post x0 x1 result)
}

let v_COEFFICIENTS_IN_SIMD_UNIT: usize = sz 8

let v_FIELD_MODULUS: i32 = 8380417l

let v_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R: u64 = 58728449uL

let v_SIMD_UNITS_IN_RING_ELEMENT: usize =
  Libcrux_ml_dsa.Constants.v_COEFFICIENTS_IN_RING_ELEMENT /! v_COEFFICIENTS_IN_SIMD_UNIT

val montgomery_multiply_by_fer (#v_S: Type0) {| i1: t_Operations v_S |} (simd_unit: v_S) (fer: i32)
    : Prims.Pure v_S Prims.l_True (fun _ -> Prims.l_True)
