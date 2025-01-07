module Libcrux_ml_dsa.Simd.Avx2
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_intrinsics.Avx2_extract in
  let open Libcrux_ml_dsa.Simd.Avx2.Vector_type in
  ()

/// Implementing the [`Operations`] for AVX2.
[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: Libcrux_ml_dsa.Simd.Traits.t_Operations
Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit =
  {
    _super_13011033735201511749 = FStar.Tactics.Typeclasses.solve;
    _super_9529721400157967266 = FStar.Tactics.Typeclasses.solve;
    f_Coefficient = Libcrux_intrinsics.Avx2_extract.t_Vec256;
    f_Coefficient_2030105210046411076 = FStar.Tactics.Typeclasses.solve;
    f_zero_pre = (fun (_: Prims.unit) -> true);
    f_zero_post = (fun (_: Prims.unit) (out: Libcrux_intrinsics.Avx2_extract.t_Vec256) -> true);
    f_zero = (fun (_: Prims.unit) -> Libcrux_ml_dsa.Simd.Avx2.Vector_type.zero ());
    f_from_coefficient_array_pre
    =
    (fun (coefficient_array: t_Slice i32) (out: Libcrux_intrinsics.Avx2_extract.t_Vec256) -> true);
    f_from_coefficient_array_post
    =
    (fun
        (coefficient_array: t_Slice i32)
        (out: Libcrux_intrinsics.Avx2_extract.t_Vec256)
        (out1: Libcrux_intrinsics.Avx2_extract.t_Vec256)
        ->
        true);
    f_from_coefficient_array
    =
    (fun (coefficient_array: t_Slice i32) (out: Libcrux_intrinsics.Avx2_extract.t_Vec256) ->
        let hax_temp_output, out:(Prims.unit & Libcrux_intrinsics.Avx2_extract.t_Vec256) =
          (), Libcrux_ml_dsa.Simd.Avx2.Vector_type.from_coefficient_array coefficient_array out
          <:
          (Prims.unit & Libcrux_intrinsics.Avx2_extract.t_Vec256)
        in
        out);
    f_to_coefficient_array_pre
    =
    (fun (value: Libcrux_intrinsics.Avx2_extract.t_Vec256) (out: t_Slice i32) -> true);
    f_to_coefficient_array_post
    =
    (fun (value: Libcrux_intrinsics.Avx2_extract.t_Vec256) (out: t_Slice i32) (out1: t_Slice i32) ->
        true);
    f_to_coefficient_array
    =
    (fun (value: Libcrux_intrinsics.Avx2_extract.t_Vec256) (out: t_Slice i32) ->
        let hax_temp_output, out:(Prims.unit & t_Slice i32) =
          (), Libcrux_ml_dsa.Simd.Avx2.Vector_type.to_coefficient_array value out
          <:
          (Prims.unit & t_Slice i32)
        in
        out);
    f_add_pre
    =
    (fun
        (lhs: Libcrux_intrinsics.Avx2_extract.t_Vec256)
        (rhs: Libcrux_intrinsics.Avx2_extract.t_Vec256)
        ->
        true);
    f_add_post
    =
    (fun
        (lhs: Libcrux_intrinsics.Avx2_extract.t_Vec256)
        (rhs: Libcrux_intrinsics.Avx2_extract.t_Vec256)
        (out: Libcrux_intrinsics.Avx2_extract.t_Vec256)
        ->
        true);
    f_add
    =
    (fun
        (lhs: Libcrux_intrinsics.Avx2_extract.t_Vec256)
        (rhs: Libcrux_intrinsics.Avx2_extract.t_Vec256)
        ->
        let hax_temp_output, lhs:(Prims.unit & Libcrux_intrinsics.Avx2_extract.t_Vec256) =
          (), Libcrux_ml_dsa.Simd.Avx2.Arithmetic.add lhs rhs
          <:
          (Prims.unit & Libcrux_intrinsics.Avx2_extract.t_Vec256)
        in
        lhs);
    f_subtract_pre
    =
    (fun
        (lhs: Libcrux_intrinsics.Avx2_extract.t_Vec256)
        (rhs: Libcrux_intrinsics.Avx2_extract.t_Vec256)
        ->
        true);
    f_subtract_post
    =
    (fun
        (lhs: Libcrux_intrinsics.Avx2_extract.t_Vec256)
        (rhs: Libcrux_intrinsics.Avx2_extract.t_Vec256)
        (out: Libcrux_intrinsics.Avx2_extract.t_Vec256)
        ->
        true);
    f_subtract
    =
    (fun
        (lhs: Libcrux_intrinsics.Avx2_extract.t_Vec256)
        (rhs: Libcrux_intrinsics.Avx2_extract.t_Vec256)
        ->
        let hax_temp_output, lhs:(Prims.unit & Libcrux_intrinsics.Avx2_extract.t_Vec256) =
          (), Libcrux_ml_dsa.Simd.Avx2.Arithmetic.subtract lhs rhs
          <:
          (Prims.unit & Libcrux_intrinsics.Avx2_extract.t_Vec256)
        in
        lhs);
    f_montgomery_multiply_pre
    =
    (fun
        (lhs: Libcrux_intrinsics.Avx2_extract.t_Vec256)
        (rhs: Libcrux_intrinsics.Avx2_extract.t_Vec256)
        ->
        true);
    f_montgomery_multiply_post
    =
    (fun
        (lhs: Libcrux_intrinsics.Avx2_extract.t_Vec256)
        (rhs: Libcrux_intrinsics.Avx2_extract.t_Vec256)
        (out: Libcrux_intrinsics.Avx2_extract.t_Vec256)
        ->
        true);
    f_montgomery_multiply
    =
    (fun
        (lhs: Libcrux_intrinsics.Avx2_extract.t_Vec256)
        (rhs: Libcrux_intrinsics.Avx2_extract.t_Vec256)
        ->
        let lhs:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
          Libcrux_ml_dsa.Simd.Avx2.Arithmetic.montgomery_multiply lhs rhs
        in
        lhs);
    f_shift_left_then_reduce_pre
    =
    (fun (v_SHIFT_BY: i32) (simd_unit: Libcrux_intrinsics.Avx2_extract.t_Vec256) -> true);
    f_shift_left_then_reduce_post
    =
    (fun
        (v_SHIFT_BY: i32)
        (simd_unit: Libcrux_intrinsics.Avx2_extract.t_Vec256)
        (out: Libcrux_intrinsics.Avx2_extract.t_Vec256)
        ->
        true);
    f_shift_left_then_reduce
    =
    (fun (v_SHIFT_BY: i32) (simd_unit: Libcrux_intrinsics.Avx2_extract.t_Vec256) ->
        let hax_temp_output, simd_unit:(Prims.unit & Libcrux_intrinsics.Avx2_extract.t_Vec256) =
          (), Libcrux_ml_dsa.Simd.Avx2.Arithmetic.shift_left_then_reduce v_SHIFT_BY simd_unit
          <:
          (Prims.unit & Libcrux_intrinsics.Avx2_extract.t_Vec256)
        in
        simd_unit);
    f_power2round_pre
    =
    (fun
        (t0: Libcrux_intrinsics.Avx2_extract.t_Vec256)
        (t1: Libcrux_intrinsics.Avx2_extract.t_Vec256)
        ->
        true);
    f_power2round_post
    =
    (fun
        (t0: Libcrux_intrinsics.Avx2_extract.t_Vec256)
        (t1: Libcrux_intrinsics.Avx2_extract.t_Vec256)
        (out: (Libcrux_intrinsics.Avx2_extract.t_Vec256 & Libcrux_intrinsics.Avx2_extract.t_Vec256))
        ->
        true);
    f_power2round
    =
    (fun
        (t0: Libcrux_intrinsics.Avx2_extract.t_Vec256)
        (t1: Libcrux_intrinsics.Avx2_extract.t_Vec256)
        ->
        let tmp0, tmp1:(Libcrux_intrinsics.Avx2_extract.t_Vec256 &
          Libcrux_intrinsics.Avx2_extract.t_Vec256) =
          Libcrux_ml_dsa.Simd.Avx2.Arithmetic.power2round t0 t1
        in
        let t0:Libcrux_intrinsics.Avx2_extract.t_Vec256 = tmp0 in
        let t1:Libcrux_intrinsics.Avx2_extract.t_Vec256 = tmp1 in
        let _:Prims.unit = () in
        t0, t1
        <:
        (Libcrux_intrinsics.Avx2_extract.t_Vec256 & Libcrux_intrinsics.Avx2_extract.t_Vec256));
    f_infinity_norm_exceeds_pre
    =
    (fun (simd_unit: Libcrux_intrinsics.Avx2_extract.t_Vec256) (bound: i32) -> true);
    f_infinity_norm_exceeds_post
    =
    (fun (simd_unit: Libcrux_intrinsics.Avx2_extract.t_Vec256) (bound: i32) (out: bool) -> true);
    f_infinity_norm_exceeds
    =
    (fun (simd_unit: Libcrux_intrinsics.Avx2_extract.t_Vec256) (bound: i32) ->
        Libcrux_ml_dsa.Simd.Avx2.Arithmetic.infinity_norm_exceeds simd_unit bound);
    f_decompose_pre
    =
    (fun
        (gamma2: i32)
        (simd_unit: Libcrux_intrinsics.Avx2_extract.t_Vec256)
        (low: Libcrux_intrinsics.Avx2_extract.t_Vec256)
        (high: Libcrux_intrinsics.Avx2_extract.t_Vec256)
        ->
        true);
    f_decompose_post
    =
    (fun
        (gamma2: i32)
        (simd_unit: Libcrux_intrinsics.Avx2_extract.t_Vec256)
        (low: Libcrux_intrinsics.Avx2_extract.t_Vec256)
        (high: Libcrux_intrinsics.Avx2_extract.t_Vec256)
        (out: (Libcrux_intrinsics.Avx2_extract.t_Vec256 & Libcrux_intrinsics.Avx2_extract.t_Vec256))
        ->
        true);
    f_decompose
    =
    (fun
        (gamma2: i32)
        (simd_unit: Libcrux_intrinsics.Avx2_extract.t_Vec256)
        (low: Libcrux_intrinsics.Avx2_extract.t_Vec256)
        (high: Libcrux_intrinsics.Avx2_extract.t_Vec256)
        ->
        let tmp0, tmp1:(Libcrux_intrinsics.Avx2_extract.t_Vec256 &
          Libcrux_intrinsics.Avx2_extract.t_Vec256) =
          Libcrux_ml_dsa.Simd.Avx2.Arithmetic.decompose gamma2 simd_unit low high
        in
        let low:Libcrux_intrinsics.Avx2_extract.t_Vec256 = tmp0 in
        let high:Libcrux_intrinsics.Avx2_extract.t_Vec256 = tmp1 in
        let _:Prims.unit = () in
        low, high
        <:
        (Libcrux_intrinsics.Avx2_extract.t_Vec256 & Libcrux_intrinsics.Avx2_extract.t_Vec256));
    f_compute_hint_pre
    =
    (fun
        (v_GAMMA2: i32)
        (low: Libcrux_intrinsics.Avx2_extract.t_Vec256)
        (high: Libcrux_intrinsics.Avx2_extract.t_Vec256)
        (hint: Libcrux_intrinsics.Avx2_extract.t_Vec256)
        ->
        true);
    f_compute_hint_post
    =
    (fun
        (v_GAMMA2: i32)
        (low: Libcrux_intrinsics.Avx2_extract.t_Vec256)
        (high: Libcrux_intrinsics.Avx2_extract.t_Vec256)
        (hint: Libcrux_intrinsics.Avx2_extract.t_Vec256)
        (out2: (Libcrux_intrinsics.Avx2_extract.t_Vec256 & usize))
        ->
        true);
    f_compute_hint
    =
    (fun
        (v_GAMMA2: i32)
        (low: Libcrux_intrinsics.Avx2_extract.t_Vec256)
        (high: Libcrux_intrinsics.Avx2_extract.t_Vec256)
        (hint: Libcrux_intrinsics.Avx2_extract.t_Vec256)
        ->
        let tmp0, out1:(Libcrux_intrinsics.Avx2_extract.t_Vec256 & usize) =
          Libcrux_ml_dsa.Simd.Avx2.Arithmetic.compute_hint v_GAMMA2 low high hint
        in
        let hint:Libcrux_intrinsics.Avx2_extract.t_Vec256 = tmp0 in
        let hax_temp_output:usize = out1 in
        hint, hax_temp_output <: (Libcrux_intrinsics.Avx2_extract.t_Vec256 & usize));
    f_use_hint_pre
    =
    (fun
        (gamma2: i32)
        (simd_unit: Libcrux_intrinsics.Avx2_extract.t_Vec256)
        (hint: Libcrux_intrinsics.Avx2_extract.t_Vec256)
        ->
        true);
    f_use_hint_post
    =
    (fun
        (gamma2: i32)
        (simd_unit: Libcrux_intrinsics.Avx2_extract.t_Vec256)
        (hint: Libcrux_intrinsics.Avx2_extract.t_Vec256)
        (out: Libcrux_intrinsics.Avx2_extract.t_Vec256)
        ->
        true);
    f_use_hint
    =
    (fun
        (gamma2: i32)
        (simd_unit: Libcrux_intrinsics.Avx2_extract.t_Vec256)
        (hint: Libcrux_intrinsics.Avx2_extract.t_Vec256)
        ->
        let hint:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
          Libcrux_ml_dsa.Simd.Avx2.Arithmetic.use_hint gamma2 simd_unit hint
        in
        hint);
    f_rejection_sample_less_than_field_modulus_pre
    =
    (fun (randomness: t_Slice u8) (out: t_Slice i32) -> true);
    f_rejection_sample_less_than_field_modulus_post
    =
    (fun (randomness: t_Slice u8) (out: t_Slice i32) (out2: (t_Slice i32 & usize)) -> true);
    f_rejection_sample_less_than_field_modulus
    =
    (fun (randomness: t_Slice u8) (out: t_Slice i32) ->
        let tmp0, out1:(t_Slice i32 & usize) =
          Libcrux_ml_dsa.Simd.Avx2.Rejection_sample.Less_than_field_modulus.sample randomness out
        in
        let out:t_Slice i32 = tmp0 in
        let hax_temp_output:usize = out1 in
        out, hax_temp_output <: (t_Slice i32 & usize));
    f_rejection_sample_less_than_eta_equals_2_pre
    =
    (fun (randomness: t_Slice u8) (out: t_Slice i32) -> true);
    f_rejection_sample_less_than_eta_equals_2_post
    =
    (fun (randomness: t_Slice u8) (out: t_Slice i32) (out2: (t_Slice i32 & usize)) -> true);
    f_rejection_sample_less_than_eta_equals_2_
    =
    (fun (randomness: t_Slice u8) (out: t_Slice i32) ->
        let tmp0, out1:(t_Slice i32 & usize) =
          Libcrux_ml_dsa.Simd.Avx2.Rejection_sample.Less_than_eta.sample (sz 2) randomness out
        in
        let out:t_Slice i32 = tmp0 in
        let hax_temp_output:usize = out1 in
        out, hax_temp_output <: (t_Slice i32 & usize));
    f_rejection_sample_less_than_eta_equals_4_pre
    =
    (fun (randomness: t_Slice u8) (out: t_Slice i32) -> true);
    f_rejection_sample_less_than_eta_equals_4_post
    =
    (fun (randomness: t_Slice u8) (out: t_Slice i32) (out2: (t_Slice i32 & usize)) -> true);
    f_rejection_sample_less_than_eta_equals_4_
    =
    (fun (randomness: t_Slice u8) (out: t_Slice i32) ->
        let tmp0, out1:(t_Slice i32 & usize) =
          Libcrux_ml_dsa.Simd.Avx2.Rejection_sample.Less_than_eta.sample (sz 4) randomness out
        in
        let out:t_Slice i32 = tmp0 in
        let hax_temp_output:usize = out1 in
        out, hax_temp_output <: (t_Slice i32 & usize));
    f_gamma1_serialize_pre
    =
    (fun
        (simd_unit: Libcrux_intrinsics.Avx2_extract.t_Vec256)
        (serialized: t_Slice u8)
        (gamma1_exponent: usize)
        ->
        true);
    f_gamma1_serialize_post
    =
    (fun
        (simd_unit: Libcrux_intrinsics.Avx2_extract.t_Vec256)
        (serialized: t_Slice u8)
        (gamma1_exponent: usize)
        (out: t_Slice u8)
        ->
        true);
    f_gamma1_serialize
    =
    (fun
        (simd_unit: Libcrux_intrinsics.Avx2_extract.t_Vec256)
        (serialized: t_Slice u8)
        (gamma1_exponent: usize)
        ->
        let hax_temp_output, serialized:(Prims.unit & t_Slice u8) =
          (),
          Libcrux_ml_dsa.Simd.Avx2.Encoding.Gamma1.serialize simd_unit serialized gamma1_exponent
          <:
          (Prims.unit & t_Slice u8)
        in
        serialized);
    f_gamma1_deserialize_pre
    =
    (fun
        (serialized: t_Slice u8)
        (out: Libcrux_intrinsics.Avx2_extract.t_Vec256)
        (gamma1_exponent: usize)
        ->
        true);
    f_gamma1_deserialize_post
    =
    (fun
        (serialized: t_Slice u8)
        (out: Libcrux_intrinsics.Avx2_extract.t_Vec256)
        (gamma1_exponent: usize)
        (out1: Libcrux_intrinsics.Avx2_extract.t_Vec256)
        ->
        true);
    f_gamma1_deserialize
    =
    (fun
        (serialized: t_Slice u8)
        (out: Libcrux_intrinsics.Avx2_extract.t_Vec256)
        (gamma1_exponent: usize)
        ->
        let out:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
          Libcrux_ml_dsa.Simd.Avx2.Encoding.Gamma1.deserialize serialized out gamma1_exponent
        in
        out);
    f_commitment_serialize_pre
    =
    (fun (simd_unit: Libcrux_intrinsics.Avx2_extract.t_Vec256) (serialized: t_Slice u8) -> true);
    f_commitment_serialize_post
    =
    (fun
        (simd_unit: Libcrux_intrinsics.Avx2_extract.t_Vec256)
        (serialized: t_Slice u8)
        (out: t_Slice u8)
        ->
        true);
    f_commitment_serialize
    =
    (fun (simd_unit: Libcrux_intrinsics.Avx2_extract.t_Vec256) (serialized: t_Slice u8) ->
        let hax_temp_output, serialized:(Prims.unit & t_Slice u8) =
          (), Libcrux_ml_dsa.Simd.Avx2.Encoding.Commitment.serialize simd_unit serialized
          <:
          (Prims.unit & t_Slice u8)
        in
        serialized);
    f_error_serialize_pre
    =
    (fun
        (eta: Libcrux_ml_dsa.Constants.t_Eta)
        (simd_unit: Libcrux_intrinsics.Avx2_extract.t_Vec256)
        (serialized: t_Slice u8)
        ->
        true);
    f_error_serialize_post
    =
    (fun
        (eta: Libcrux_ml_dsa.Constants.t_Eta)
        (simd_unit: Libcrux_intrinsics.Avx2_extract.t_Vec256)
        (serialized: t_Slice u8)
        (out: t_Slice u8)
        ->
        true);
    f_error_serialize
    =
    (fun
        (eta: Libcrux_ml_dsa.Constants.t_Eta)
        (simd_unit: Libcrux_intrinsics.Avx2_extract.t_Vec256)
        (serialized: t_Slice u8)
        ->
        let hax_temp_output, serialized:(Prims.unit & t_Slice u8) =
          (), Libcrux_ml_dsa.Simd.Avx2.Encoding.Error.serialize eta simd_unit serialized
          <:
          (Prims.unit & t_Slice u8)
        in
        serialized);
    f_error_deserialize_pre
    =
    (fun
        (eta: Libcrux_ml_dsa.Constants.t_Eta)
        (serialized: t_Slice u8)
        (out: Libcrux_intrinsics.Avx2_extract.t_Vec256)
        ->
        true);
    f_error_deserialize_post
    =
    (fun
        (eta: Libcrux_ml_dsa.Constants.t_Eta)
        (serialized: t_Slice u8)
        (out: Libcrux_intrinsics.Avx2_extract.t_Vec256)
        (out1: Libcrux_intrinsics.Avx2_extract.t_Vec256)
        ->
        true);
    f_error_deserialize
    =
    (fun
        (eta: Libcrux_ml_dsa.Constants.t_Eta)
        (serialized: t_Slice u8)
        (out: Libcrux_intrinsics.Avx2_extract.t_Vec256)
        ->
        let out:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
          Libcrux_ml_dsa.Simd.Avx2.Encoding.Error.deserialize eta serialized out
        in
        out);
    f_t0_serialize_pre
    =
    (fun (simd_unit: Libcrux_intrinsics.Avx2_extract.t_Vec256) (out: t_Slice u8) -> true);
    f_t0_serialize_post
    =
    (fun
        (simd_unit: Libcrux_intrinsics.Avx2_extract.t_Vec256)
        (out: t_Slice u8)
        (out1: t_Slice u8)
        ->
        true);
    f_t0_serialize
    =
    (fun (simd_unit: Libcrux_intrinsics.Avx2_extract.t_Vec256) (out: t_Slice u8) ->
        let out:t_Slice u8 = Libcrux_ml_dsa.Simd.Avx2.Encoding.T0.serialize simd_unit out in
        out);
    f_t0_deserialize_pre
    =
    (fun (serialized: t_Slice u8) (out: Libcrux_intrinsics.Avx2_extract.t_Vec256) -> true);
    f_t0_deserialize_post
    =
    (fun
        (serialized: t_Slice u8)
        (out: Libcrux_intrinsics.Avx2_extract.t_Vec256)
        (out1: Libcrux_intrinsics.Avx2_extract.t_Vec256)
        ->
        true);
    f_t0_deserialize
    =
    (fun (serialized: t_Slice u8) (out: Libcrux_intrinsics.Avx2_extract.t_Vec256) ->
        let out:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
          Libcrux_ml_dsa.Simd.Avx2.Encoding.T0.deserialize serialized out
        in
        out);
    f_t1_serialize_pre
    =
    (fun (simd_unit: Libcrux_intrinsics.Avx2_extract.t_Vec256) (out: t_Slice u8) -> true);
    f_t1_serialize_post
    =
    (fun
        (simd_unit: Libcrux_intrinsics.Avx2_extract.t_Vec256)
        (out: t_Slice u8)
        (out1: t_Slice u8)
        ->
        true);
    f_t1_serialize
    =
    (fun (simd_unit: Libcrux_intrinsics.Avx2_extract.t_Vec256) (out: t_Slice u8) ->
        let out:t_Slice u8 = Libcrux_ml_dsa.Simd.Avx2.Encoding.T1.serialize simd_unit out in
        out);
    f_t1_deserialize_pre
    =
    (fun (serialized: t_Slice u8) (out: Libcrux_intrinsics.Avx2_extract.t_Vec256) -> true);
    f_t1_deserialize_post
    =
    (fun
        (serialized: t_Slice u8)
        (out: Libcrux_intrinsics.Avx2_extract.t_Vec256)
        (out1: Libcrux_intrinsics.Avx2_extract.t_Vec256)
        ->
        true);
    f_t1_deserialize
    =
    (fun (serialized: t_Slice u8) (out: Libcrux_intrinsics.Avx2_extract.t_Vec256) ->
        let out:Libcrux_intrinsics.Avx2_extract.t_Vec256 =
          Libcrux_ml_dsa.Simd.Avx2.Encoding.T1.deserialize serialized out
        in
        out);
    f_ntt_pre = (fun (simd_units: t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32)) -> true);
    f_ntt_post
    =
    (fun
        (simd_units: t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32))
        (out: t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32))
        ->
        true);
    f_ntt
    =
    (fun (simd_units: t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32)) ->
        let simd_units:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
          Libcrux_ml_dsa.Simd.Avx2.Ntt.ntt simd_units
        in
        simd_units);
    f_invert_ntt_montgomery_pre
    =
    (fun (simd_units: t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32)) -> true);
    f_invert_ntt_montgomery_post
    =
    (fun
        (simd_units: t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32))
        (out: t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32))
        ->
        true);
    f_invert_ntt_montgomery
    =
    fun (simd_units: t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32)) ->
      let simd_units:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
        Libcrux_ml_dsa.Simd.Avx2.Invntt.invert_ntt_montgomery simd_units
      in
      simd_units
  }
