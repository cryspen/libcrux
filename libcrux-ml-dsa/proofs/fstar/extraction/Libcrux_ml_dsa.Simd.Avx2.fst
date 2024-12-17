module Libcrux_ml_dsa.Simd.Avx2
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_dsa.Simd.Avx2.Vector_type in
  ()

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: Libcrux_ml_dsa.Simd.Traits.t_Operations
Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit =
  {
    _super_11581440318597584651 = FStar.Tactics.Typeclasses.solve;
    _super_9442900250278684536 = FStar.Tactics.Typeclasses.solve;
    f_ZERO_pre = (fun (_: Prims.unit) -> true);
    f_ZERO_post
    =
    (fun (_: Prims.unit) (out: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit) -> true);
    f_ZERO = (fun (_: Prims.unit) -> Libcrux_ml_dsa.Simd.Avx2.Vector_type.v_ZERO ());
    f_from_coefficient_array_pre = (fun (coefficient_array: t_Slice i32) -> true);
    f_from_coefficient_array_post
    =
    (fun
        (coefficient_array: t_Slice i32)
        (out: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit)
        ->
        true);
    f_from_coefficient_array
    =
    (fun (coefficient_array: t_Slice i32) ->
        Libcrux_ml_dsa.Simd.Avx2.Vector_type.from_coefficient_array coefficient_array);
    f_to_coefficient_array_pre
    =
    (fun (self: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit) -> true);
    f_to_coefficient_array_post
    =
    (fun (self: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit) (out: t_Array i32 (sz 8)) ->
        true);
    f_to_coefficient_array
    =
    (fun (self: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit) ->
        Libcrux_ml_dsa.Simd.Avx2.Vector_type.to_coefficient_array self);
    f_add_pre
    =
    (fun
        (lhs: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit)
        (rhs: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit)
        ->
        true);
    f_add_post
    =
    (fun
        (lhs: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit)
        (rhs: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit)
        (out: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit)
        ->
        true);
    f_add
    =
    (fun
        (lhs: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit)
        (rhs: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit)
        ->
        Core.Convert.f_into #Libcrux_intrinsics.Avx2_extract.t_Vec256
          #Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit
          #FStar.Tactics.Typeclasses.solve
          (Libcrux_ml_dsa.Simd.Avx2.Arithmetic.add lhs
                .Libcrux_ml_dsa.Simd.Avx2.Vector_type.f_coefficients
              rhs.Libcrux_ml_dsa.Simd.Avx2.Vector_type.f_coefficients
            <:
            Libcrux_intrinsics.Avx2_extract.t_Vec256));
    f_subtract_pre
    =
    (fun
        (lhs: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit)
        (rhs: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit)
        ->
        true);
    f_subtract_post
    =
    (fun
        (lhs: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit)
        (rhs: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit)
        (out: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit)
        ->
        true);
    f_subtract
    =
    (fun
        (lhs: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit)
        (rhs: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit)
        ->
        Core.Convert.f_into #Libcrux_intrinsics.Avx2_extract.t_Vec256
          #Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit
          #FStar.Tactics.Typeclasses.solve
          (Libcrux_ml_dsa.Simd.Avx2.Arithmetic.subtract lhs
                .Libcrux_ml_dsa.Simd.Avx2.Vector_type.f_coefficients
              rhs.Libcrux_ml_dsa.Simd.Avx2.Vector_type.f_coefficients
            <:
            Libcrux_intrinsics.Avx2_extract.t_Vec256));
    f_montgomery_multiply_pre
    =
    (fun
        (lhs: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit)
        (rhs: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit)
        ->
        true);
    f_montgomery_multiply_post
    =
    (fun
        (lhs: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit)
        (rhs: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit)
        (out: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit)
        ->
        true);
    f_montgomery_multiply
    =
    (fun
        (lhs: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit)
        (rhs: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit)
        ->
        Core.Convert.f_into #Libcrux_intrinsics.Avx2_extract.t_Vec256
          #Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit
          #FStar.Tactics.Typeclasses.solve
          (Libcrux_ml_dsa.Simd.Avx2.Arithmetic.montgomery_multiply lhs
                .Libcrux_ml_dsa.Simd.Avx2.Vector_type.f_coefficients
              rhs.Libcrux_ml_dsa.Simd.Avx2.Vector_type.f_coefficients
            <:
            Libcrux_intrinsics.Avx2_extract.t_Vec256));
    f_shift_left_then_reduce_pre
    =
    (fun (v_SHIFT_BY: i32) (simd_unit: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit) -> true);
    f_shift_left_then_reduce_post
    =
    (fun
        (v_SHIFT_BY: i32)
        (simd_unit: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit)
        (out: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit)
        ->
        true);
    f_shift_left_then_reduce
    =
    (fun (v_SHIFT_BY: i32) (simd_unit: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit) ->
        Core.Convert.f_into #Libcrux_intrinsics.Avx2_extract.t_Vec256
          #Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit
          #FStar.Tactics.Typeclasses.solve
          (Libcrux_ml_dsa.Simd.Avx2.Arithmetic.shift_left_then_reduce v_SHIFT_BY
              simd_unit.Libcrux_ml_dsa.Simd.Avx2.Vector_type.f_coefficients
            <:
            Libcrux_intrinsics.Avx2_extract.t_Vec256));
    f_power2round_pre
    =
    (fun (simd_unit: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit) -> true);
    f_power2round_post
    =
    (fun
        (simd_unit: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit)
        (out:
          (Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit &
            Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit))
        ->
        true);
    f_power2round
    =
    (fun (simd_unit: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit) ->
        let lower, upper:(Libcrux_intrinsics.Avx2_extract.t_Vec256 &
          Libcrux_intrinsics.Avx2_extract.t_Vec256) =
          Libcrux_ml_dsa.Simd.Avx2.Arithmetic.power2round simd_unit
              .Libcrux_ml_dsa.Simd.Avx2.Vector_type.f_coefficients
        in
        Core.Convert.f_into #Libcrux_intrinsics.Avx2_extract.t_Vec256
          #Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit
          #FStar.Tactics.Typeclasses.solve
          lower,
        Core.Convert.f_into #Libcrux_intrinsics.Avx2_extract.t_Vec256
          #Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit
          #FStar.Tactics.Typeclasses.solve
          upper
        <:
        (Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit &
          Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit));
    f_infinity_norm_exceeds_pre
    =
    (fun (simd_unit: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit) (bound: i32) -> true);
    f_infinity_norm_exceeds_post
    =
    (fun
        (simd_unit: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit)
        (bound: i32)
        (out: bool)
        ->
        true);
    f_infinity_norm_exceeds
    =
    (fun (simd_unit: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit) (bound: i32) ->
        Libcrux_ml_dsa.Simd.Avx2.Arithmetic.infinity_norm_exceeds simd_unit
            .Libcrux_ml_dsa.Simd.Avx2.Vector_type.f_coefficients
          bound);
    f_decompose_pre
    =
    (fun (v_GAMMA2: i32) (simd_unit: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit) -> true);
    f_decompose_post
    =
    (fun
        (v_GAMMA2: i32)
        (simd_unit: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit)
        (out:
          (Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit &
            Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit))
        ->
        true);
    f_decompose
    =
    (fun (v_GAMMA2: i32) (simd_unit: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit) ->
        let lower, upper:(Libcrux_intrinsics.Avx2_extract.t_Vec256 &
          Libcrux_intrinsics.Avx2_extract.t_Vec256) =
          Libcrux_ml_dsa.Simd.Avx2.Arithmetic.decompose v_GAMMA2
            simd_unit.Libcrux_ml_dsa.Simd.Avx2.Vector_type.f_coefficients
        in
        Core.Convert.f_into #Libcrux_intrinsics.Avx2_extract.t_Vec256
          #Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit
          #FStar.Tactics.Typeclasses.solve
          lower,
        Core.Convert.f_into #Libcrux_intrinsics.Avx2_extract.t_Vec256
          #Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit
          #FStar.Tactics.Typeclasses.solve
          upper
        <:
        (Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit &
          Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit));
    f_compute_hint_pre
    =
    (fun
        (v_GAMMA2: i32)
        (low: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit)
        (high: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit)
        ->
        true);
    f_compute_hint_post
    =
    (fun
        (v_GAMMA2: i32)
        (low: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit)
        (high: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit)
        (out: (usize & Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit))
        ->
        true);
    f_compute_hint
    =
    (fun
        (v_GAMMA2: i32)
        (low: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit)
        (high: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit)
        ->
        let count, hint:(usize & Libcrux_intrinsics.Avx2_extract.t_Vec256) =
          Libcrux_ml_dsa.Simd.Avx2.Arithmetic.compute_hint v_GAMMA2
            low.Libcrux_ml_dsa.Simd.Avx2.Vector_type.f_coefficients
            high.Libcrux_ml_dsa.Simd.Avx2.Vector_type.f_coefficients
        in
        count,
        Core.Convert.f_into #Libcrux_intrinsics.Avx2_extract.t_Vec256
          #Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit
          #FStar.Tactics.Typeclasses.solve
          hint
        <:
        (usize & Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit));
    f_use_hint_pre
    =
    (fun
        (v_GAMMA2: i32)
        (simd_unit: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit)
        (hint: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit)
        ->
        true);
    f_use_hint_post
    =
    (fun
        (v_GAMMA2: i32)
        (simd_unit: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit)
        (hint: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit)
        (out: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit)
        ->
        true);
    f_use_hint
    =
    (fun
        (v_GAMMA2: i32)
        (simd_unit: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit)
        (hint: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit)
        ->
        Core.Convert.f_into #Libcrux_intrinsics.Avx2_extract.t_Vec256
          #Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit
          #FStar.Tactics.Typeclasses.solve
          (Libcrux_ml_dsa.Simd.Avx2.Arithmetic.use_hint v_GAMMA2
              simd_unit.Libcrux_ml_dsa.Simd.Avx2.Vector_type.f_coefficients
              hint.Libcrux_ml_dsa.Simd.Avx2.Vector_type.f_coefficients
            <:
            Libcrux_intrinsics.Avx2_extract.t_Vec256));
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
        (v_GAMMA1_EXPONENT: usize)
        (simd_unit: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit)
        (serialized: t_Slice u8)
        ->
        true);
    f_gamma1_serialize_post
    =
    (fun
        (v_GAMMA1_EXPONENT: usize)
        (simd_unit: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit)
        (serialized: t_Slice u8)
        (out: t_Slice u8)
        ->
        true);
    f_gamma1_serialize
    =
    (fun
        (v_GAMMA1_EXPONENT: usize)
        (simd_unit: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit)
        (serialized: t_Slice u8)
        ->
        let hax_temp_output, serialized:(Prims.unit & t_Slice u8) =
          (),
          Libcrux_ml_dsa.Simd.Avx2.Encoding.Gamma1.serialize v_GAMMA1_EXPONENT
            simd_unit.Libcrux_ml_dsa.Simd.Avx2.Vector_type.f_coefficients
            serialized
          <:
          (Prims.unit & t_Slice u8)
        in
        serialized);
    f_gamma1_deserialize_pre = (fun (v_GAMMA1_EXPONENT: usize) (serialized: t_Slice u8) -> true);
    f_gamma1_deserialize_post
    =
    (fun
        (v_GAMMA1_EXPONENT: usize)
        (serialized: t_Slice u8)
        (out: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit)
        ->
        true);
    f_gamma1_deserialize
    =
    (fun (v_GAMMA1_EXPONENT: usize) (serialized: t_Slice u8) ->
        Core.Convert.f_into #Libcrux_intrinsics.Avx2_extract.t_Vec256
          #Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit
          #FStar.Tactics.Typeclasses.solve
          (Libcrux_ml_dsa.Simd.Avx2.Encoding.Gamma1.deserialize v_GAMMA1_EXPONENT serialized
            <:
            Libcrux_intrinsics.Avx2_extract.t_Vec256));
    f_commitment_serialize_pre
    =
    (fun
        (simd_unit: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit)
        (serialized: t_Slice u8)
        ->
        true);
    f_commitment_serialize_post
    =
    (fun
        (simd_unit: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit)
        (serialized: t_Slice u8)
        (out: t_Slice u8)
        ->
        true);
    f_commitment_serialize
    =
    (fun
        (simd_unit: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit)
        (serialized: t_Slice u8)
        ->
        let hax_temp_output, serialized:(Prims.unit & t_Slice u8) =
          (),
          Libcrux_ml_dsa.Simd.Avx2.Encoding.Commitment.serialize simd_unit
              .Libcrux_ml_dsa.Simd.Avx2.Vector_type.f_coefficients
            serialized
          <:
          (Prims.unit & t_Slice u8)
        in
        serialized);
    f_error_serialize_pre
    =
    (fun
        (v_ETA: usize)
        (simd_unit: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit)
        (serialized: t_Slice u8)
        ->
        true);
    f_error_serialize_post
    =
    (fun
        (v_ETA: usize)
        (simd_unit: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit)
        (serialized: t_Slice u8)
        (out: t_Slice u8)
        ->
        true);
    f_error_serialize
    =
    (fun
        (v_ETA: usize)
        (simd_unit: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit)
        (serialized: t_Slice u8)
        ->
        let hax_temp_output, serialized:(Prims.unit & t_Slice u8) =
          (),
          Libcrux_ml_dsa.Simd.Avx2.Encoding.Error.serialize v_ETA
            simd_unit.Libcrux_ml_dsa.Simd.Avx2.Vector_type.f_coefficients
            serialized
          <:
          (Prims.unit & t_Slice u8)
        in
        serialized);
    f_error_deserialize_pre = (fun (v_ETA: usize) (serialized: t_Slice u8) -> true);
    f_error_deserialize_post
    =
    (fun
        (v_ETA: usize)
        (serialized: t_Slice u8)
        (out: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit)
        ->
        true);
    f_error_deserialize
    =
    (fun (v_ETA: usize) (serialized: t_Slice u8) ->
        Core.Convert.f_into #Libcrux_intrinsics.Avx2_extract.t_Vec256
          #Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit
          #FStar.Tactics.Typeclasses.solve
          (Libcrux_ml_dsa.Simd.Avx2.Encoding.Error.deserialize v_ETA serialized
            <:
            Libcrux_intrinsics.Avx2_extract.t_Vec256));
    f_t0_serialize_pre
    =
    (fun (simd_unit: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit) -> true);
    f_t0_serialize_post
    =
    (fun
        (simd_unit: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit)
        (out: t_Array u8 (sz 13))
        ->
        true);
    f_t0_serialize
    =
    (fun (simd_unit: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit) ->
        Libcrux_ml_dsa.Simd.Avx2.Encoding.T0.serialize simd_unit
            .Libcrux_ml_dsa.Simd.Avx2.Vector_type.f_coefficients);
    f_t0_deserialize_pre = (fun (serialized: t_Slice u8) -> true);
    f_t0_deserialize_post
    =
    (fun (serialized: t_Slice u8) (out: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit) -> true
    );
    f_t0_deserialize
    =
    (fun (serialized: t_Slice u8) ->
        Core.Convert.f_into #Libcrux_intrinsics.Avx2_extract.t_Vec256
          #Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit
          #FStar.Tactics.Typeclasses.solve
          (Libcrux_ml_dsa.Simd.Avx2.Encoding.T0.deserialize serialized
            <:
            Libcrux_intrinsics.Avx2_extract.t_Vec256));
    f_t1_serialize_pre
    =
    (fun (simd_unit: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit) -> true);
    f_t1_serialize_post
    =
    (fun
        (simd_unit: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit)
        (out: t_Array u8 (sz 10))
        ->
        true);
    f_t1_serialize
    =
    (fun (simd_unit: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit) ->
        Libcrux_ml_dsa.Simd.Avx2.Encoding.T1.serialize simd_unit
            .Libcrux_ml_dsa.Simd.Avx2.Vector_type.f_coefficients);
    f_t1_deserialize_pre = (fun (serialized: t_Slice u8) -> true);
    f_t1_deserialize_post
    =
    (fun (serialized: t_Slice u8) (out: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit) -> true
    );
    f_t1_deserialize
    =
    (fun (serialized: t_Slice u8) ->
        Core.Convert.f_into #Libcrux_intrinsics.Avx2_extract.t_Vec256
          #Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit
          #FStar.Tactics.Typeclasses.solve
          (Libcrux_ml_dsa.Simd.Avx2.Encoding.T1.deserialize serialized
            <:
            Libcrux_intrinsics.Avx2_extract.t_Vec256));
    f_ntt_pre
    =
    (fun (simd_units: t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit (sz 32)) -> true);
    f_ntt_post
    =
    (fun
        (simd_units: t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit (sz 32))
        (out: t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit (sz 32))
        ->
        true);
    f_ntt
    =
    (fun (simd_units: t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit (sz 32)) ->
        let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
          Rust_primitives.Hax.repeat (Libcrux_intrinsics.Avx2_extract.mm256_setzero_si256 ()
              <:
              Libcrux_intrinsics.Avx2_extract.t_Vec256)
            (sz 32)
        in
        let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
          Rust_primitives.Hax.Folds.fold_range (sz 0)
            Libcrux_ml_dsa.Simd.Traits.v_SIMD_UNITS_IN_RING_ELEMENT
            (fun re temp_1_ ->
                let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) = re in
                let _:usize = temp_1_ in
                true)
            re
            (fun re i ->
                let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) = re in
                let i:usize = i in
                Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                  i
                  (simd_units.[ i ] <: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit)
                    .Libcrux_ml_dsa.Simd.Avx2.Vector_type.f_coefficients
                <:
                t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32))
        in
        let result:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
          Libcrux_ml_dsa.Simd.Avx2.Ntt.ntt re
        in
        Core.Array.from_fn #Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit
          (sz 32)
          (fun i ->
              let i:usize = i in
              {
                Libcrux_ml_dsa.Simd.Avx2.Vector_type.f_coefficients
                =
                result.[ i ] <: Libcrux_intrinsics.Avx2_extract.t_Vec256
              }
              <:
              Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit));
    f_invert_ntt_montgomery_pre
    =
    (fun (simd_units: t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit (sz 32)) -> true);
    f_invert_ntt_montgomery_post
    =
    (fun
        (simd_units: t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit (sz 32))
        (out: t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit (sz 32))
        ->
        true);
    f_invert_ntt_montgomery
    =
    fun (simd_units: t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit (sz 32)) ->
      let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
        Rust_primitives.Hax.repeat (Libcrux_intrinsics.Avx2_extract.mm256_setzero_si256 ()
            <:
            Libcrux_intrinsics.Avx2_extract.t_Vec256)
          (sz 32)
      in
      let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
        Rust_primitives.Hax.Folds.fold_range (sz 0)
          Libcrux_ml_dsa.Simd.Traits.v_SIMD_UNITS_IN_RING_ELEMENT
          (fun re temp_1_ ->
              let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) = re in
              let _:usize = temp_1_ in
              true)
          re
          (fun re i ->
              let re:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) = re in
              let i:usize = i in
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize re
                i
                (simd_units.[ i ] <: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit)
                  .Libcrux_ml_dsa.Simd.Avx2.Vector_type.f_coefficients
              <:
              t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32))
      in
      let result:t_Array Libcrux_intrinsics.Avx2_extract.t_Vec256 (sz 32) =
        Libcrux_ml_dsa.Simd.Avx2.Invntt.invert_ntt_montgomery re
      in
      Core.Array.from_fn #Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit
        (sz 32)
        (fun i ->
            let i:usize = i in
            {
              Libcrux_ml_dsa.Simd.Avx2.Vector_type.f_coefficients
              =
              result.[ i ] <: Libcrux_intrinsics.Avx2_extract.t_Vec256
            }
            <:
            Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_AVX2SIMDUnit)
  }
