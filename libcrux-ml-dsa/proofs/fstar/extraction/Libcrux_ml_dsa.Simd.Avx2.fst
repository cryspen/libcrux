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
let impl: Libcrux_ml_dsa.Simd.Traits.t_Operations Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 =
  {
    _super_13011033735201511749 = FStar.Tactics.Typeclasses.solve;
    _super_9529721400157967266 = FStar.Tactics.Typeclasses.solve;
    f_zero_pre = (fun (_: Prims.unit) -> true);
    f_zero_post = (fun (_: Prims.unit) (out: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256) -> true);
    f_zero = (fun (_: Prims.unit) -> Libcrux_ml_dsa.Simd.Avx2.Vector_type.zero ());
    f_from_coefficient_array_pre
    =
    (fun (coefficient_array: t_Slice i32) (out: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256) ->
        true);
    f_from_coefficient_array_post
    =
    (fun
        (coefficient_array: t_Slice i32)
        (out: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
        (out1: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
        ->
        true);
    f_from_coefficient_array
    =
    (fun (coefficient_array: t_Slice i32) (out: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256) ->
        let out:Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 =
          Libcrux_ml_dsa.Simd.Avx2.Vector_type.from_coefficient_array coefficient_array out
        in
        out);
    f_to_coefficient_array_pre
    =
    (fun (value: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256) (out: t_Slice i32) -> true);
    f_to_coefficient_array_post
    =
    (fun
        (value: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
        (out: t_Slice i32)
        (out1: t_Slice i32)
        ->
        true);
    f_to_coefficient_array
    =
    (fun (value: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256) (out: t_Slice i32) ->
        let out:t_Slice i32 = Libcrux_ml_dsa.Simd.Avx2.Vector_type.to_coefficient_array value out in
        out);
    f_add_pre
    =
    (fun
        (lhs: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
        (rhs: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
        ->
        true);
    f_add_post
    =
    (fun
        (lhs: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
        (rhs: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
        (out: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
        ->
        true);
    f_add
    =
    (fun
        (lhs: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
        (rhs: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
        ->
        let lhs:Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 =
          {
            lhs with
            Libcrux_ml_dsa.Simd.Avx2.Vector_type.f_value
            =
            Libcrux_ml_dsa.Simd.Avx2.Arithmetic.add lhs.Libcrux_ml_dsa.Simd.Avx2.Vector_type.f_value
              rhs.Libcrux_ml_dsa.Simd.Avx2.Vector_type.f_value
          }
          <:
          Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256
        in
        lhs);
    f_subtract_pre
    =
    (fun
        (lhs: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
        (rhs: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
        ->
        true);
    f_subtract_post
    =
    (fun
        (lhs: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
        (rhs: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
        (out: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
        ->
        true);
    f_subtract
    =
    (fun
        (lhs: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
        (rhs: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
        ->
        let lhs:Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 =
          {
            lhs with
            Libcrux_ml_dsa.Simd.Avx2.Vector_type.f_value
            =
            Libcrux_ml_dsa.Simd.Avx2.Arithmetic.subtract lhs
                .Libcrux_ml_dsa.Simd.Avx2.Vector_type.f_value
              rhs.Libcrux_ml_dsa.Simd.Avx2.Vector_type.f_value
          }
          <:
          Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256
        in
        lhs);
    f_montgomery_multiply_pre
    =
    (fun
        (lhs: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
        (rhs: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
        ->
        true);
    f_montgomery_multiply_post
    =
    (fun
        (lhs: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
        (rhs: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
        (out: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
        ->
        true);
    f_montgomery_multiply
    =
    (fun
        (lhs: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
        (rhs: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
        ->
        let lhs:Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 =
          {
            lhs with
            Libcrux_ml_dsa.Simd.Avx2.Vector_type.f_value
            =
            Libcrux_ml_dsa.Simd.Avx2.Arithmetic.montgomery_multiply lhs
                .Libcrux_ml_dsa.Simd.Avx2.Vector_type.f_value
              rhs.Libcrux_ml_dsa.Simd.Avx2.Vector_type.f_value
          }
          <:
          Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256
        in
        lhs);
    f_shift_left_then_reduce_pre
    =
    (fun (v_SHIFT_BY: i32) (simd_unit: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256) -> true);
    f_shift_left_then_reduce_post
    =
    (fun
        (v_SHIFT_BY: i32)
        (simd_unit: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
        (out: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
        ->
        true);
    f_shift_left_then_reduce
    =
    (fun (v_SHIFT_BY: i32) (simd_unit: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256) ->
        let simd_unit:Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 =
          {
            simd_unit with
            Libcrux_ml_dsa.Simd.Avx2.Vector_type.f_value
            =
            Libcrux_ml_dsa.Simd.Avx2.Arithmetic.shift_left_then_reduce v_SHIFT_BY
              simd_unit.Libcrux_ml_dsa.Simd.Avx2.Vector_type.f_value
          }
          <:
          Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256
        in
        simd_unit);
    f_power2round_pre
    =
    (fun
        (t0: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
        (t1: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
        ->
        true);
    f_power2round_post
    =
    (fun
        (t0: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
        (t1: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
        (out:
          (Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 &
            Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256))
        ->
        true);
    f_power2round
    =
    (fun
        (t0: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
        (t1: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
        ->
        let tmp0, tmp1:(Libcrux_intrinsics.Avx2_extract.t_Vec256 &
          Libcrux_intrinsics.Avx2_extract.t_Vec256) =
          Libcrux_ml_dsa.Simd.Avx2.Arithmetic.power2round t0
              .Libcrux_ml_dsa.Simd.Avx2.Vector_type.f_value
            t1.Libcrux_ml_dsa.Simd.Avx2.Vector_type.f_value
        in
        let t0:Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 =
          { t0 with Libcrux_ml_dsa.Simd.Avx2.Vector_type.f_value = tmp0 }
          <:
          Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256
        in
        let t1:Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 =
          { t1 with Libcrux_ml_dsa.Simd.Avx2.Vector_type.f_value = tmp1 }
          <:
          Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256
        in
        let _:Prims.unit = () in
        t0, t1
        <:
        (Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 &
          Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256));
    f_infinity_norm_exceeds_pre
    =
    (fun (simd_unit: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256) (bound: i32) -> true);
    f_infinity_norm_exceeds_post
    =
    (fun (simd_unit: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256) (bound: i32) (out: bool) -> true
    );
    f_infinity_norm_exceeds
    =
    (fun (simd_unit: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256) (bound: i32) ->
        Libcrux_ml_dsa.Simd.Avx2.Arithmetic.infinity_norm_exceeds simd_unit
            .Libcrux_ml_dsa.Simd.Avx2.Vector_type.f_value
          bound);
    f_decompose_pre
    =
    (fun
        (gamma2: i32)
        (simd_unit: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
        (low: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
        (high: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
        ->
        true);
    f_decompose_post
    =
    (fun
        (gamma2: i32)
        (simd_unit: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
        (low: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
        (high: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
        (out:
          (Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 &
            Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256))
        ->
        true);
    f_decompose
    =
    (fun
        (gamma2: i32)
        (simd_unit: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
        (low: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
        (high: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
        ->
        let tmp0, tmp1:(Libcrux_intrinsics.Avx2_extract.t_Vec256 &
          Libcrux_intrinsics.Avx2_extract.t_Vec256) =
          Libcrux_ml_dsa.Simd.Avx2.Arithmetic.decompose gamma2
            simd_unit.Libcrux_ml_dsa.Simd.Avx2.Vector_type.f_value
            low.Libcrux_ml_dsa.Simd.Avx2.Vector_type.f_value
            high.Libcrux_ml_dsa.Simd.Avx2.Vector_type.f_value
        in
        let low:Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 =
          { low with Libcrux_ml_dsa.Simd.Avx2.Vector_type.f_value = tmp0 }
          <:
          Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256
        in
        let high:Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 =
          { high with Libcrux_ml_dsa.Simd.Avx2.Vector_type.f_value = tmp1 }
          <:
          Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256
        in
        let _:Prims.unit = () in
        low, high
        <:
        (Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 &
          Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256));
    f_compute_hint_pre
    =
    (fun
        (low: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
        (high: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
        (gamma2: i32)
        (hint: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
        ->
        true);
    f_compute_hint_post
    =
    (fun
        (low: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
        (high: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
        (gamma2: i32)
        (hint: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
        (out2: (Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 & usize))
        ->
        true);
    f_compute_hint
    =
    (fun
        (low: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
        (high: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
        (gamma2: i32)
        (hint: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
        ->
        let tmp0, out1:(Libcrux_intrinsics.Avx2_extract.t_Vec256 & usize) =
          Libcrux_ml_dsa.Simd.Avx2.Arithmetic.compute_hint low
              .Libcrux_ml_dsa.Simd.Avx2.Vector_type.f_value
            high.Libcrux_ml_dsa.Simd.Avx2.Vector_type.f_value
            gamma2
            hint.Libcrux_ml_dsa.Simd.Avx2.Vector_type.f_value
        in
        let hint:Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 =
          { hint with Libcrux_ml_dsa.Simd.Avx2.Vector_type.f_value = tmp0 }
          <:
          Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256
        in
        let hax_temp_output:usize = out1 in
        hint, hax_temp_output <: (Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 & usize));
    f_uuse_hint_pre
    =
    (fun
        (gamma2: i32)
        (simd_unit: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
        (hint: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
        ->
        true);
    f_uuse_hint_post
    =
    (fun
        (gamma2: i32)
        (simd_unit: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
        (hint: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
        (out: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
        ->
        true);
    f_uuse_hint
    =
    (fun
        (gamma2: i32)
        (simd_unit: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
        (hint: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
        ->
        let hint:Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 =
          {
            hint with
            Libcrux_ml_dsa.Simd.Avx2.Vector_type.f_value
            =
            Libcrux_ml_dsa.Simd.Avx2.Arithmetic.uuse_hint gamma2
              simd_unit.Libcrux_ml_dsa.Simd.Avx2.Vector_type.f_value
              hint.Libcrux_ml_dsa.Simd.Avx2.Vector_type.f_value
          }
          <:
          Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256
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
    f_rejection_sample_less_than_eta_equals_2__pre
    =
    (fun (randomness: t_Slice u8) (out: t_Slice i32) -> true);
    f_rejection_sample_less_than_eta_equals_2__post
    =
    (fun (randomness: t_Slice u8) (out: t_Slice i32) (out2: (t_Slice i32 & usize)) -> true);
    f_rejection_sample_less_than_eta_equals_2_
    =
    (fun (randomness: t_Slice u8) (out: t_Slice i32) ->
        let tmp0, out1:(t_Slice i32 & usize) =
          Libcrux_ml_dsa.Simd.Avx2.Rejection_sample.Less_than_eta.sample (mk_usize 2) randomness out
        in
        let out:t_Slice i32 = tmp0 in
        let hax_temp_output:usize = out1 in
        out, hax_temp_output <: (t_Slice i32 & usize));
    f_rejection_sample_less_than_eta_equals_4__pre
    =
    (fun (randomness: t_Slice u8) (out: t_Slice i32) -> true);
    f_rejection_sample_less_than_eta_equals_4__post
    =
    (fun (randomness: t_Slice u8) (out: t_Slice i32) (out2: (t_Slice i32 & usize)) -> true);
    f_rejection_sample_less_than_eta_equals_4_
    =
    (fun (randomness: t_Slice u8) (out: t_Slice i32) ->
        let tmp0, out1:(t_Slice i32 & usize) =
          Libcrux_ml_dsa.Simd.Avx2.Rejection_sample.Less_than_eta.sample (mk_usize 4) randomness out
        in
        let out:t_Slice i32 = tmp0 in
        let hax_temp_output:usize = out1 in
        out, hax_temp_output <: (t_Slice i32 & usize));
    f_gamma1_serialize_pre
    =
    (fun
        (simd_unit: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
        (serialized: t_Slice u8)
        (gamma1_exponent: usize)
        ->
        true);
    f_gamma1_serialize_post
    =
    (fun
        (simd_unit: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
        (serialized: t_Slice u8)
        (gamma1_exponent: usize)
        (out: t_Slice u8)
        ->
        true);
    f_gamma1_serialize
    =
    (fun
        (simd_unit: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
        (serialized: t_Slice u8)
        (gamma1_exponent: usize)
        ->
        let serialized:t_Slice u8 =
          Libcrux_ml_dsa.Simd.Avx2.Encoding.Gamma1.serialize simd_unit
              .Libcrux_ml_dsa.Simd.Avx2.Vector_type.f_value
            serialized
            gamma1_exponent
        in
        serialized);
    f_gamma1_deserialize_pre
    =
    (fun
        (serialized: t_Slice u8)
        (out: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
        (gamma1_exponent: usize)
        ->
        true);
    f_gamma1_deserialize_post
    =
    (fun
        (serialized: t_Slice u8)
        (out: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
        (gamma1_exponent: usize)
        (out1: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
        ->
        true);
    f_gamma1_deserialize
    =
    (fun
        (serialized: t_Slice u8)
        (out: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
        (gamma1_exponent: usize)
        ->
        let out:Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 =
          {
            out with
            Libcrux_ml_dsa.Simd.Avx2.Vector_type.f_value
            =
            Libcrux_ml_dsa.Simd.Avx2.Encoding.Gamma1.deserialize serialized
              out.Libcrux_ml_dsa.Simd.Avx2.Vector_type.f_value
              gamma1_exponent
          }
          <:
          Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256
        in
        out);
    f_commitment_serialize_pre
    =
    (fun (simd_unit: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256) (serialized: t_Slice u8) -> true
    );
    f_commitment_serialize_post
    =
    (fun
        (simd_unit: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
        (serialized: t_Slice u8)
        (out: t_Slice u8)
        ->
        true);
    f_commitment_serialize
    =
    (fun (simd_unit: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256) (serialized: t_Slice u8) ->
        let serialized:t_Slice u8 =
          Libcrux_ml_dsa.Simd.Avx2.Encoding.Commitment.serialize simd_unit
              .Libcrux_ml_dsa.Simd.Avx2.Vector_type.f_value
            serialized
        in
        serialized);
    f_error_serialize_pre
    =
    (fun
        (eta: Libcrux_ml_dsa.Constants.t_Eta)
        (simd_unit: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
        (serialized: t_Slice u8)
        ->
        true);
    f_error_serialize_post
    =
    (fun
        (eta: Libcrux_ml_dsa.Constants.t_Eta)
        (simd_unit: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
        (serialized: t_Slice u8)
        (out: t_Slice u8)
        ->
        true);
    f_error_serialize
    =
    (fun
        (eta: Libcrux_ml_dsa.Constants.t_Eta)
        (simd_unit: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
        (serialized: t_Slice u8)
        ->
        let serialized:t_Slice u8 =
          Libcrux_ml_dsa.Simd.Avx2.Encoding.Error.serialize eta
            simd_unit.Libcrux_ml_dsa.Simd.Avx2.Vector_type.f_value
            serialized
        in
        serialized);
    f_error_deserialize_pre
    =
    (fun
        (eta: Libcrux_ml_dsa.Constants.t_Eta)
        (serialized: t_Slice u8)
        (out: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
        ->
        true);
    f_error_deserialize_post
    =
    (fun
        (eta: Libcrux_ml_dsa.Constants.t_Eta)
        (serialized: t_Slice u8)
        (out: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
        (out1: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
        ->
        true);
    f_error_deserialize
    =
    (fun
        (eta: Libcrux_ml_dsa.Constants.t_Eta)
        (serialized: t_Slice u8)
        (out: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
        ->
        let out:Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 =
          {
            out with
            Libcrux_ml_dsa.Simd.Avx2.Vector_type.f_value
            =
            Libcrux_ml_dsa.Simd.Avx2.Encoding.Error.deserialize eta
              serialized
              out.Libcrux_ml_dsa.Simd.Avx2.Vector_type.f_value
          }
          <:
          Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256
        in
        out);
    f_t0_serialize_pre
    =
    (fun (simd_unit: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256) (out: t_Slice u8) -> true);
    f_t0_serialize_post
    =
    (fun
        (simd_unit: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
        (out: t_Slice u8)
        (out1: t_Slice u8)
        ->
        true);
    f_t0_serialize
    =
    (fun (simd_unit: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256) (out: t_Slice u8) ->
        let out:t_Slice u8 =
          Libcrux_ml_dsa.Simd.Avx2.Encoding.T0.serialize simd_unit
              .Libcrux_ml_dsa.Simd.Avx2.Vector_type.f_value
            out
        in
        out);
    f_t0_deserialize_pre
    =
    (fun (serialized: t_Slice u8) (out: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256) -> true);
    f_t0_deserialize_post
    =
    (fun
        (serialized: t_Slice u8)
        (out: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
        (out1: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
        ->
        true);
    f_t0_deserialize
    =
    (fun (serialized: t_Slice u8) (out: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256) ->
        let out:Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 =
          {
            out with
            Libcrux_ml_dsa.Simd.Avx2.Vector_type.f_value
            =
            Libcrux_ml_dsa.Simd.Avx2.Encoding.T0.deserialize serialized
              out.Libcrux_ml_dsa.Simd.Avx2.Vector_type.f_value
          }
          <:
          Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256
        in
        out);
    f_t1_serialize_pre
    =
    (fun (simd_unit: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256) (out: t_Slice u8) -> true);
    f_t1_serialize_post
    =
    (fun
        (simd_unit: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
        (out: t_Slice u8)
        (out1: t_Slice u8)
        ->
        true);
    f_t1_serialize
    =
    (fun (simd_unit: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256) (out: t_Slice u8) ->
        let out:t_Slice u8 =
          Libcrux_ml_dsa.Simd.Avx2.Encoding.T1.serialize simd_unit
              .Libcrux_ml_dsa.Simd.Avx2.Vector_type.f_value
            out
        in
        out);
    f_t1_deserialize_pre
    =
    (fun (serialized: t_Slice u8) (out: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256) -> true);
    f_t1_deserialize_post
    =
    (fun
        (serialized: t_Slice u8)
        (out: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
        (out1: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256)
        ->
        true);
    f_t1_deserialize
    =
    (fun (serialized: t_Slice u8) (out: Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256) ->
        let out:Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 =
          {
            out with
            Libcrux_ml_dsa.Simd.Avx2.Vector_type.f_value
            =
            Libcrux_ml_dsa.Simd.Avx2.Encoding.T1.deserialize serialized
              out.Libcrux_ml_dsa.Simd.Avx2.Vector_type.f_value
          }
          <:
          Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256
        in
        out);
    f_ntt_pre
    =
    (fun (simd_units: t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32)) -> true);
    f_ntt_post
    =
    (fun
        (simd_units: t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32))
        (out: t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32))
        ->
        true);
    f_ntt
    =
    (fun (simd_units: t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32)) ->
        let simd_units:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
          Libcrux_ml_dsa.Simd.Avx2.Ntt.ntt simd_units
        in
        simd_units);
    f_invert_ntt_montgomery_pre
    =
    (fun (simd_units: t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32)) -> true);
    f_invert_ntt_montgomery_post
    =
    (fun
        (simd_units: t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32))
        (out: t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32))
        ->
        true);
    f_invert_ntt_montgomery
    =
    fun (simd_units: t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32)) ->
      let simd_units:t_Array Libcrux_ml_dsa.Simd.Avx2.Vector_type.t_Vec256 (mk_usize 32) =
        Libcrux_ml_dsa.Simd.Avx2.Invntt.invert_ntt_montgomery simd_units
      in
      simd_units
  }
