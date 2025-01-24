module Libcrux_ml_dsa.Simd.Portable
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_dsa.Simd.Portable.Vector_type in
  ()

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: Libcrux_ml_dsa.Simd.Traits.t_Operations
Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
  {
    _super_13011033735201511749 = FStar.Tactics.Typeclasses.solve;
    _super_9529721400157967266 = FStar.Tactics.Typeclasses.solve;
    f_zero_pre = (fun (_: Prims.unit) -> true);
    f_zero_post
    =
    (fun (_: Prims.unit) (out: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients) -> true);
    f_zero = (fun (_: Prims.unit) -> Libcrux_ml_dsa.Simd.Portable.Vector_type.zero ());
    f_from_coefficient_array_pre
    =
    (fun (array: t_Slice i32) (out: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients) -> true
    );
    f_from_coefficient_array_post
    =
    (fun
        (array: t_Slice i32)
        (out: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
        (out1: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
        ->
        true);
    f_from_coefficient_array
    =
    (fun (array: t_Slice i32) (out: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients) ->
        let out:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
          Libcrux_ml_dsa.Simd.Portable.Vector_type.from_coefficient_array array out
        in
        out);
    f_to_coefficient_array_pre
    =
    (fun (value: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients) (out: t_Slice i32) -> true
    );
    f_to_coefficient_array_post
    =
    (fun
        (value: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
        (out: t_Slice i32)
        (out1: t_Slice i32)
        ->
        true);
    f_to_coefficient_array
    =
    (fun (value: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients) (out: t_Slice i32) ->
        let out:t_Slice i32 =
          Libcrux_ml_dsa.Simd.Portable.Vector_type.to_coefficient_array value out
        in
        out);
    f_add_pre
    =
    (fun
        (lhs: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
        (rhs: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
        ->
        true);
    f_add_post
    =
    (fun
        (lhs: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
        (rhs: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
        (out: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
        ->
        true);
    f_add
    =
    (fun
        (lhs: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
        (rhs: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
        ->
        let lhs:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
          Libcrux_ml_dsa.Simd.Portable.Arithmetic.add lhs rhs
        in
        lhs);
    f_subtract_pre
    =
    (fun
        (lhs: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
        (rhs: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
        ->
        true);
    f_subtract_post
    =
    (fun
        (lhs: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
        (rhs: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
        (out: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
        ->
        true);
    f_subtract
    =
    (fun
        (lhs: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
        (rhs: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
        ->
        let lhs:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
          Libcrux_ml_dsa.Simd.Portable.Arithmetic.subtract lhs rhs
        in
        lhs);
    f_montgomery_multiply_pre
    =
    (fun
        (lhs: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
        (rhs: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
        ->
        true);
    f_montgomery_multiply_post
    =
    (fun
        (lhs: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
        (rhs: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
        (out: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
        ->
        true);
    f_montgomery_multiply
    =
    (fun
        (lhs: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
        (rhs: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
        ->
        let lhs:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
          Libcrux_ml_dsa.Simd.Portable.Arithmetic.montgomery_multiply lhs rhs
        in
        lhs);
    f_shift_left_then_reduce_pre
    =
    (fun (v_SHIFT_BY: i32) (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients) ->
        true);
    f_shift_left_then_reduce_post
    =
    (fun
        (v_SHIFT_BY: i32)
        (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
        (out: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
        ->
        true);
    f_shift_left_then_reduce
    =
    (fun (v_SHIFT_BY: i32) (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients) ->
        let simd_unit:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
          Libcrux_ml_dsa.Simd.Portable.Arithmetic.shift_left_then_reduce v_SHIFT_BY simd_unit
        in
        simd_unit);
    f_power2round_pre
    =
    (fun
        (t0: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
        (t1: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
        ->
        true);
    f_power2round_post
    =
    (fun
        (t0: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
        (t1: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
        (out:
          (Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients &
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients))
        ->
        true);
    f_power2round
    =
    (fun
        (t0: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
        (t1: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
        ->
        let tmp0, tmp1:(Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients &
          Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients) =
          Libcrux_ml_dsa.Simd.Portable.Arithmetic.power2round t0 t1
        in
        let t0:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients = tmp0 in
        let t1:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients = tmp1 in
        let _:Prims.unit = () in
        t0, t1
        <:
        (Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients &
          Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients));
    f_infinity_norm_exceeds_pre
    =
    (fun (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients) (bound: i32) -> true);
    f_infinity_norm_exceeds_post
    =
    (fun
        (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
        (bound: i32)
        (out: bool)
        ->
        true);
    f_infinity_norm_exceeds
    =
    (fun (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients) (bound: i32) ->
        Libcrux_ml_dsa.Simd.Portable.Arithmetic.infinity_norm_exceeds simd_unit bound);
    f_decompose_pre
    =
    (fun
        (gamma2: i32)
        (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
        (low: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
        (high: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
        ->
        true);
    f_decompose_post
    =
    (fun
        (gamma2: i32)
        (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
        (low: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
        (high: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
        (out:
          (Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients &
            Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients))
        ->
        true);
    f_decompose
    =
    (fun
        (gamma2: i32)
        (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
        (low: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
        (high: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
        ->
        let tmp0, tmp1:(Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients &
          Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients) =
          Libcrux_ml_dsa.Simd.Portable.Arithmetic.decompose gamma2 simd_unit low high
        in
        let low:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients = tmp0 in
        let high:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients = tmp1 in
        let _:Prims.unit = () in
        low, high
        <:
        (Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients &
          Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients));
    f_compute_hint_pre
    =
    (fun
        (low: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
        (high: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
        (gamma2: i32)
        (hint: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
        ->
        true);
    f_compute_hint_post
    =
    (fun
        (low: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
        (high: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
        (gamma2: i32)
        (hint: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
        (out2: (Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients & usize))
        ->
        true);
    f_compute_hint
    =
    (fun
        (low: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
        (high: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
        (gamma2: i32)
        (hint: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
        ->
        let tmp0, out1:(Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients & usize) =
          Libcrux_ml_dsa.Simd.Portable.Arithmetic.compute_hint low high gamma2 hint
        in
        let hint:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients = tmp0 in
        let hax_temp_output:usize = out1 in
        hint, hax_temp_output <: (Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients & usize));
    f_use_hint_pre
    =
    (fun
        (gamma2: i32)
        (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
        (hint: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
        ->
        true);
    f_use_hint_post
    =
    (fun
        (gamma2: i32)
        (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
        (hint: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
        (out: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
        ->
        true);
    f_use_hint
    =
    (fun
        (gamma2: i32)
        (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
        (hint: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
        ->
        let hint:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
          Libcrux_ml_dsa.Simd.Portable.Arithmetic.use_hint gamma2 simd_unit hint
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
          Libcrux_ml_dsa.Simd.Portable.Sample.rejection_sample_less_than_field_modulus randomness
            out
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
          Libcrux_ml_dsa.Simd.Portable.Sample.rejection_sample_less_than_eta_equals_2_ randomness
            out
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
          Libcrux_ml_dsa.Simd.Portable.Sample.rejection_sample_less_than_eta_equals_4_ randomness
            out
        in
        let out:t_Slice i32 = tmp0 in
        let hax_temp_output:usize = out1 in
        out, hax_temp_output <: (t_Slice i32 & usize));
    f_gamma1_serialize_pre
    =
    (fun
        (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
        (serialized: t_Slice u8)
        (gamma1_exponent: usize)
        ->
        true);
    f_gamma1_serialize_post
    =
    (fun
        (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
        (serialized: t_Slice u8)
        (gamma1_exponent: usize)
        (out: t_Slice u8)
        ->
        true);
    f_gamma1_serialize
    =
    (fun
        (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
        (serialized: t_Slice u8)
        (gamma1_exponent: usize)
        ->
        let serialized:t_Slice u8 =
          Libcrux_ml_dsa.Simd.Portable.Encoding.Gamma1.serialize simd_unit
            serialized
            gamma1_exponent
        in
        serialized);
    f_gamma1_deserialize_pre
    =
    (fun
        (serialized: t_Slice u8)
        (out: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
        (gamma1_exponent: usize)
        ->
        true);
    f_gamma1_deserialize_post
    =
    (fun
        (serialized: t_Slice u8)
        (out: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
        (gamma1_exponent: usize)
        (out1: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
        ->
        true);
    f_gamma1_deserialize
    =
    (fun
        (serialized: t_Slice u8)
        (out: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
        (gamma1_exponent: usize)
        ->
        let out:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
          Libcrux_ml_dsa.Simd.Portable.Encoding.Gamma1.deserialize serialized out gamma1_exponent
        in
        out);
    f_commitment_serialize_pre
    =
    (fun
        (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
        (serialized: t_Slice u8)
        ->
        true);
    f_commitment_serialize_post
    =
    (fun
        (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
        (serialized: t_Slice u8)
        (out: t_Slice u8)
        ->
        true);
    f_commitment_serialize
    =
    (fun
        (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
        (serialized: t_Slice u8)
        ->
        let serialized:t_Slice u8 =
          Libcrux_ml_dsa.Simd.Portable.Encoding.Commitment.serialize simd_unit serialized
        in
        serialized);
    f_error_serialize_pre
    =
    (fun
        (eta: Libcrux_ml_dsa.Constants.t_Eta)
        (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
        (serialized: t_Slice u8)
        ->
        true);
    f_error_serialize_post
    =
    (fun
        (eta: Libcrux_ml_dsa.Constants.t_Eta)
        (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
        (serialized: t_Slice u8)
        (out: t_Slice u8)
        ->
        true);
    f_error_serialize
    =
    (fun
        (eta: Libcrux_ml_dsa.Constants.t_Eta)
        (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
        (serialized: t_Slice u8)
        ->
        let serialized:t_Slice u8 =
          Libcrux_ml_dsa.Simd.Portable.Encoding.Error.serialize eta simd_unit serialized
        in
        serialized);
    f_error_deserialize_pre
    =
    (fun
        (eta: Libcrux_ml_dsa.Constants.t_Eta)
        (serialized: t_Slice u8)
        (out: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
        ->
        true);
    f_error_deserialize_post
    =
    (fun
        (eta: Libcrux_ml_dsa.Constants.t_Eta)
        (serialized: t_Slice u8)
        (out: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
        (out1: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
        ->
        true);
    f_error_deserialize
    =
    (fun
        (eta: Libcrux_ml_dsa.Constants.t_Eta)
        (serialized: t_Slice u8)
        (out: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
        ->
        let out:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
          Libcrux_ml_dsa.Simd.Portable.Encoding.Error.deserialize eta serialized out
        in
        out);
    f_t0_serialize_pre
    =
    (fun (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients) (out: t_Slice u8) ->
        true);
    f_t0_serialize_post
    =
    (fun
        (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
        (out: t_Slice u8)
        (out1: t_Slice u8)
        ->
        true);
    f_t0_serialize
    =
    (fun (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients) (out: t_Slice u8) ->
        let out:t_Slice u8 = Libcrux_ml_dsa.Simd.Portable.Encoding.T0.serialize simd_unit out in
        out);
    f_t0_deserialize_pre
    =
    (fun (serialized: t_Slice u8) (out: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients) ->
        true);
    f_t0_deserialize_post
    =
    (fun
        (serialized: t_Slice u8)
        (out: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
        (out1: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
        ->
        true);
    f_t0_deserialize
    =
    (fun (serialized: t_Slice u8) (out: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients) ->
        let out:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
          Libcrux_ml_dsa.Simd.Portable.Encoding.T0.deserialize serialized out
        in
        out);
    f_t1_serialize_pre
    =
    (fun (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients) (out: t_Slice u8) ->
        true);
    f_t1_serialize_post
    =
    (fun
        (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
        (out: t_Slice u8)
        (out1: t_Slice u8)
        ->
        true);
    f_t1_serialize
    =
    (fun (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients) (out: t_Slice u8) ->
        let out:t_Slice u8 = Libcrux_ml_dsa.Simd.Portable.Encoding.T1.serialize simd_unit out in
        out);
    f_t1_deserialize_pre
    =
    (fun (serialized: t_Slice u8) (out: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients) ->
        true);
    f_t1_deserialize_post
    =
    (fun
        (serialized: t_Slice u8)
        (out: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
        (out1: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
        ->
        true);
    f_t1_deserialize
    =
    (fun (serialized: t_Slice u8) (out: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients) ->
        let out:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
          Libcrux_ml_dsa.Simd.Portable.Encoding.T1.deserialize serialized out
        in
        out);
    f_ntt_pre
    =
    (fun (simd_units: t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (sz 32)) ->
        true);
    f_ntt_post
    =
    (fun
        (simd_units: t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (sz 32))
        (out: t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (sz 32))
        ->
        true);
    f_ntt
    =
    (fun (simd_units: t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (sz 32)) ->
        let simd_units:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (sz 32) =
          Libcrux_ml_dsa.Simd.Portable.Ntt.ntt simd_units
        in
        simd_units);
    f_invert_ntt_montgomery_pre
    =
    (fun (simd_units: t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (sz 32)) ->
        true);
    f_invert_ntt_montgomery_post
    =
    (fun
        (simd_units: t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (sz 32))
        (out: t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (sz 32))
        ->
        true);
    f_invert_ntt_montgomery
    =
    fun (simd_units: t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (sz 32)) ->
      let simd_units:t_Array Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients (sz 32) =
        Libcrux_ml_dsa.Simd.Portable.Invntt.invert_ntt_montgomery simd_units
      in
      simd_units
  }
