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
Libcrux_ml_dsa.Simd.Portable.Vector_type.t_PortableSIMDUnit =
  {
    _super_11581440318597584651 = FStar.Tactics.Typeclasses.solve;
    _super_9442900250278684536 = FStar.Tactics.Typeclasses.solve;
    f_Coefficient = t_Array i32 (sz 8);
    f_Coefficient_11316922548682728705 = FStar.Tactics.Typeclasses.solve;
    f_zero_pre = (fun (_: Prims.unit) -> true);
    f_zero_post = (fun (_: Prims.unit) (out: t_Array i32 (sz 8)) -> true);
    f_zero = (fun (_: Prims.unit) -> Libcrux_ml_dsa.Simd.Portable.Vector_type.zero ());
    f_from_coefficient_array_pre = (fun (array: t_Slice i32) (out: t_Array i32 (sz 8)) -> true);
    f_from_coefficient_array_post
    =
    (fun (array: t_Slice i32) (out: t_Array i32 (sz 8)) (out1: t_Array i32 (sz 8)) -> true);
    f_from_coefficient_array
    =
    (fun (array: t_Slice i32) (out: t_Array i32 (sz 8)) ->
        let hax_temp_output, out:(Prims.unit & t_Array i32 (sz 8)) =
          (), Libcrux_ml_dsa.Simd.Portable.Vector_type.from_coefficient_array array out
          <:
          (Prims.unit & t_Array i32 (sz 8))
        in
        out);
    f_to_coefficient_array_pre = (fun (value: t_Array i32 (sz 8)) (out: t_Slice i32) -> true);
    f_to_coefficient_array_post
    =
    (fun (value: t_Array i32 (sz 8)) (out: t_Slice i32) (out1: t_Slice i32) -> true);
    f_to_coefficient_array
    =
    (fun (value: t_Array i32 (sz 8)) (out: t_Slice i32) ->
        let hax_temp_output, out:(Prims.unit & t_Slice i32) =
          (), Libcrux_ml_dsa.Simd.Portable.Vector_type.to_coefficient_array value out
          <:
          (Prims.unit & t_Slice i32)
        in
        out);
    f_add_pre = (fun (lhs: t_Array i32 (sz 8)) (rhs: t_Array i32 (sz 8)) -> true);
    f_add_post
    =
    (fun (lhs: t_Array i32 (sz 8)) (rhs: t_Array i32 (sz 8)) (out: t_Array i32 (sz 8)) -> true);
    f_add
    =
    (fun (lhs: t_Array i32 (sz 8)) (rhs: t_Array i32 (sz 8)) ->
        let hax_temp_output, lhs:(Prims.unit & t_Array i32 (sz 8)) =
          (), Libcrux_ml_dsa.Simd.Portable.Arithmetic.add lhs rhs
          <:
          (Prims.unit & t_Array i32 (sz 8))
        in
        lhs);
    f_subtract_pre = (fun (lhs: t_Array i32 (sz 8)) (rhs: t_Array i32 (sz 8)) -> true);
    f_subtract_post
    =
    (fun (lhs: t_Array i32 (sz 8)) (rhs: t_Array i32 (sz 8)) (out: t_Array i32 (sz 8)) -> true);
    f_subtract
    =
    (fun (lhs: t_Array i32 (sz 8)) (rhs: t_Array i32 (sz 8)) ->
        let hax_temp_output, lhs:(Prims.unit & t_Array i32 (sz 8)) =
          (), Libcrux_ml_dsa.Simd.Portable.Arithmetic.subtract lhs rhs
          <:
          (Prims.unit & t_Array i32 (sz 8))
        in
        lhs);
    f_montgomery_multiply_pre = (fun (lhs: t_Array i32 (sz 8)) (rhs: t_Array i32 (sz 8)) -> true);
    f_montgomery_multiply_post
    =
    (fun (lhs: t_Array i32 (sz 8)) (rhs: t_Array i32 (sz 8)) (out: t_Array i32 (sz 8)) -> true);
    f_montgomery_multiply
    =
    (fun (lhs: t_Array i32 (sz 8)) (rhs: t_Array i32 (sz 8)) ->
        let lhs:t_Array i32 (sz 8) =
          Libcrux_ml_dsa.Simd.Portable.Arithmetic.montgomery_multiply lhs rhs
        in
        lhs);
    f_shift_left_then_reduce_pre = (fun (v_SHIFT_BY: i32) (simd_unit: t_Array i32 (sz 8)) -> true);
    f_shift_left_then_reduce_post
    =
    (fun (v_SHIFT_BY: i32) (simd_unit: t_Array i32 (sz 8)) (out: t_Array i32 (sz 8)) -> true);
    f_shift_left_then_reduce
    =
    (fun (v_SHIFT_BY: i32) (simd_unit: t_Array i32 (sz 8)) ->
        let simd_unit:t_Array i32 (sz 8) =
          Libcrux_ml_dsa.Simd.Portable.Arithmetic.shift_left_then_reduce v_SHIFT_BY simd_unit
        in
        simd_unit);
    f_power2round_pre = (fun (t0: t_Array i32 (sz 8)) (t1: t_Array i32 (sz 8)) -> true);
    f_power2round_post
    =
    (fun
        (t0: t_Array i32 (sz 8))
        (t1: t_Array i32 (sz 8))
        (out: (t_Array i32 (sz 8) & t_Array i32 (sz 8)))
        ->
        true);
    f_power2round
    =
    (fun (t0: t_Array i32 (sz 8)) (t1: t_Array i32 (sz 8)) ->
        let tmp0, tmp1:(t_Array i32 (sz 8) & t_Array i32 (sz 8)) =
          Libcrux_ml_dsa.Simd.Portable.Arithmetic.power2round t0 t1
        in
        let t0:t_Array i32 (sz 8) = tmp0 in
        let t1:t_Array i32 (sz 8) = tmp1 in
        let hax_temp_output:Prims.unit = () in
        t0, t1 <: (t_Array i32 (sz 8) & t_Array i32 (sz 8)));
    f_infinity_norm_exceeds_pre = (fun (simd_unit: t_Array i32 (sz 8)) (bound: i32) -> true);
    f_infinity_norm_exceeds_post
    =
    (fun (simd_unit: t_Array i32 (sz 8)) (bound: i32) (out: bool) -> true);
    f_infinity_norm_exceeds
    =
    (fun (simd_unit: t_Array i32 (sz 8)) (bound: i32) ->
        Libcrux_ml_dsa.Simd.Portable.Arithmetic.infinity_norm_exceeds simd_unit bound);
    f_decompose_pre
    =
    (fun
        (gamma2: Libcrux_ml_dsa.Constants.t_Gamma2)
        (simd_unit: t_Array i32 (sz 8))
        (low: t_Array i32 (sz 8))
        (high: t_Array i32 (sz 8))
        ->
        true);
    f_decompose_post
    =
    (fun
        (gamma2: Libcrux_ml_dsa.Constants.t_Gamma2)
        (simd_unit: t_Array i32 (sz 8))
        (low: t_Array i32 (sz 8))
        (high: t_Array i32 (sz 8))
        (out: (t_Array i32 (sz 8) & t_Array i32 (sz 8)))
        ->
        true);
    f_decompose
    =
    (fun
        (gamma2: Libcrux_ml_dsa.Constants.t_Gamma2)
        (simd_unit: t_Array i32 (sz 8))
        (low: t_Array i32 (sz 8))
        (high: t_Array i32 (sz 8))
        ->
        let tmp0, tmp1:(t_Array i32 (sz 8) & t_Array i32 (sz 8)) =
          Libcrux_ml_dsa.Simd.Portable.Arithmetic.decompose gamma2 simd_unit low high
        in
        let low:t_Array i32 (sz 8) = tmp0 in
        let high:t_Array i32 (sz 8) = tmp1 in
        let hax_temp_output:Prims.unit = () in
        low, high <: (t_Array i32 (sz 8) & t_Array i32 (sz 8)));
    f_compute_hint_pre
    =
    (fun
        (v_GAMMA2: i32)
        (low: t_Array i32 (sz 8))
        (high: t_Array i32 (sz 8))
        (hint: t_Array i32 (sz 8))
        ->
        true);
    f_compute_hint_post
    =
    (fun
        (v_GAMMA2: i32)
        (low: t_Array i32 (sz 8))
        (high: t_Array i32 (sz 8))
        (hint: t_Array i32 (sz 8))
        (out2: (t_Array i32 (sz 8) & usize))
        ->
        true);
    f_compute_hint
    =
    (fun
        (v_GAMMA2: i32)
        (low: t_Array i32 (sz 8))
        (high: t_Array i32 (sz 8))
        (hint: t_Array i32 (sz 8))
        ->
        let tmp0, out1:(t_Array i32 (sz 8) & usize) =
          Libcrux_ml_dsa.Simd.Portable.Arithmetic.compute_hint v_GAMMA2 low high hint
        in
        let hint:t_Array i32 (sz 8) = tmp0 in
        let hax_temp_output:usize = out1 in
        hint, hax_temp_output <: (t_Array i32 (sz 8) & usize));
    f_use_hint_pre
    =
    (fun
        (gamma2: Libcrux_ml_dsa.Constants.t_Gamma2)
        (simd_unit: t_Array i32 (sz 8))
        (hint: t_Array i32 (sz 8))
        ->
        true);
    f_use_hint_post
    =
    (fun
        (gamma2: Libcrux_ml_dsa.Constants.t_Gamma2)
        (simd_unit: t_Array i32 (sz 8))
        (hint: t_Array i32 (sz 8))
        (out: t_Array i32 (sz 8))
        ->
        true);
    f_use_hint
    =
    (fun
        (gamma2: Libcrux_ml_dsa.Constants.t_Gamma2)
        (simd_unit: t_Array i32 (sz 8))
        (hint: t_Array i32 (sz 8))
        ->
        let hax_temp_output, hint:(Prims.unit & t_Array i32 (sz 8)) =
          (), Libcrux_ml_dsa.Simd.Portable.Arithmetic.use_hint gamma2 simd_unit hint
          <:
          (Prims.unit & t_Array i32 (sz 8))
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
    (fun (simd_unit: t_Array i32 (sz 8)) (serialized: t_Slice u8) (gamma1_exponent: usize) -> true);
    f_gamma1_serialize_post
    =
    (fun
        (simd_unit: t_Array i32 (sz 8))
        (serialized: t_Slice u8)
        (gamma1_exponent: usize)
        (out: t_Slice u8)
        ->
        true);
    f_gamma1_serialize
    =
    (fun (simd_unit: t_Array i32 (sz 8)) (serialized: t_Slice u8) (gamma1_exponent: usize) ->
        let hax_temp_output, serialized:(Prims.unit & t_Slice u8) =
          (),
          Libcrux_ml_dsa.Simd.Portable.Encoding.Gamma1.serialize simd_unit
            serialized
            gamma1_exponent
          <:
          (Prims.unit & t_Slice u8)
        in
        serialized);
    f_gamma1_deserialize_pre
    =
    (fun (serialized: t_Slice u8) (out: t_Array i32 (sz 8)) (gamma1_exponent: usize) -> true);
    f_gamma1_deserialize_post
    =
    (fun
        (serialized: t_Slice u8)
        (out: t_Array i32 (sz 8))
        (gamma1_exponent: usize)
        (out1: t_Array i32 (sz 8))
        ->
        true);
    f_gamma1_deserialize
    =
    (fun (serialized: t_Slice u8) (out: t_Array i32 (sz 8)) (gamma1_exponent: usize) ->
        let hax_temp_output, out:(Prims.unit & t_Array i32 (sz 8)) =
          (),
          Libcrux_ml_dsa.Simd.Portable.Encoding.Gamma1.deserialize serialized out gamma1_exponent
          <:
          (Prims.unit & t_Array i32 (sz 8))
        in
        out);
    f_commitment_serialize_pre
    =
    (fun (simd_unit: t_Array i32 (sz 8)) (serialized: t_Slice u8) -> true);
    f_commitment_serialize_post
    =
    (fun (simd_unit: t_Array i32 (sz 8)) (serialized: t_Slice u8) (out: t_Slice u8) -> true);
    f_commitment_serialize
    =
    (fun (simd_unit: t_Array i32 (sz 8)) (serialized: t_Slice u8) ->
        let hax_temp_output, serialized:(Prims.unit & t_Slice u8) =
          (), Libcrux_ml_dsa.Simd.Portable.Encoding.Commitment.serialize simd_unit serialized
          <:
          (Prims.unit & t_Slice u8)
        in
        serialized);
    f_error_serialize_pre
    =
    (fun
        (eta: Libcrux_ml_dsa.Constants.t_Eta)
        (simd_unit: t_Array i32 (sz 8))
        (serialized: t_Slice u8)
        ->
        true);
    f_error_serialize_post
    =
    (fun
        (eta: Libcrux_ml_dsa.Constants.t_Eta)
        (simd_unit: t_Array i32 (sz 8))
        (serialized: t_Slice u8)
        (out: t_Slice u8)
        ->
        true);
    f_error_serialize
    =
    (fun
        (eta: Libcrux_ml_dsa.Constants.t_Eta)
        (simd_unit: t_Array i32 (sz 8))
        (serialized: t_Slice u8)
        ->
        let hax_temp_output, serialized:(Prims.unit & t_Slice u8) =
          (), Libcrux_ml_dsa.Simd.Portable.Encoding.Error.serialize eta simd_unit serialized
          <:
          (Prims.unit & t_Slice u8)
        in
        serialized);
    f_error_deserialize_pre
    =
    (fun (eta: Libcrux_ml_dsa.Constants.t_Eta) (serialized: t_Slice u8) (out: t_Array i32 (sz 8)) ->
        true);
    f_error_deserialize_post
    =
    (fun
        (eta: Libcrux_ml_dsa.Constants.t_Eta)
        (serialized: t_Slice u8)
        (out: t_Array i32 (sz 8))
        (out1: t_Array i32 (sz 8))
        ->
        true);
    f_error_deserialize
    =
    (fun (eta: Libcrux_ml_dsa.Constants.t_Eta) (serialized: t_Slice u8) (out: t_Array i32 (sz 8)) ->
        let out:t_Array i32 (sz 8) =
          Libcrux_ml_dsa.Simd.Portable.Encoding.Error.deserialize eta serialized out
        in
        out);
    f_t0_serialize_pre = (fun (simd_unit: t_Array i32 (sz 8)) (out: t_Slice u8) -> true);
    f_t0_serialize_post
    =
    (fun (simd_unit: t_Array i32 (sz 8)) (out: t_Slice u8) (out1: t_Slice u8) -> true);
    f_t0_serialize
    =
    (fun (simd_unit: t_Array i32 (sz 8)) (out: t_Slice u8) ->
        let hax_temp_output, out:(Prims.unit & t_Slice u8) =
          (), Libcrux_ml_dsa.Simd.Portable.Encoding.T0.serialize simd_unit out
          <:
          (Prims.unit & t_Slice u8)
        in
        out);
    f_t0_deserialize_pre = (fun (serialized: t_Slice u8) (out: t_Array i32 (sz 8)) -> true);
    f_t0_deserialize_post
    =
    (fun (serialized: t_Slice u8) (out: t_Array i32 (sz 8)) (out1: t_Array i32 (sz 8)) -> true);
    f_t0_deserialize
    =
    (fun (serialized: t_Slice u8) (out: t_Array i32 (sz 8)) ->
        let hax_temp_output, out:(Prims.unit & t_Array i32 (sz 8)) =
          (), Libcrux_ml_dsa.Simd.Portable.Encoding.T0.deserialize serialized out
          <:
          (Prims.unit & t_Array i32 (sz 8))
        in
        out);
    f_t1_serialize_pre = (fun (simd_unit: t_Array i32 (sz 8)) (out: t_Slice u8) -> true);
    f_t1_serialize_post
    =
    (fun (simd_unit: t_Array i32 (sz 8)) (out: t_Slice u8) (out1: t_Slice u8) -> true);
    f_t1_serialize
    =
    (fun (simd_unit: t_Array i32 (sz 8)) (out: t_Slice u8) ->
        let out:t_Slice u8 = Libcrux_ml_dsa.Simd.Portable.Encoding.T1.serialize simd_unit out in
        out);
    f_t1_deserialize_pre = (fun (serialized: t_Slice u8) (out: t_Array i32 (sz 8)) -> true);
    f_t1_deserialize_post
    =
    (fun (serialized: t_Slice u8) (out: t_Array i32 (sz 8)) (out1: t_Array i32 (sz 8)) -> true);
    f_t1_deserialize
    =
    (fun (serialized: t_Slice u8) (out: t_Array i32 (sz 8)) ->
        let out:t_Array i32 (sz 8) =
          Libcrux_ml_dsa.Simd.Portable.Encoding.T1.deserialize serialized out
        in
        out);
    f_ntt_pre = (fun (simd_units: t_Array (t_Array i32 (sz 8)) (sz 32)) -> true);
    f_ntt_post
    =
    (fun
        (simd_units: t_Array (t_Array i32 (sz 8)) (sz 32))
        (out: t_Array (t_Array i32 (sz 8)) (sz 32))
        ->
        true);
    f_ntt
    =
    (fun (simd_units: t_Array (t_Array i32 (sz 8)) (sz 32)) ->
        let hax_temp_output, simd_units:(Prims.unit & t_Array (t_Array i32 (sz 8)) (sz 32)) =
          (), Libcrux_ml_dsa.Simd.Portable.Ntt.ntt simd_units
          <:
          (Prims.unit & t_Array (t_Array i32 (sz 8)) (sz 32))
        in
        simd_units);
    f_invert_ntt_montgomery_pre = (fun (simd_units: t_Array (t_Array i32 (sz 8)) (sz 32)) -> true);
    f_invert_ntt_montgomery_post
    =
    (fun
        (simd_units: t_Array (t_Array i32 (sz 8)) (sz 32))
        (out: t_Array (t_Array i32 (sz 8)) (sz 32))
        ->
        true);
    f_invert_ntt_montgomery
    =
    fun (simd_units: t_Array (t_Array i32 (sz 8)) (sz 32)) ->
      let hax_temp_output, simd_units:(Prims.unit & t_Array (t_Array i32 (sz 8)) (sz 32)) =
        (), Libcrux_ml_dsa.Simd.Portable.Invntt.invert_ntt_montgomery simd_units
        <:
        (Prims.unit & t_Array (t_Array i32 (sz 8)) (sz 32))
      in
      simd_units
  }
