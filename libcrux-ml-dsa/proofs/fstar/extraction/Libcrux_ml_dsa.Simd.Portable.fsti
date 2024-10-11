module Libcrux_ml_dsa.Simd.Portable
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

type t_PortableSIMDUnit = { f_coefficients:t_Array i32 (Rust_primitives.mk_usize 8) }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: Libcrux_ml_dsa.Simd.Traits.t_Operations t_PortableSIMDUnit =
  {
    _super_11581440318597584651 = FStar.Tactics.Typeclasses.solve;
    _super_9442900250278684536 = FStar.Tactics.Typeclasses.solve;
    f_ZERO_pre = (fun (_: Prims.unit) -> true);
    f_ZERO_post = (fun (_: Prims.unit) (out: t_PortableSIMDUnit) -> true);
    f_ZERO
    =
    (fun (_: Prims.unit) ->
        {
          f_coefficients
          =
          Rust_primitives.Hax.repeat (Rust_primitives.mk_i32 0) (Rust_primitives.mk_usize 8)
        }
        <:
        t_PortableSIMDUnit);
    f_from_coefficient_array_pre = (fun (array: t_Slice i32) -> true);
    f_from_coefficient_array_post = (fun (array: t_Slice i32) (out: t_PortableSIMDUnit) -> true);
    f_from_coefficient_array
    =
    (fun (array: t_Slice i32) ->
        {
          f_coefficients
          =
          Core.Result.impl__unwrap #(t_Array i32 (Rust_primitives.mk_usize 8))
            #Core.Array.t_TryFromSliceError
            (Core.Convert.f_try_into #(t_Slice i32)
                #(t_Array i32 (Rust_primitives.mk_usize 8))
                #FStar.Tactics.Typeclasses.solve
                (array.[ {
                      Core.Ops.Range.f_start = Rust_primitives.mk_usize 0;
                      Core.Ops.Range.f_end = Rust_primitives.mk_usize 8
                    }
                    <:
                    Core.Ops.Range.t_Range usize ]
                  <:
                  t_Slice i32)
              <:
              Core.Result.t_Result (t_Array i32 (Rust_primitives.mk_usize 8))
                Core.Array.t_TryFromSliceError)
        }
        <:
        t_PortableSIMDUnit);
    f_to_coefficient_array_pre = (fun (self: t_PortableSIMDUnit) -> true);
    f_to_coefficient_array_post
    =
    (fun (self: t_PortableSIMDUnit) (out: t_Array i32 (Rust_primitives.mk_usize 8)) -> true);
    f_to_coefficient_array
    =
    (fun (self: t_PortableSIMDUnit) ->
        Core.Result.impl__unwrap #(t_Array i32 (Rust_primitives.mk_usize 8))
          #Core.Convert.t_Infallible
          (Core.Convert.f_try_into #(t_Array i32 (Rust_primitives.mk_usize 8))
              #(t_Array i32 (Rust_primitives.mk_usize 8))
              #FStar.Tactics.Typeclasses.solve
              self.f_coefficients
            <:
            Core.Result.t_Result (t_Array i32 (Rust_primitives.mk_usize 8))
              Core.Convert.t_Infallible));
    f_add_pre = (fun (lhs: t_PortableSIMDUnit) (rhs: t_PortableSIMDUnit) -> true);
    f_add_post
    =
    (fun (lhs: t_PortableSIMDUnit) (rhs: t_PortableSIMDUnit) (out: t_PortableSIMDUnit) -> true);
    f_add
    =
    (fun (lhs: t_PortableSIMDUnit) (rhs: t_PortableSIMDUnit) ->
        Libcrux_ml_dsa.Simd.Portable.Arithmetic.add lhs rhs);
    f_subtract_pre = (fun (lhs: t_PortableSIMDUnit) (rhs: t_PortableSIMDUnit) -> true);
    f_subtract_post
    =
    (fun (lhs: t_PortableSIMDUnit) (rhs: t_PortableSIMDUnit) (out: t_PortableSIMDUnit) -> true);
    f_subtract
    =
    (fun (lhs: t_PortableSIMDUnit) (rhs: t_PortableSIMDUnit) ->
        Libcrux_ml_dsa.Simd.Portable.Arithmetic.subtract lhs rhs);
    f_montgomery_multiply_by_constant_pre = (fun (simd_unit: t_PortableSIMDUnit) (c: i32) -> true);
    f_montgomery_multiply_by_constant_post
    =
    (fun (simd_unit: t_PortableSIMDUnit) (c: i32) (out: t_PortableSIMDUnit) -> true);
    f_montgomery_multiply_by_constant
    =
    (fun (simd_unit: t_PortableSIMDUnit) (c: i32) ->
        Libcrux_ml_dsa.Simd.Portable.Arithmetic.montgomery_multiply_by_constant simd_unit c);
    f_montgomery_multiply_pre = (fun (lhs: t_PortableSIMDUnit) (rhs: t_PortableSIMDUnit) -> true);
    f_montgomery_multiply_post
    =
    (fun (lhs: t_PortableSIMDUnit) (rhs: t_PortableSIMDUnit) (out: t_PortableSIMDUnit) -> true);
    f_montgomery_multiply
    =
    (fun (lhs: t_PortableSIMDUnit) (rhs: t_PortableSIMDUnit) ->
        Libcrux_ml_dsa.Simd.Portable.Arithmetic.montgomery_multiply lhs rhs);
    f_shift_left_then_reduce_pre = (fun (v_SHIFT_BY: i32) (simd_unit: t_PortableSIMDUnit) -> true);
    f_shift_left_then_reduce_post
    =
    (fun (v_SHIFT_BY: i32) (simd_unit: t_PortableSIMDUnit) (out: t_PortableSIMDUnit) -> true);
    f_shift_left_then_reduce
    =
    (fun (v_SHIFT_BY: i32) (simd_unit: t_PortableSIMDUnit) ->
        Libcrux_ml_dsa.Simd.Portable.Arithmetic.shift_left_then_reduce v_SHIFT_BY simd_unit);
    f_power2round_pre = (fun (simd_unit: t_PortableSIMDUnit) -> true);
    f_power2round_post
    =
    (fun (simd_unit: t_PortableSIMDUnit) (out: (t_PortableSIMDUnit & t_PortableSIMDUnit)) -> true);
    f_power2round
    =
    (fun (simd_unit: t_PortableSIMDUnit) ->
        Libcrux_ml_dsa.Simd.Portable.Arithmetic.power2round simd_unit);
    f_infinity_norm_exceeds_pre = (fun (simd_unit: t_PortableSIMDUnit) (bound: i32) -> true);
    f_infinity_norm_exceeds_post
    =
    (fun (simd_unit: t_PortableSIMDUnit) (bound: i32) (out: bool) -> true);
    f_infinity_norm_exceeds
    =
    (fun (simd_unit: t_PortableSIMDUnit) (bound: i32) ->
        Libcrux_ml_dsa.Simd.Portable.Arithmetic.infinity_norm_exceeds simd_unit bound);
    f_decompose_pre = (fun (v_GAMMA2: i32) (simd_unit: t_PortableSIMDUnit) -> true);
    f_decompose_post
    =
    (fun
        (v_GAMMA2: i32)
        (simd_unit: t_PortableSIMDUnit)
        (out: (t_PortableSIMDUnit & t_PortableSIMDUnit))
        ->
        true);
    f_decompose
    =
    (fun (v_GAMMA2: i32) (simd_unit: t_PortableSIMDUnit) ->
        Libcrux_ml_dsa.Simd.Portable.Arithmetic.decompose v_GAMMA2 simd_unit);
    f_compute_hint_pre
    =
    (fun (v_GAMMA2: i32) (low: t_PortableSIMDUnit) (high: t_PortableSIMDUnit) -> true);
    f_compute_hint_post
    =
    (fun
        (v_GAMMA2: i32)
        (low: t_PortableSIMDUnit)
        (high: t_PortableSIMDUnit)
        (out: (usize & t_PortableSIMDUnit))
        ->
        true);
    f_compute_hint
    =
    (fun (v_GAMMA2: i32) (low: t_PortableSIMDUnit) (high: t_PortableSIMDUnit) ->
        Libcrux_ml_dsa.Simd.Portable.Arithmetic.compute_hint v_GAMMA2 low high);
    f_use_hint_pre
    =
    (fun (v_GAMMA2: i32) (simd_unit: t_PortableSIMDUnit) (hint: t_PortableSIMDUnit) -> true);
    f_use_hint_post
    =
    (fun
        (v_GAMMA2: i32)
        (simd_unit: t_PortableSIMDUnit)
        (hint: t_PortableSIMDUnit)
        (out: t_PortableSIMDUnit)
        ->
        true);
    f_use_hint
    =
    (fun (v_GAMMA2: i32) (simd_unit: t_PortableSIMDUnit) (hint: t_PortableSIMDUnit) ->
        Libcrux_ml_dsa.Simd.Portable.Arithmetic.use_hint v_GAMMA2 simd_unit hint);
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
    f_gamma1_serialize_pre = (fun (v_OUTPUT_SIZE: usize) (simd_unit: t_PortableSIMDUnit) -> true);
    f_gamma1_serialize_post
    =
    (fun (v_OUTPUT_SIZE: usize) (simd_unit: t_PortableSIMDUnit) (out: t_Array u8 v_OUTPUT_SIZE) ->
        true);
    f_gamma1_serialize
    =
    (fun (v_OUTPUT_SIZE: usize) (simd_unit: t_PortableSIMDUnit) ->
        Libcrux_ml_dsa.Simd.Portable.Encoding.Gamma1.serialize v_OUTPUT_SIZE simd_unit);
    f_gamma1_deserialize_pre = (fun (v_GAMMA1_EXPONENT: usize) (serialized: t_Slice u8) -> true);
    f_gamma1_deserialize_post
    =
    (fun (v_GAMMA1_EXPONENT: usize) (serialized: t_Slice u8) (out: t_PortableSIMDUnit) -> true);
    f_gamma1_deserialize
    =
    (fun (v_GAMMA1_EXPONENT: usize) (serialized: t_Slice u8) ->
        Libcrux_ml_dsa.Simd.Portable.Encoding.Gamma1.deserialize v_GAMMA1_EXPONENT serialized);
    f_commitment_serialize_pre
    =
    (fun (v_OUTPUT_SIZE: usize) (simd_unit: t_PortableSIMDUnit) -> true);
    f_commitment_serialize_post
    =
    (fun (v_OUTPUT_SIZE: usize) (simd_unit: t_PortableSIMDUnit) (out: t_Array u8 v_OUTPUT_SIZE) ->
        true);
    f_commitment_serialize
    =
    (fun (v_OUTPUT_SIZE: usize) (simd_unit: t_PortableSIMDUnit) ->
        Libcrux_ml_dsa.Simd.Portable.Encoding.Commitment.serialize v_OUTPUT_SIZE simd_unit);
    f_error_serialize_pre = (fun (v_OUTPUT_SIZE: usize) (simd_unit: t_PortableSIMDUnit) -> true);
    f_error_serialize_post
    =
    (fun (v_OUTPUT_SIZE: usize) (simd_unit: t_PortableSIMDUnit) (out: t_Array u8 v_OUTPUT_SIZE) ->
        true);
    f_error_serialize
    =
    (fun (v_OUTPUT_SIZE: usize) (simd_unit: t_PortableSIMDUnit) ->
        Libcrux_ml_dsa.Simd.Portable.Encoding.Error.serialize v_OUTPUT_SIZE simd_unit);
    f_error_deserialize_pre = (fun (v_ETA: usize) (serialized: t_Slice u8) -> true);
    f_error_deserialize_post
    =
    (fun (v_ETA: usize) (serialized: t_Slice u8) (out: t_PortableSIMDUnit) -> true);
    f_error_deserialize
    =
    (fun (v_ETA: usize) (serialized: t_Slice u8) ->
        Libcrux_ml_dsa.Simd.Portable.Encoding.Error.deserialize v_ETA serialized);
    f_t0_serialize_pre = (fun (simd_unit: t_PortableSIMDUnit) -> true);
    f_t0_serialize_post
    =
    (fun (simd_unit: t_PortableSIMDUnit) (out: t_Array u8 (Rust_primitives.mk_usize 13)) -> true);
    f_t0_serialize
    =
    (fun (simd_unit: t_PortableSIMDUnit) ->
        Libcrux_ml_dsa.Simd.Portable.Encoding.T0.serialize simd_unit);
    f_t0_deserialize_pre = (fun (serialized: t_Slice u8) -> true);
    f_t0_deserialize_post = (fun (serialized: t_Slice u8) (out: t_PortableSIMDUnit) -> true);
    f_t0_deserialize
    =
    (fun (serialized: t_Slice u8) -> Libcrux_ml_dsa.Simd.Portable.Encoding.T0.deserialize serialized
    );
    f_t1_serialize_pre = (fun (simd_unit: t_PortableSIMDUnit) -> true);
    f_t1_serialize_post
    =
    (fun (simd_unit: t_PortableSIMDUnit) (out: t_Array u8 (Rust_primitives.mk_usize 10)) -> true);
    f_t1_serialize
    =
    (fun (simd_unit: t_PortableSIMDUnit) ->
        Libcrux_ml_dsa.Simd.Portable.Encoding.T1.serialize simd_unit);
    f_t1_deserialize_pre = (fun (serialized: t_Slice u8) -> true);
    f_t1_deserialize_post = (fun (serialized: t_Slice u8) (out: t_PortableSIMDUnit) -> true);
    f_t1_deserialize
    =
    (fun (serialized: t_Slice u8) -> Libcrux_ml_dsa.Simd.Portable.Encoding.T1.deserialize serialized
    );
    f_ntt_at_layer_0_pre
    =
    (fun (simd_unit: t_PortableSIMDUnit) (zeta0: i32) (zeta1: i32) (zeta2: i32) (zeta3: i32) -> true
    );
    f_ntt_at_layer_0_post
    =
    (fun
        (simd_unit: t_PortableSIMDUnit)
        (zeta0: i32)
        (zeta1: i32)
        (zeta2: i32)
        (zeta3: i32)
        (out: t_PortableSIMDUnit)
        ->
        true);
    f_ntt_at_layer_0_
    =
    (fun (simd_unit: t_PortableSIMDUnit) (zeta0: i32) (zeta1: i32) (zeta2: i32) (zeta3: i32) ->
        Libcrux_ml_dsa.Simd.Portable.Ntt.ntt_at_layer_0_ simd_unit zeta0 zeta1 zeta2 zeta3);
    f_ntt_at_layer_1_pre = (fun (simd_unit: t_PortableSIMDUnit) (zeta0: i32) (zeta1: i32) -> true);
    f_ntt_at_layer_1_post
    =
    (fun (simd_unit: t_PortableSIMDUnit) (zeta0: i32) (zeta1: i32) (out: t_PortableSIMDUnit) -> true
    );
    f_ntt_at_layer_1_
    =
    (fun (simd_unit: t_PortableSIMDUnit) (zeta0: i32) (zeta1: i32) ->
        Libcrux_ml_dsa.Simd.Portable.Ntt.ntt_at_layer_1_ simd_unit zeta0 zeta1);
    f_ntt_at_layer_2_pre = (fun (simd_unit: t_PortableSIMDUnit) (zeta: i32) -> true);
    f_ntt_at_layer_2_post
    =
    (fun (simd_unit: t_PortableSIMDUnit) (zeta: i32) (out: t_PortableSIMDUnit) -> true);
    f_ntt_at_layer_2_
    =
    (fun (simd_unit: t_PortableSIMDUnit) (zeta: i32) ->
        Libcrux_ml_dsa.Simd.Portable.Ntt.ntt_at_layer_2_ simd_unit zeta);
    f_invert_ntt_at_layer_0_pre
    =
    (fun (simd_unit: t_PortableSIMDUnit) (zeta0: i32) (zeta1: i32) (zeta2: i32) (zeta3: i32) -> true
    );
    f_invert_ntt_at_layer_0_post
    =
    (fun
        (simd_unit: t_PortableSIMDUnit)
        (zeta0: i32)
        (zeta1: i32)
        (zeta2: i32)
        (zeta3: i32)
        (out: t_PortableSIMDUnit)
        ->
        true);
    f_invert_ntt_at_layer_0_
    =
    (fun (simd_unit: t_PortableSIMDUnit) (zeta0: i32) (zeta1: i32) (zeta2: i32) (zeta3: i32) ->
        Libcrux_ml_dsa.Simd.Portable.Ntt.invert_ntt_at_layer_0_ simd_unit zeta0 zeta1 zeta2 zeta3);
    f_invert_ntt_at_layer_1_pre
    =
    (fun (simd_unit: t_PortableSIMDUnit) (zeta0: i32) (zeta1: i32) -> true);
    f_invert_ntt_at_layer_1_post
    =
    (fun (simd_unit: t_PortableSIMDUnit) (zeta0: i32) (zeta1: i32) (out: t_PortableSIMDUnit) -> true
    );
    f_invert_ntt_at_layer_1_
    =
    (fun (simd_unit: t_PortableSIMDUnit) (zeta0: i32) (zeta1: i32) ->
        Libcrux_ml_dsa.Simd.Portable.Ntt.invert_ntt_at_layer_1_ simd_unit zeta0 zeta1);
    f_invert_ntt_at_layer_2_pre = (fun (simd_unit: t_PortableSIMDUnit) (zeta: i32) -> true);
    f_invert_ntt_at_layer_2_post
    =
    (fun (simd_unit: t_PortableSIMDUnit) (zeta: i32) (out: t_PortableSIMDUnit) -> true);
    f_invert_ntt_at_layer_2_
    =
    fun (simd_unit: t_PortableSIMDUnit) (zeta: i32) ->
      Libcrux_ml_dsa.Simd.Portable.Ntt.invert_ntt_at_layer_2_ simd_unit zeta
  }
