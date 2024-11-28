module Libcrux_ml_dsa.Simd.Avx2
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

type t_AVX2SIMDUnit = { f_coefficients:u8 }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: Core.Convert.t_From t_AVX2SIMDUnit u8 =
  {
    f_from_pre = (fun (coefficients: u8) -> true);
    f_from_post = (fun (coefficients: u8) (out: t_AVX2SIMDUnit) -> true);
    f_from = fun (coefficients: u8) -> { f_coefficients = coefficients } <: t_AVX2SIMDUnit
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1: Libcrux_ml_dsa.Simd.Traits.t_Operations t_AVX2SIMDUnit =
  {
    _super_11581440318597584651 = FStar.Tactics.Typeclasses.solve;
    _super_9442900250278684536 = FStar.Tactics.Typeclasses.solve;
    f_ZERO_pre = (fun (_: Prims.unit) -> true);
    f_ZERO_post = (fun (_: Prims.unit) (out: t_AVX2SIMDUnit) -> true);
    f_ZERO
    =
    (fun (_: Prims.unit) ->
        Core.Convert.f_into #u8
          #t_AVX2SIMDUnit
          #FStar.Tactics.Typeclasses.solve
          (Libcrux_intrinsics.Avx2_extract.mm256_setzero_si256 () <: u8));
    f_from_coefficient_array_pre = (fun (coefficient_array: t_Slice i32) -> true);
    f_from_coefficient_array_post
    =
    (fun (coefficient_array: t_Slice i32) (out: t_AVX2SIMDUnit) -> true);
    f_from_coefficient_array
    =
    (fun (coefficient_array: t_Slice i32) ->
        Core.Convert.f_into #u8
          #t_AVX2SIMDUnit
          #FStar.Tactics.Typeclasses.solve
          (Libcrux_intrinsics.Avx2_extract.mm256_loadu_si256_i32 coefficient_array <: u8));
    f_to_coefficient_array_pre = (fun (self: t_AVX2SIMDUnit) -> true);
    f_to_coefficient_array_post = (fun (self: t_AVX2SIMDUnit) (out: t_Array i32 (sz 8)) -> true);
    f_to_coefficient_array
    =
    (fun (self: t_AVX2SIMDUnit) ->
        let coefficient_array:t_Array i32 (sz 8) = Rust_primitives.Hax.repeat 0l (sz 8) in
        let coefficient_array:t_Array i32 (sz 8) =
          Libcrux_intrinsics.Avx2_extract.mm256_storeu_si256_i32 coefficient_array
            self.f_coefficients
        in
        coefficient_array);
    f_add_pre = (fun (lhs: t_AVX2SIMDUnit) (rhs: t_AVX2SIMDUnit) -> true);
    f_add_post = (fun (lhs: t_AVX2SIMDUnit) (rhs: t_AVX2SIMDUnit) (out: t_AVX2SIMDUnit) -> true);
    f_add
    =
    (fun (lhs: t_AVX2SIMDUnit) (rhs: t_AVX2SIMDUnit) ->
        Core.Convert.f_into #u8
          #t_AVX2SIMDUnit
          #FStar.Tactics.Typeclasses.solve
          (Libcrux_ml_dsa.Simd.Avx2.Arithmetic.add lhs.f_coefficients rhs.f_coefficients <: u8));
    f_subtract_pre = (fun (lhs: t_AVX2SIMDUnit) (rhs: t_AVX2SIMDUnit) -> true);
    f_subtract_post
    =
    (fun (lhs: t_AVX2SIMDUnit) (rhs: t_AVX2SIMDUnit) (out: t_AVX2SIMDUnit) -> true);
    f_subtract
    =
    (fun (lhs: t_AVX2SIMDUnit) (rhs: t_AVX2SIMDUnit) ->
        Core.Convert.f_into #u8
          #t_AVX2SIMDUnit
          #FStar.Tactics.Typeclasses.solve
          (Libcrux_ml_dsa.Simd.Avx2.Arithmetic.subtract lhs.f_coefficients rhs.f_coefficients <: u8)
    );
    f_montgomery_multiply_by_constant_pre
    =
    (fun (simd_unit: t_AVX2SIMDUnit) (constant: i32) -> true);
    f_montgomery_multiply_by_constant_post
    =
    (fun (simd_unit: t_AVX2SIMDUnit) (constant: i32) (out: t_AVX2SIMDUnit) -> true);
    f_montgomery_multiply_by_constant
    =
    (fun (simd_unit: t_AVX2SIMDUnit) (constant: i32) ->
        Core.Convert.f_into #u8
          #t_AVX2SIMDUnit
          #FStar.Tactics.Typeclasses.solve
          (Libcrux_ml_dsa.Simd.Avx2.Arithmetic.montgomery_multiply_by_constant simd_unit
                .f_coefficients
              constant
            <:
            u8));
    f_montgomery_multiply_pre = (fun (lhs: t_AVX2SIMDUnit) (rhs: t_AVX2SIMDUnit) -> true);
    f_montgomery_multiply_post
    =
    (fun (lhs: t_AVX2SIMDUnit) (rhs: t_AVX2SIMDUnit) (out: t_AVX2SIMDUnit) -> true);
    f_montgomery_multiply
    =
    (fun (lhs: t_AVX2SIMDUnit) (rhs: t_AVX2SIMDUnit) ->
        Core.Convert.f_into #u8
          #t_AVX2SIMDUnit
          #FStar.Tactics.Typeclasses.solve
          (Libcrux_ml_dsa.Simd.Avx2.Arithmetic.montgomery_multiply lhs.f_coefficients
              rhs.f_coefficients
            <:
            u8));
    f_shift_left_then_reduce_pre = (fun (v_SHIFT_BY: i32) (simd_unit: t_AVX2SIMDUnit) -> true);
    f_shift_left_then_reduce_post
    =
    (fun (v_SHIFT_BY: i32) (simd_unit: t_AVX2SIMDUnit) (out: t_AVX2SIMDUnit) -> true);
    f_shift_left_then_reduce
    =
    (fun (v_SHIFT_BY: i32) (simd_unit: t_AVX2SIMDUnit) ->
        Core.Convert.f_into #u8
          #t_AVX2SIMDUnit
          #FStar.Tactics.Typeclasses.solve
          (Libcrux_ml_dsa.Simd.Avx2.Arithmetic.shift_left_then_reduce v_SHIFT_BY
              simd_unit.f_coefficients
            <:
            u8));
    f_power2round_pre = (fun (simd_unit: t_AVX2SIMDUnit) -> true);
    f_power2round_post
    =
    (fun (simd_unit: t_AVX2SIMDUnit) (out: (t_AVX2SIMDUnit & t_AVX2SIMDUnit)) -> true);
    f_power2round
    =
    (fun (simd_unit: t_AVX2SIMDUnit) ->
        let lower, upper:(u8 & u8) =
          Libcrux_ml_dsa.Simd.Avx2.Arithmetic.power2round simd_unit.f_coefficients
        in
        Core.Convert.f_into #u8 #t_AVX2SIMDUnit #FStar.Tactics.Typeclasses.solve lower,
        Core.Convert.f_into #u8 #t_AVX2SIMDUnit #FStar.Tactics.Typeclasses.solve upper
        <:
        (t_AVX2SIMDUnit & t_AVX2SIMDUnit));
    f_infinity_norm_exceeds_pre = (fun (simd_unit: t_AVX2SIMDUnit) (bound: i32) -> true);
    f_infinity_norm_exceeds_post
    =
    (fun (simd_unit: t_AVX2SIMDUnit) (bound: i32) (out: bool) -> true);
    f_infinity_norm_exceeds
    =
    (fun (simd_unit: t_AVX2SIMDUnit) (bound: i32) ->
        Libcrux_ml_dsa.Simd.Avx2.Arithmetic.infinity_norm_exceeds simd_unit.f_coefficients bound);
    f_decompose_pre = (fun (v_GAMMA2: i32) (simd_unit: t_AVX2SIMDUnit) -> true);
    f_decompose_post
    =
    (fun (v_GAMMA2: i32) (simd_unit: t_AVX2SIMDUnit) (out: (t_AVX2SIMDUnit & t_AVX2SIMDUnit)) ->
        true);
    f_decompose
    =
    (fun (v_GAMMA2: i32) (simd_unit: t_AVX2SIMDUnit) ->
        let lower, upper:(u8 & u8) =
          Libcrux_ml_dsa.Simd.Avx2.Arithmetic.decompose v_GAMMA2 simd_unit.f_coefficients
        in
        Core.Convert.f_into #u8 #t_AVX2SIMDUnit #FStar.Tactics.Typeclasses.solve lower,
        Core.Convert.f_into #u8 #t_AVX2SIMDUnit #FStar.Tactics.Typeclasses.solve upper
        <:
        (t_AVX2SIMDUnit & t_AVX2SIMDUnit));
    f_compute_hint_pre = (fun (v_GAMMA2: i32) (low: t_AVX2SIMDUnit) (high: t_AVX2SIMDUnit) -> true);
    f_compute_hint_post
    =
    (fun
        (v_GAMMA2: i32)
        (low: t_AVX2SIMDUnit)
        (high: t_AVX2SIMDUnit)
        (out: (usize & t_AVX2SIMDUnit))
        ->
        true);
    f_compute_hint
    =
    (fun (v_GAMMA2: i32) (low: t_AVX2SIMDUnit) (high: t_AVX2SIMDUnit) ->
        let count, hint:(usize & u8) =
          Libcrux_ml_dsa.Simd.Avx2.Arithmetic.compute_hint v_GAMMA2
            low.f_coefficients
            high.f_coefficients
        in
        count, Core.Convert.f_into #u8 #t_AVX2SIMDUnit #FStar.Tactics.Typeclasses.solve hint
        <:
        (usize & t_AVX2SIMDUnit));
    f_use_hint_pre
    =
    (fun (v_GAMMA2: i32) (simd_unit: t_AVX2SIMDUnit) (hint: t_AVX2SIMDUnit) -> true);
    f_use_hint_post
    =
    (fun (v_GAMMA2: i32) (simd_unit: t_AVX2SIMDUnit) (hint: t_AVX2SIMDUnit) (out: t_AVX2SIMDUnit) ->
        true);
    f_use_hint
    =
    (fun (v_GAMMA2: i32) (simd_unit: t_AVX2SIMDUnit) (hint: t_AVX2SIMDUnit) ->
        Core.Convert.f_into #u8
          #t_AVX2SIMDUnit
          #FStar.Tactics.Typeclasses.solve
          (Libcrux_ml_dsa.Simd.Avx2.Arithmetic.use_hint v_GAMMA2
              simd_unit.f_coefficients
              hint.f_coefficients
            <:
            u8));
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
    f_gamma1_serialize_pre = (fun (v_OUTPUT_SIZE: usize) (simd_unit: t_AVX2SIMDUnit) -> true);
    f_gamma1_serialize_post
    =
    (fun (v_OUTPUT_SIZE: usize) (simd_unit: t_AVX2SIMDUnit) (out: t_Array u8 v_OUTPUT_SIZE) -> true);
    f_gamma1_serialize
    =
    (fun (v_OUTPUT_SIZE: usize) (simd_unit: t_AVX2SIMDUnit) ->
        Libcrux_ml_dsa.Simd.Avx2.Encoding.Gamma1.serialize v_OUTPUT_SIZE simd_unit.f_coefficients);
    f_gamma1_deserialize_pre = (fun (v_GAMMA1_EXPONENT: usize) (serialized: t_Slice u8) -> true);
    f_gamma1_deserialize_post
    =
    (fun (v_GAMMA1_EXPONENT: usize) (serialized: t_Slice u8) (out: t_AVX2SIMDUnit) -> true);
    f_gamma1_deserialize
    =
    (fun (v_GAMMA1_EXPONENT: usize) (serialized: t_Slice u8) ->
        Core.Convert.f_into #u8
          #t_AVX2SIMDUnit
          #FStar.Tactics.Typeclasses.solve
          (Libcrux_ml_dsa.Simd.Avx2.Encoding.Gamma1.deserialize v_GAMMA1_EXPONENT serialized <: u8));
    f_commitment_serialize_pre = (fun (v_OUTPUT_SIZE: usize) (simd_unit: t_AVX2SIMDUnit) -> true);
    f_commitment_serialize_post
    =
    (fun (v_OUTPUT_SIZE: usize) (simd_unit: t_AVX2SIMDUnit) (out: t_Array u8 v_OUTPUT_SIZE) -> true);
    f_commitment_serialize
    =
    (fun (v_OUTPUT_SIZE: usize) (simd_unit: t_AVX2SIMDUnit) ->
        Libcrux_ml_dsa.Simd.Avx2.Encoding.Commitment.serialize v_OUTPUT_SIZE
          simd_unit.f_coefficients);
    f_error_serialize_pre = (fun (v_OUTPUT_SIZE: usize) (simd_unit: t_AVX2SIMDUnit) -> true);
    f_error_serialize_post
    =
    (fun (v_OUTPUT_SIZE: usize) (simd_unit: t_AVX2SIMDUnit) (out: t_Array u8 v_OUTPUT_SIZE) -> true);
    f_error_serialize
    =
    (fun (v_OUTPUT_SIZE: usize) (simd_unit: t_AVX2SIMDUnit) ->
        Libcrux_ml_dsa.Simd.Avx2.Encoding.Error.serialize v_OUTPUT_SIZE simd_unit.f_coefficients);
    f_error_deserialize_pre = (fun (v_ETA: usize) (serialized: t_Slice u8) -> true);
    f_error_deserialize_post
    =
    (fun (v_ETA: usize) (serialized: t_Slice u8) (out: t_AVX2SIMDUnit) -> true);
    f_error_deserialize
    =
    (fun (v_ETA: usize) (serialized: t_Slice u8) ->
        Core.Convert.f_into #u8
          #t_AVX2SIMDUnit
          #FStar.Tactics.Typeclasses.solve
          (Libcrux_ml_dsa.Simd.Avx2.Encoding.Error.deserialize v_ETA serialized <: u8));
    f_t0_serialize_pre = (fun (simd_unit: t_AVX2SIMDUnit) -> true);
    f_t0_serialize_post = (fun (simd_unit: t_AVX2SIMDUnit) (out: t_Array u8 (sz 13)) -> true);
    f_t0_serialize
    =
    (fun (simd_unit: t_AVX2SIMDUnit) ->
        Libcrux_ml_dsa.Simd.Avx2.Encoding.T0.serialize simd_unit.f_coefficients);
    f_t0_deserialize_pre = (fun (serialized: t_Slice u8) -> true);
    f_t0_deserialize_post = (fun (serialized: t_Slice u8) (out: t_AVX2SIMDUnit) -> true);
    f_t0_deserialize
    =
    (fun (serialized: t_Slice u8) ->
        Core.Convert.f_into #u8
          #t_AVX2SIMDUnit
          #FStar.Tactics.Typeclasses.solve
          (Libcrux_ml_dsa.Simd.Avx2.Encoding.T0.deserialize serialized <: u8));
    f_t1_serialize_pre = (fun (simd_unit: t_AVX2SIMDUnit) -> true);
    f_t1_serialize_post = (fun (simd_unit: t_AVX2SIMDUnit) (out: t_Array u8 (sz 10)) -> true);
    f_t1_serialize
    =
    (fun (simd_unit: t_AVX2SIMDUnit) ->
        Libcrux_ml_dsa.Simd.Avx2.Encoding.T1.serialize simd_unit.f_coefficients);
    f_t1_deserialize_pre = (fun (serialized: t_Slice u8) -> true);
    f_t1_deserialize_post = (fun (serialized: t_Slice u8) (out: t_AVX2SIMDUnit) -> true);
    f_t1_deserialize
    =
    (fun (serialized: t_Slice u8) ->
        Core.Convert.f_into #u8
          #t_AVX2SIMDUnit
          #FStar.Tactics.Typeclasses.solve
          (Libcrux_ml_dsa.Simd.Avx2.Encoding.T1.deserialize serialized <: u8));
    f_ntt_pre = (fun (simd_units: t_Array t_AVX2SIMDUnit (sz 32)) -> true);
    f_ntt_post
    =
    (fun (simd_units: t_Array t_AVX2SIMDUnit (sz 32)) (out: t_Array t_AVX2SIMDUnit (sz 32)) -> true);
    f_ntt
    =
    (fun (simd_units: t_Array t_AVX2SIMDUnit (sz 32)) ->
        let result:t_Array u8 (sz 32) =
          Libcrux_ml_dsa.Simd.Avx2.Ntt.ntt (Core.Array.impl_23__map #t_AVX2SIMDUnit
                (sz 32)
                #u8
                simd_units
                (fun x ->
                    let x:t_AVX2SIMDUnit = x in
                    x.f_coefficients)
              <:
              t_Array u8 (sz 32))
        in
        Core.Array.impl_23__map #u8
          (sz 32)
          #t_AVX2SIMDUnit
          result
          (fun x ->
              let x:u8 = x in
              Core.Convert.f_into #u8 #t_AVX2SIMDUnit #FStar.Tactics.Typeclasses.solve x
              <:
              t_AVX2SIMDUnit));
    f_invert_ntt_at_layer_0_pre
    =
    (fun (simd_unit: t_AVX2SIMDUnit) (zeta0: i32) (zeta1: i32) (zeta2: i32) (zeta3: i32) -> true);
    f_invert_ntt_at_layer_0_post
    =
    (fun
        (simd_unit: t_AVX2SIMDUnit)
        (zeta0: i32)
        (zeta1: i32)
        (zeta2: i32)
        (zeta3: i32)
        (out: t_AVX2SIMDUnit)
        ->
        true);
    f_invert_ntt_at_layer_0_
    =
    (fun (simd_unit: t_AVX2SIMDUnit) (zeta0: i32) (zeta1: i32) (zeta2: i32) (zeta3: i32) ->
        Core.Convert.f_into #u8
          #t_AVX2SIMDUnit
          #FStar.Tactics.Typeclasses.solve
          (Libcrux_ml_dsa.Simd.Avx2.Ntt.invert_ntt_at_layer_0_ simd_unit.f_coefficients
              zeta0
              zeta1
              zeta2
              zeta3
            <:
            u8));
    f_invert_ntt_at_layer_1_pre
    =
    (fun (simd_unit: t_AVX2SIMDUnit) (zeta0: i32) (zeta1: i32) -> true);
    f_invert_ntt_at_layer_1_post
    =
    (fun (simd_unit: t_AVX2SIMDUnit) (zeta0: i32) (zeta1: i32) (out: t_AVX2SIMDUnit) -> true);
    f_invert_ntt_at_layer_1_
    =
    (fun (simd_unit: t_AVX2SIMDUnit) (zeta0: i32) (zeta1: i32) ->
        Core.Convert.f_into #u8
          #t_AVX2SIMDUnit
          #FStar.Tactics.Typeclasses.solve
          (Libcrux_ml_dsa.Simd.Avx2.Ntt.invert_ntt_at_layer_1_ simd_unit.f_coefficients zeta0 zeta1
            <:
            u8));
    f_invert_ntt_at_layer_2_pre = (fun (simd_unit: t_AVX2SIMDUnit) (zeta: i32) -> true);
    f_invert_ntt_at_layer_2_post
    =
    (fun (simd_unit: t_AVX2SIMDUnit) (zeta: i32) (out: t_AVX2SIMDUnit) -> true);
    f_invert_ntt_at_layer_2_
    =
    fun (simd_unit: t_AVX2SIMDUnit) (zeta: i32) ->
      Core.Convert.f_into #u8
        #t_AVX2SIMDUnit
        #FStar.Tactics.Typeclasses.solve
        (Libcrux_ml_dsa.Simd.Avx2.Ntt.invert_ntt_at_layer_2_ simd_unit.f_coefficients zeta <: u8)
  }
