module Libcrux_ml_dsa.Simd.Portable.Arithmetic
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_dsa.Simd.Portable.Vector_type in
  ()

let v_MONTGOMERY_SHIFT: u8 = mk_u8 32

val add (lhs rhs: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
    : Prims.Pure Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients
      (requires
        Libcrux_ml_dsa.Simd.Traits.add_pre lhs.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
          rhs.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values)
      (ensures
        fun lhs_future ->
          let lhs_future:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients = lhs_future in
          Libcrux_ml_dsa.Simd.Traits.add_post lhs.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
            rhs.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
            lhs_future.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values)

val subtract (lhs rhs: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
    : Prims.Pure Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients
      (requires
        Libcrux_ml_dsa.Simd.Traits.sub_pre lhs.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
          rhs.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values)
      (ensures
        fun lhs_future ->
          let lhs_future:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients = lhs_future in
          Libcrux_ml_dsa.Simd.Traits.sub_post lhs.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
            rhs.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values
            lhs_future.Libcrux_ml_dsa.Simd.Portable.Vector_type.f_values)

val get_n_least_significant_bits (n: u8) (value: u64)
    : Prims.Pure u64
      (requires n <=. mk_u8 32)
      (ensures
        fun result ->
          let result:u64 = result in
          v result == v value % pow2 (v n))

val montgomery_reduce_element (value: i64)
    : Prims.Pure i32
      (requires Spec.Utils.is_i64b (8380416 * pow2 32) value)
      (ensures
        fun result ->
          let result:i32 = result in
          Spec.Utils.is_i32b (8380416 + 4190209) result /\
          (Spec.Utils.is_i64b (8380416 * pow2 31) value ==> Spec.Utils.is_i32b 8380416 result) /\
          v result % 8380417 == (v value * 8265825) % 8380417)

val montgomery_multiply_fe_by_fer (fe fer: i32)
    : Prims.Pure i32
      (requires Spec.Utils.is_i32b 4190208 fer)
      (ensures
        fun result ->
          let result:i32 = result in
          Spec.Utils.is_i32b 8380416 result /\
          v result % 8380417 == (v fe * v fer * 8265825) % 8380417)

val montgomery_multiply_by_constant
      (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
      (c: i32)
    : Prims.Pure Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients
      (requires Spec.Utils.is_i32b 4190208 c)
      (ensures
        fun simd_unit_future ->
          let simd_unit_future:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients =
            simd_unit_future
          in
          Spec.Utils.is_i32b_array 8380416 simd_unit_future.f_values /\
          (forall i.
              i < 8 ==>
              (v (Seq.index simd_unit_future.f_values i) % 8380417 ==
                (v (Seq.index simd_unit.f_values i) * v c * 8265825) % 8380417)))

val montgomery_multiply (lhs rhs: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
    : Prims.Pure Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients
      (requires forall i. i < 8 ==> Spec.Utils.is_i32b 4190208 (Seq.index rhs.f_values i))
      (ensures
        fun lhs_future ->
          let lhs_future:Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients = lhs_future in
          Spec.Utils.is_i32b_array 8380416 lhs_future.f_values /\
          (forall i.
              i < 8 ==>
              (v (Seq.index lhs_future.f_values i) % 8380417 ==
                (v (Seq.index lhs.f_values i) * v (Seq.index rhs.f_values i) * 8265825) % 8380417)))

val power2round_element (t: i32) : Prims.Pure (i32 & i32) Prims.l_True (fun _ -> Prims.l_True)

val power2round (t0 t1: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
    : Prims.Pure
      (Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients &
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
      Prims.l_True
      (fun _ -> Prims.l_True)

val infinity_norm_exceeds
      (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
      (bound: i32)
    : Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)

val reduce_element (fe: i32) : Prims.Pure i32 Prims.l_True (fun _ -> Prims.l_True)

val shift_left_then_reduce
      (v_SHIFT_BY: i32)
      (simd_unit: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
    : Prims.Pure Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients
      Prims.l_True
      (fun _ -> Prims.l_True)

val compute_one_hint (low high gamma2: i32) : Prims.Pure i32 Prims.l_True (fun _ -> Prims.l_True)

val compute_hint
      (low high: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
      (gamma2: i32)
      (hint: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
    : Prims.Pure (Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients & usize)
      Prims.l_True
      (fun _ -> Prims.l_True)

val decompose_element (gamma2 r: i32) : Prims.Pure (i32 & i32) Prims.l_True (fun _ -> Prims.l_True)

val uuse_one_hint (gamma2 r hint: i32) : Prims.Pure i32 Prims.l_True (fun _ -> Prims.l_True)

val decompose
      (gamma2: i32)
      (simd_unit low high: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
    : Prims.Pure
      (Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients &
        Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
      Prims.l_True
      (fun _ -> Prims.l_True)

val uuse_hint
      (gamma2: i32)
      (simd_unit hint: Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients)
    : Prims.Pure Libcrux_ml_dsa.Simd.Portable.Vector_type.t_Coefficients
      Prims.l_True
      (fun _ -> Prims.l_True)
