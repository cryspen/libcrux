module Libcrux_ml_dsa.Simd.Portable.Encoding.Gamma1
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_dsa.Simd.Portable in
  ()

let deserialize_when_gamma1_is_2_pow_17___GAMMA1: i32 = 1l <<! 17l

let deserialize_when_gamma1_is_2_pow_17___GAMMA1_TIMES_2_BITMASK: i32 =
  (deserialize_when_gamma1_is_2_pow_17___GAMMA1 <<! 1l <: i32) -! 1l

let deserialize_when_gamma1_is_2_pow_19___GAMMA1: i32 = 1l <<! 19l

let deserialize_when_gamma1_is_2_pow_19___GAMMA1_TIMES_2_BITMASK: i32 =
  (deserialize_when_gamma1_is_2_pow_19___GAMMA1 <<! 1l <: i32) -! 1l

let serialize_when_gamma1_is_2_pow_17___GAMMA1: i32 = 1l <<! 17l

let serialize_when_gamma1_is_2_pow_19___GAMMA1: i32 = 1l <<! 19l

val serialize_when_gamma1_is_2_pow_17_
      (v_OUTPUT_SIZE: usize)
      (simd_unit: Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit)
    : Prims.Pure (t_Array u8 v_OUTPUT_SIZE) Prims.l_True (fun _ -> Prims.l_True)

val serialize_when_gamma1_is_2_pow_19_
      (v_OUTPUT_SIZE: usize)
      (simd_unit: Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit)
    : Prims.Pure (t_Array u8 v_OUTPUT_SIZE) Prims.l_True (fun _ -> Prims.l_True)

val serialize (v_OUTPUT_SIZE: usize) (simd_unit: Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit)
    : Prims.Pure (t_Array u8 v_OUTPUT_SIZE) Prims.l_True (fun _ -> Prims.l_True)

val deserialize_when_gamma1_is_2_pow_17_ (serialized: t_Slice u8)
    : Prims.Pure Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
      Prims.l_True
      (fun _ -> Prims.l_True)

val deserialize_when_gamma1_is_2_pow_19_ (serialized: t_Slice u8)
    : Prims.Pure Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
      Prims.l_True
      (fun _ -> Prims.l_True)

val deserialize (v_GAMMA1_EXPONENT: usize) (serialized: t_Slice u8)
    : Prims.Pure Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
      Prims.l_True
      (fun _ -> Prims.l_True)
