module Libcrux_ml_dsa.Simd.Portable.Encoding.T0
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_dsa.Simd.Portable in
  let open Libcrux_ml_dsa.Simd.Traits in
  ()

val change_t0_interval (t0: i32) : Prims.Pure i32 Prims.l_True (fun _ -> Prims.l_True)

let deserialize__BITS_IN_LOWER_PART_OF_T_MASK: i32 =
  (Rust_primitives.mk_i32 1 <<!
    (cast (Libcrux_ml_dsa.Constants.v_BITS_IN_LOWER_PART_OF_T <: usize) <: i32)
    <:
    i32) -!
  Rust_primitives.mk_i32 1

val serialize (simd_unit: Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit)
    : Prims.Pure (t_Array u8 (Rust_primitives.mk_usize 13)) Prims.l_True (fun _ -> Prims.l_True)

val deserialize (serialized: t_Slice u8)
    : Prims.Pure Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
      Prims.l_True
      (fun _ -> Prims.l_True)
