module Libcrux_ml_dsa.Simd.Portable.Encoding.T1
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_dsa.Simd.Portable in
  let open Libcrux_ml_dsa.Simd.Traits in
  ()

val serialize (simd_unit: Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit)
    : Prims.Pure (t_Array u8 (Rust_primitives.mk_usize 10)) Prims.l_True (fun _ -> Prims.l_True)

val deserialize (serialized: t_Slice u8)
    : Prims.Pure Libcrux_ml_dsa.Simd.Portable.t_PortableSIMDUnit
      Prims.l_True
      (fun _ -> Prims.l_True)
