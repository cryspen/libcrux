module Libcrux_ml_kem.Vector.Neon
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_kem.Vector.Neon.Vector_type in
  let open Libcrux_ml_kem.Vector.Traits in
  ()

val rej_sample (a: t_Slice u8) (result: t_Slice i16)
    : Prims.Pure (t_Slice i16 & usize) Prims.l_True (fun _ -> Prims.l_True)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl:Libcrux_ml_kem.Vector.Traits.t_Repr Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_1:Libcrux_ml_kem.Vector.Traits.t_Operations
Libcrux_ml_kem.Vector.Neon.Vector_type.t_SIMD128Vector
