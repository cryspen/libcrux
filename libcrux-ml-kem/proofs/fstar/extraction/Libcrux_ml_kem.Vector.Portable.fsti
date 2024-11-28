module Libcrux_ml_kem.Vector.Portable
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_kem.Vector.Portable.Vector_type in
  ()

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl:Libcrux_ml_kem.Vector.Traits.t_Operations
Libcrux_ml_kem.Vector.Portable.Vector_type.t_PortableVector
