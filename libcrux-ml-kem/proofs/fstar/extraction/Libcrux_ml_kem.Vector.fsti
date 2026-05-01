module Libcrux_ml_kem.Vector
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open FStar.Mul
open Core_models

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_kem.Vector.Traits in
  ()

let v_VECTORS_IN_RING_ELEMENT: usize = mk_usize 16

type t_PolynomialRingElement
  (v_Vector: Type0) {| i0: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
  = { f_coefficients:t_Array v_Vector (mk_usize 16) }

let impl
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Clone.t_Clone v_Vector)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
    : Core_models.Clone.t_Clone (t_PolynomialRingElement v_Vector) =
  { f_clone = (fun x -> x); f_clone_pre = (fun _ -> True); f_clone_post = (fun _ _ -> True) }

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_1
      (#v_Vector: Type0)
      {| i0: Core_models.Marker.t_Copy v_Vector |}
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
    : Core_models.Marker.t_Copy (t_PolynomialRingElement v_Vector)
