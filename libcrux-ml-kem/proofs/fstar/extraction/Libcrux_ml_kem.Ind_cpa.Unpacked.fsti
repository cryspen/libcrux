module Libcrux_ml_kem.Ind_cpa.Unpacked
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_kem.Vector.Traits in
  ()

/// An unpacked ML-KEM IND-CPA Private Key
type t_IndCpaPrivateKeyUnpacked
  (v_K: usize) (v_Vector: Type0) {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
  = { f_secret_as_ntt:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K }

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl
      (v_K: usize)
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
    : Core.Default.t_Default (t_IndCpaPrivateKeyUnpacked v_K v_Vector)

/// An unpacked ML-KEM IND-CPA Public Key
type t_IndCpaPublicKeyUnpacked
  (v_K: usize) (v_Vector: Type0) {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
  = {
  f_tt_as_ntt:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K;
  f_seed_for_A:t_Array u8 (mk_usize 32);
  f_A:t_Array (t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K) v_K
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_2
      (v_K: usize)
      (#v_Vector: Type0)
      {| i1: Core.Clone.t_Clone v_Vector |}
      {| i2: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
    : Core.Clone.t_Clone (t_IndCpaPublicKeyUnpacked v_K v_Vector)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_1
      (v_K: usize)
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
    : Core.Default.t_Default (t_IndCpaPublicKeyUnpacked v_K v_Vector)
