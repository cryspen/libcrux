module Libcrux_ml_kem.Ind_cpa.Unpacked
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
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
let impl
      (v_K: usize)
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
    : Core.Default.t_Default (t_IndCpaPrivateKeyUnpacked v_K v_Vector) =
  {
    f_default_pre = (fun (_: Prims.unit) -> true);
    f_default_post = (fun (_: Prims.unit) (out: t_IndCpaPrivateKeyUnpacked v_K v_Vector) -> true);
    f_default
    =
    fun (_: Prims.unit) ->
      {
        f_secret_as_ntt
        =
        Rust_primitives.Hax.repeat (Libcrux_ml_kem.Polynomial.impl__ZERO #v_Vector ()
            <:
            Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
          v_K
      }
      <:
      t_IndCpaPrivateKeyUnpacked v_K v_Vector
  }

/// An unpacked ML-KEM IND-CPA Private Key
type t_IndCpaPublicKeyUnpacked
  (v_K: usize) (v_Vector: Type0) {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
  = {
  f_t_as_ntt:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K;
  f_seed_for_A:t_Array u8 (sz 32);
  f_A:t_Array (t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K) v_K
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1
      (v_K: usize)
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
    : Core.Default.t_Default (t_IndCpaPublicKeyUnpacked v_K v_Vector) =
  {
    f_default_pre = (fun (_: Prims.unit) -> true);
    f_default_post = (fun (_: Prims.unit) (out: t_IndCpaPublicKeyUnpacked v_K v_Vector) -> true);
    f_default
    =
    fun (_: Prims.unit) ->
      {
        f_t_as_ntt
        =
        Rust_primitives.Hax.repeat (Libcrux_ml_kem.Polynomial.impl__ZERO #v_Vector ()
            <:
            Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
          v_K;
        f_seed_for_A = Rust_primitives.Hax.repeat 0uy (sz 32);
        f_A
        =
        Rust_primitives.Hax.repeat (Rust_primitives.Hax.repeat (Libcrux_ml_kem.Polynomial.impl__ZERO
                  #v_Vector
                  ()
                <:
                Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
              v_K
            <:
            t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K)
          v_K
      }
      <:
      t_IndCpaPublicKeyUnpacked v_K v_Vector
  }
