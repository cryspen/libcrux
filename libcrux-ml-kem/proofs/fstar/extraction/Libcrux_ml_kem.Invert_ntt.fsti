module Libcrux_ml_kem.Invert_ntt
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_kem.Vector.Traits in
  ()

val inv_ntt_layer_int_vec_step_reduce
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (a b: v_Vector)
      (zeta_r: i16)
    : Prims.Pure (v_Vector & v_Vector) Prims.l_True (fun _ -> Prims.l_True)

val invert_ntt_at_layer_1_
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (zeta_i: usize)
      (re: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (v__layer: usize)
    : Prims.Pure (usize & Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (requires zeta_i >=. sz 64 && zeta_i <=. sz 128)
      (fun _ -> Prims.l_True)

val invert_ntt_at_layer_2_
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (zeta_i: usize)
      (re: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (v__layer: usize)
    : Prims.Pure (usize & Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (requires zeta_i >=. sz 32 && zeta_i <=. sz 128)
      (fun _ -> Prims.l_True)

val invert_ntt_at_layer_3_
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (zeta_i: usize)
      (re: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (v__layer: usize)
    : Prims.Pure (usize & Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (requires zeta_i >=. sz 16 && zeta_i <=. sz 128)
      (fun _ -> Prims.l_True)

val invert_ntt_at_layer_4_plus
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (zeta_i: usize)
      (re: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (layer: usize)
    : Prims.Pure (usize & Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (requires
        (Rust_primitives.Hax.Int.from_machine layer <: Hax_lib.Int.t_Int) <
        (Rust_primitives.Hax.Int.from_machine Core.Num.impl__usize__BITS <: Hax_lib.Int.t_Int) &&
        (zeta_i -! (sz 128 >>! layer <: usize) <: usize) >=. sz 0)
      (fun _ -> Prims.l_True)

val invert_ntt_montgomery
      (#v_K: usize)
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (re: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
    : Prims.Pure (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      Prims.l_True
      (fun _ -> Prims.l_True)
