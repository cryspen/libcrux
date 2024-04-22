module Libcrux_ml_kem.Ntt
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

val invert_ntt_montgomery (v_K: usize) (re: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement)
    : Prims.Pure Libcrux_ml_kem.Polynomial.t_PolynomialRingElement
      Prims.l_True
      (fun _ -> Prims.l_True)

val ntt_binomially_sampled_ring_element (re: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement)
    : Prims.Pure Libcrux_ml_kem.Polynomial.t_PolynomialRingElement
      Prims.l_True
      (fun _ -> Prims.l_True)

val ntt_vector_u
      (v_VECTOR_U_COMPRESSION_FACTOR: usize)
      (re: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement)
    : Prims.Pure Libcrux_ml_kem.Polynomial.t_PolynomialRingElement
      Prims.l_True
      (fun _ -> Prims.l_True)
