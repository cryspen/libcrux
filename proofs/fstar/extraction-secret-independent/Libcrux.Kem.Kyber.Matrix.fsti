module Libcrux.Kem.Kyber.Matrix
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

val compute_As_plus_e
      (v_K: usize)
      (matrix_A: t_Array (t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K) v_K)
      (s_as_ntt error_as_ntt: t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K)
    : Prims.Pure (t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K)
      Prims.l_True
      (fun _ -> Prims.l_True)

val compute_message
      (v_K: usize)
      (v: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement)
      (secret_as_ntt u_as_ntt: t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K)
    : Prims.Pure Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
      Prims.l_True
      (fun _ -> Prims.l_True)

val compute_ring_element_v
      (v_K: usize)
      (tt_as_ntt r_as_ntt: t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K)
      (error_2_ message: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement)
    : Prims.Pure Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
      Prims.l_True
      (fun _ -> Prims.l_True)

val compute_vector_u
      (v_K: usize)
      (a_as_ntt: t_Array (t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K) v_K)
      (r_as_ntt error_1_: t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K)
    : Prims.Pure (t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K)
      Prims.l_True
      (fun _ -> Prims.l_True)

val sample_matrix_A (v_K: usize) (seed: t_Array u8 (sz 34)) (transpose: bool)
    : Prims.Pure (t_Array (t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K) v_K)
      Prims.l_True
      (fun _ -> Prims.l_True)
