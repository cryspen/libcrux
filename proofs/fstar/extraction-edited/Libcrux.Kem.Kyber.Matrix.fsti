module Libcrux.Kem.Kyber.Matrix
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

val compute_As_plus_e (#p:Spec.Kyber.params)
      (v_K: usize)
      (matrix_A: t_Array (t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K) v_K)
      (s_as_ntt error_as_ntt: t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K)
    : Pure (t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K) 
           (requires (v_K == p.v_RANK))
           (ensures fun _ -> True)

val compute_message (#p:Spec.Kyber.params)
      (v_K: usize)
      (v: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement)
      (secret_as_ntt u_as_ntt: t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K)
    : Pure (Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement)
      (requires (v_K == p.v_RANK))
      (ensures (fun _ -> True))

val compute_ring_element_v (#p:Spec.Kyber.params)
      (v_K: usize)
      (tt_as_ntt r_as_ntt: t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K)
      (error_2_ message: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement)
    : Pure (Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement)
      (requires (v_K == p.v_RANK))
      (ensures fun _ -> True)

val compute_vector_u (#p:Spec.Kyber.params)
      (v_K: usize)
      (a_as_ntt: t_Array (t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K) v_K)
      (r_as_ntt error_1_: t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K)
    : Pure (t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K)
      (requires (v_K == p.v_RANK))
      (ensures fun _ -> True)


val sample_matrix_A (#p:Spec.Kyber.params) (v_K: usize) (seed: t_Array u8 (sz 34)) (transpose: bool)
    : Pure (t_Array (t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K) v_K)
      (requires (v_K == p.v_RANK))
      (ensures fun _ -> True)
