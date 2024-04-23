module Libcrux_ml_kem.Sampling
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

val sample_from_uniform_distribution_next
      (v_K v_N: usize)
      (randomness: t_Array (t_Array u8 v_N) v_K)
      (sampled_coefficients: t_Array usize v_K)
      (out: t_Array (t_Array i32 (sz 256)) v_K)
    : Prims.Pure (t_Array usize v_K & t_Array (t_Array i32 (sz 256)) v_K & bool)
      Prims.l_True
      (fun _ -> Prims.l_True)

val sample_from_binomial_distribution_2_ (randomness: t_Slice u8)
    : Prims.Pure Libcrux_ml_kem.Polynomial.t_PolynomialRingElement
      (requires (Core.Slice.impl__len randomness <: usize) =. (sz 2 *! sz 64 <: usize))
      (fun _ -> Prims.l_True)

val sample_from_binomial_distribution_3_ (randomness: t_Slice u8)
    : Prims.Pure Libcrux_ml_kem.Polynomial.t_PolynomialRingElement
      (requires (Core.Slice.impl__len randomness <: usize) =. (sz 3 *! sz 64 <: usize))
      (fun _ -> Prims.l_True)

val sample_from_binomial_distribution (v_ETA: usize) (randomness: t_Slice u8)
    : Prims.Pure Libcrux_ml_kem.Polynomial.t_PolynomialRingElement
      Prims.l_True
      (fun _ -> Prims.l_True)

val sample_from_xof (v_K: usize) (seeds: t_Array (t_Array u8 (sz 34)) v_K)
    : Prims.Pure (t_Array Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_K)
      Prims.l_True
      (fun _ -> Prims.l_True)
