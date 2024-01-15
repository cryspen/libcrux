module Libcrux.Kem.Kyber.Sampling
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

open Libcrux.Kem.Kyber.Arithmetic

val sample_from_binomial_distribution_2_ (randomness: t_Slice u8)
    : Prims.Pure (t_PolynomialRingElement_b 3)
      (requires (Core.Slice.impl__len randomness <: usize) =. (sz 2 *! sz 64 <: usize))
      (ensures
        fun result ->
          Libcrux.Kem.Kyber.Arithmetic.to_spec_poly_b result == 
          Spec.Kyber.sample_poly_binomial (sz 2) randomness)

val sample_from_binomial_distribution_3_ (randomness: t_Slice u8)
    : Prims.Pure (t_PolynomialRingElement_b 7)
      (requires (Core.Slice.impl__len randomness <: usize) =. (sz 3 *! sz 64 <: usize))
      (ensures
        fun result ->
          Libcrux.Kem.Kyber.Arithmetic.to_spec_poly_b result == 
          Spec.Kyber.sample_poly_binomial (sz 3) randomness)

val sample_from_binomial_distribution (#p:Spec.Kyber.params)
    (v_ETA: usize) (randomness: t_Slice u8) 
    : Pure (Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b (pow2 (v v_ETA) - 1))
      (requires (v_ETA = p.v_ETA1 \/ v_ETA = p.v_ETA2) /\
                (Core.Slice.impl__len randomness <: usize) =. (v_ETA *! sz 64 <: usize))
      (ensures
        fun result ->
          Libcrux.Kem.Kyber.Arithmetic.to_spec_poly_b result == 
          Spec.Kyber.sample_poly_binomial v_ETA randomness)

val sample_from_uniform_distribution (randomness: t_Array u8 (sz 840))
    : Pure Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement
      (requires True)
      (ensures fun _ -> True)
//      (ensures fun result -> (forall i. v (result.f_coefficients.[i]) >= 0))
      
