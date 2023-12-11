module Libcrux.Kem.Kyber.Sampling
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

val sample_from_binomial_distribution (#p:Spec.Kyber.params)
    (v_ETA: usize) (randomness: t_Slice u8)
    : Pure Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
      (requires (v_ETA = p.v_ETA1 \/ v_ETA = p.v_ETA2) /\
                (Core.Slice.impl__len randomness <: usize) =. (v_ETA *! sz 64 <: usize))
      (ensures
        fun result ->
          let result:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement = result in
          Libcrux.Kem.Kyber.Arithmetic.to_spec_poly result == 
          Spec.Kyber.sample_poly_binomial v_ETA randomness /\
          (forall (i:usize). i <. length result.Libcrux.Kem.Kyber.Arithmetic.f_coefficients ==>
             (v #i32_inttype result.f_coefficients.[i] >= - (v v_ETA) /\
              v #i32_inttype result.f_coefficients.[i] <= (v v_ETA))))


val sample_from_uniform_distribution (randomness: t_Array u8 (sz 840))
    : Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement 
