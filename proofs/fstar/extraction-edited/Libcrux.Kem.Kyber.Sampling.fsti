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
          Hax_lib.v_forall (fun i ->
                let i:usize = i in
                Hax_lib.implies (i <.
                    (Core.Slice.impl__len (Rust_primitives.unsize result
                              .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                          <:
                          t_Slice i32)
                      <:
                      usize)
                    <:
                    bool)
                  (fun _ -> (Core.Num.impl__i32__abs (result.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ i
                          ]
                          <:
                          i32)
                      <:
                      i32) <=.
                    2l
                    <:
                    bool)
                <:
                bool))

val sample_from_uniform_distribution (randomness: t_Array u8 (sz 840))
    : Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement 
