module Libcrux.Kem.Kyber.Sampling
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

val rejection_sampling_panic_with_diagnostic: Prims.unit
  -> Prims.Pure Prims.unit Prims.l_True (fun _ -> Prims.l_True)

val sample_from_binomial_distribution_2_ (randomness: t_Slice u8)
    : Prims.Pure Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
      (requires (Core.Slice.impl__len randomness <: usize) =. (sz 2 *! sz 64 <: usize))
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
                  (fun temp_0_ ->
                      let _:Prims.unit = temp_0_ in
                      (Core.Num.impl__i32__abs (result.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[
                              i ]
                            <:
                            i32)
                        <:
                        i32) <=.
                      2l
                      <:
                      bool)
                <:
                bool))

val sample_from_binomial_distribution_3_ (randomness: t_Slice u8)
    : Prims.Pure Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
      (requires (Core.Slice.impl__len randomness <: usize) =. (sz 3 *! sz 64 <: usize))
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
                  (fun temp_0_ ->
                      let _:Prims.unit = temp_0_ in
                      (Core.Num.impl__i32__abs (result.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[
                              i ]
                            <:
                            i32)
                        <:
                        i32) <=.
                      3l
                      <:
                      bool)
                <:
                bool))

val sample_from_binomial_distribution (v_ETA: usize) (randomness: t_Slice u8)
    : Prims.Pure Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
      Prims.l_True
      (fun _ -> Prims.l_True)

val sample_from_uniform_distribution (randomness: t_Array u8 (sz 840))
    : Prims.Pure Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
      Prims.l_True
      (fun _ -> Prims.l_True)
