module Libcrux.Kem.Kyber.Ntt
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul
open Libcrux.Kem.Kyber.Arithmetic

val v_ZETAS_TIMES_MONTGOMERY_R: x:t_Array (i32_b 1664) (sz 128){v (x.[sz 1] <: i32) == -758}

val ntt_multiply_binomials (a:wfFieldElement&wfFieldElement) (b: wfFieldElement&wfFieldElement) (zeta: i32_b 1664) :
    Pure (wfFieldElement & wfFieldElement)
    (requires True)
    (ensures (fun _ -> True))

val invert_ntt_at_layer (#v_K:usize{v v_K >= 1 /\ v v_K <= 4})
      (#b:nat{b <= v v_K * 3328 * 64})
      (zeta_i: usize{v zeta_i >= 1 /\ v zeta_i <= 128})
      (re: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b b)
      (layer: usize{v layer > 0 /\ 
                    v layer <= 7 /\ 
                    v zeta_i == pow2 (8 - v layer) /\ 
                    b == v v_K * 3328 * pow2(v layer - 1)})
    : Prims.Pure (usize & Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b (2*b))
      Prims.l_True
      (fun x -> let (zeta_fin,re) = x in v zeta_fin == pow2 (7 - v layer))

val invert_ntt_montgomery (v_K: usize{v v_K >= 1 /\ v v_K <= 4}) 
      (re: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b (v v_K * 3328))
    : Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b (128 * v v_K * 3328)

val ntt_at_layer 
      (#b:nat{b <= 7*3328})
      (zeta_i: usize{v zeta_i < 128})
      (re: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b b)
      (layer: usize{v layer > 0 /\ 
                    v layer <= 6 /\ 
                    v zeta_i == pow2 (7 - v layer) - 1})
      (initial_coefficient_bound: usize{b == (7 - v layer) * 3328 + v initial_coefficient_bound})
    : Pure (usize & Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b (3328+b))
      (requires True)
      (ensures fun result -> True)

val ntt_at_layer_3_ #b
      (zeta_i: usize)
      (re: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b b)
      (layer: usize)
    : Prims.Pure (usize & Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b (7*3328+3))
      Prims.l_True
      (fun _ -> Prims.l_True)

val ntt_at_layer_3328_ #b 
      (zeta_i: usize)
      (re: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b b)
      (layer: usize)
    : Prims.Pure (usize & Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b (8*3328))
      Prims.l_True
      (fun _ -> Prims.l_True)

val ntt_binomially_sampled_ring_element (re: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b 3)
    : Prims.Pure (Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b (8*3328))
      (requires True)
      (ensures (fun _ -> True))

(*
      (requires
        Hax_lib.v_forall (fun i ->
              let i:usize = i in
              Hax_lib.implies (i <.
                  (Core.Slice.impl__len (Rust_primitives.unsize re
                            .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                        <:
                        t_Slice i32)
                    <:
                    usize)
                  <:
                  bool)
                ((Core.Num.impl__i32__abs (re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ i ]
                        <:
                        i32)
                    <:
                    i32) <=.
                  3l
                  <:
                  bool)
              <:
              bool))
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
                  ((Core.Num.impl__i32__abs (result.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ i
                          ]
                          <:
                          i32)
                      <:
                      i32) <.
                    Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS
                    <:
                    bool)
                <:
                bool)) =
*)


val ntt_multiply (lhs: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b 4095)
                 (rhs: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b 3328)
    : Prims.Pure (Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b 3328)
      (requires True)
      (ensures (fun _ -> True))
    

(*
      (requires
        Hax_lib.v_forall (fun i ->
              let i:usize = i in
              Hax_lib.implies (i <. Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT
                  <:
                  bool)
                (((lhs.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ i ] <: i32) >=. 0l <: bool) &&
                  ((lhs.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ i ] <: i32) <. 4096l <: bool) &&
                  ((Core.Num.impl__i32__abs (rhs.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ i ]
                          <:
                          i32)
                      <:
                      i32) <=.
                    Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS
                    <:
                    bool))
              <:
              bool))
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
                  ((Core.Num.impl__i32__abs (result.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ i
                          ]
                          <:
                          i32)
                      <:
                      i32) <=.
                    Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS
                    <:
                    bool)
                <:
                bool)) =
*)


val ntt_vector_u
      (v_VECTOR_U_COMPRESSION_FACTOR: usize)
      (re: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b 3328)
    : Prims.Pure (Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b (8*3328))
      (requires True)
      (ensures fun _ -> True)

(*
      (requires
        Hax_lib.v_forall (fun i ->
              let i:usize = i in
              Hax_lib.implies (i <.
                  (Core.Slice.impl__len (Rust_primitives.unsize re
                            .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                        <:
                        t_Slice i32)
                    <:
                    usize)
                  <:
                  bool)
                ((Core.Num.impl__i32__abs (re.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ i ]
                        <:
                        i32)
                    <:
                    i32) <=.
                  3328l
                  <:
                  bool)
              <:
              bool))
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
                  ((Core.Num.impl__i32__abs (result.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ i
                          ]
                          <:
                          i32)
                      <:
                      i32) <.
                    Libcrux.Kem.Kyber.Constants.v_FIELD_MODULUS
                    <:
                    bool)
                <:
                bool)) 
*)
