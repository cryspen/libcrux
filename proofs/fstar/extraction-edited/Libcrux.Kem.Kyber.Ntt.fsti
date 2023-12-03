module Libcrux.Kem.Kyber.Ntt
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

val ntt_multiply_binomials (a: (i32 & i32)) (b: (i32 & i32)) (zeta: i32) :
    Pure (i32 & i32)
    (requires True) (* Need to add preconditions on ranges that imply:
      let (a0,a1) = a in
      let (b0,b1) = b in
      (range (v a0 * v b0) i32_inttype) /\
      (range (v a1 * v b1) i32_inttype) /\
      (range (v a0 * v b1) i32_inttype) /\
      (range (v a1 * v b0) i32_inttype) *)
    (ensures (fun _ -> True))
    
val invert_ntt_montgomery (v_K: usize) (re: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement)
    : Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement


val ntt_binomially_sampled_ring_element (re: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement)
    : Prims.Pure Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
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


val ntt_multiply (lhs rhs: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement)
    : Prims.Pure Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
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
      (re: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement)
    : Prims.Pure Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement
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
