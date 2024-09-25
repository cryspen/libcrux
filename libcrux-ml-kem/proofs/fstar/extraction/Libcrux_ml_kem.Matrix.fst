module Libcrux_ml_kem.Matrix
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_kem.Hash_functions in
  let open Libcrux_ml_kem.Vector.Traits in
  ()

let compute_As_plus_e
      (v_K: usize)
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (tt_as_ntt: t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K)
      (matrix_A:
          t_Array (t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K) v_K)
      (s_as_ntt error_as_ntt:
          t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K)
     =
  let tt_as_ntt:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K =
    Rust_primitives.Hax.Folds.fold_enumerated_slice (matrix_A
        <:
        t_Slice (t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K))
      (fun tt_as_ntt temp_1_ ->
          let tt_as_ntt:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K =
            tt_as_ntt
          in
          let _:usize = temp_1_ in
          true)
      tt_as_ntt
      (fun tt_as_ntt temp_1_ ->
          let tt_as_ntt:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K =
            tt_as_ntt
          in
          let i, row:(usize &
            t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K) =
            temp_1_
          in
          let tt_as_ntt:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize tt_as_ntt
              i
              (Libcrux_ml_kem.Polynomial.impl__ZERO #v_Vector ()
                <:
                Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
          in
          let tt_as_ntt:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K =
            Rust_primitives.Hax.Folds.fold_enumerated_slice (row
                <:
                t_Slice (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector))
              (fun tt_as_ntt temp_1_ ->
                  let tt_as_ntt:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
                    v_K =
                    tt_as_ntt
                  in
                  let _:usize = temp_1_ in
                  true)
              tt_as_ntt
              (fun tt_as_ntt temp_1_ ->
                  let tt_as_ntt:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
                    v_K =
                    tt_as_ntt
                  in
                  let j, matrix_element:(usize &
                    Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
                    temp_1_
                  in
                  let product:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
                    Libcrux_ml_kem.Polynomial.impl__ntt_multiply #v_Vector
                      matrix_element
                      (s_as_ntt.[ j ] <: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
                  in
                  let tt_as_ntt:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
                    v_K =
                    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize tt_as_ntt
                      i
                      (Libcrux_ml_kem.Polynomial.impl__add_to_ring_element #v_Vector
                          v_K
                          (tt_as_ntt.[ i ]
                            <:
                            Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
                          product
                        <:
                        Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
                  in
                  tt_as_ntt)
          in
          let tt_as_ntt:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize tt_as_ntt
              i
              (Libcrux_ml_kem.Polynomial.impl__add_standard_error_reduce #v_Vector
                  (tt_as_ntt.[ i ] <: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
                  (error_as_ntt.[ i ] <: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
                <:
                Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
          in
          tt_as_ntt)
  in
  let hax_temp_output:Prims.unit = () <: Prims.unit in
  tt_as_ntt

let compute_ring_element_v
      (v_K: usize)
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (tt_as_ntt r_as_ntt: t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K)
      (error_2_ message: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
     =
  let result:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
    Libcrux_ml_kem.Polynomial.impl__ZERO #v_Vector ()
  in
  let result:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      v_K
      (fun result temp_1_ ->
          let result:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = result in
          let _:usize = temp_1_ in
          true)
      result
      (fun result i ->
          let result:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = result in
          let i:usize = i in
          let product:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
            Libcrux_ml_kem.Polynomial.impl__ntt_multiply #v_Vector
              (tt_as_ntt.[ i ] <: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
              (r_as_ntt.[ i ] <: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
          in
          let result:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
            Libcrux_ml_kem.Polynomial.impl__add_to_ring_element #v_Vector v_K result product
          in
          result)
  in
  let result:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
    Libcrux_ml_kem.Invert_ntt.invert_ntt_montgomery v_K #v_Vector result
  in
  let result:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
    Libcrux_ml_kem.Polynomial.impl__add_message_error_reduce #v_Vector error_2_ message result
  in
  result

let compute_vector_u
      (v_K: usize)
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (a_as_ntt:
          t_Array (t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K) v_K)
      (r_as_ntt error_1_: t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K)
     =
  let result:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K =
    Core.Array.from_fn #(Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      v_K
      (fun v__i ->
          let v__i:usize = v__i in
          Libcrux_ml_kem.Polynomial.impl__ZERO #v_Vector ()
          <:
          Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
  in
  let result:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K =
    Rust_primitives.Hax.Folds.fold_enumerated_slice (a_as_ntt
        <:
        t_Slice (t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K))
      (fun result temp_1_ ->
          let result:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K =
            result
          in
          let _:usize = temp_1_ in
          true)
      result
      (fun result temp_1_ ->
          let result:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K =
            result
          in
          let i, row:(usize &
            t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K) =
            temp_1_
          in
          let result:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K =
            Rust_primitives.Hax.Folds.fold_enumerated_slice (row
                <:
                t_Slice (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector))
              (fun result temp_1_ ->
                  let result:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
                    v_K =
                    result
                  in
                  let _:usize = temp_1_ in
                  true)
              result
              (fun result temp_1_ ->
                  let result:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
                    v_K =
                    result
                  in
                  let j, a_element:(usize &
                    Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
                    temp_1_
                  in
                  let product:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
                    Libcrux_ml_kem.Polynomial.impl__ntt_multiply #v_Vector
                      a_element
                      (r_as_ntt.[ j ] <: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
                  in
                  let result:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
                    v_K =
                    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
                      i
                      (Libcrux_ml_kem.Polynomial.impl__add_to_ring_element #v_Vector
                          v_K
                          (result.[ i ]
                            <:
                            Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
                          product
                        <:
                        Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
                  in
                  result)
          in
          let result:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
              i
              (Libcrux_ml_kem.Invert_ntt.invert_ntt_montgomery v_K
                  #v_Vector
                  (result.[ i ] <: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
                <:
                Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
          in
          let result:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
              i
              (Libcrux_ml_kem.Polynomial.impl__add_error_reduce #v_Vector
                  (result.[ i ] <: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
                  (error_1_.[ i ] <: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
                <:
                Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
          in
          result)
  in
  result

let compute_message
      (v_K: usize)
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (v: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (secret_as_ntt u_as_ntt:
          t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K)
     =
  let result:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
    Libcrux_ml_kem.Polynomial.impl__ZERO #v_Vector ()
  in
  let result:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      v_K
      (fun result temp_1_ ->
          let result:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = result in
          let _:usize = temp_1_ in
          true)
      result
      (fun result i ->
          let result:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = result in
          let i:usize = i in
          let product:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
            Libcrux_ml_kem.Polynomial.impl__ntt_multiply #v_Vector
              (secret_as_ntt.[ i ] <: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
              (u_as_ntt.[ i ] <: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
          in
          let result:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
            Libcrux_ml_kem.Polynomial.impl__add_to_ring_element #v_Vector v_K result product
          in
          result)
  in
  let result:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
    Libcrux_ml_kem.Invert_ntt.invert_ntt_montgomery v_K #v_Vector result
  in
  let result:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
    Libcrux_ml_kem.Polynomial.impl__subtract_reduce #v_Vector v result
  in
  result

let sample_matrix_A
      (v_K: usize)
      (#v_Vector #v_Hasher: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i2:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i3:
          Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K)
      (v_A_transpose:
          t_Array (t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K) v_K)
      (seed: t_Array u8 (sz 34))
      (transpose: bool)
     =
  let v_A_transpose:t_Array
    (t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K) v_K =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      v_K
      (fun v_A_transpose temp_1_ ->
          let v_A_transpose:t_Array
            (t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K) v_K =
            v_A_transpose
          in
          let _:usize = temp_1_ in
          true)
      v_A_transpose
      (fun v_A_transpose i ->
          let v_A_transpose:t_Array
            (t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K) v_K =
            v_A_transpose
          in
          let i:usize = i in
          let seeds:t_Array (t_Array u8 (sz 34)) v_K = Rust_primitives.Hax.repeat seed v_K in
          let seeds:t_Array (t_Array u8 (sz 34)) v_K =
            Rust_primitives.Hax.Folds.fold_range (sz 0)
              v_K
              (fun seeds temp_1_ ->
                  let seeds:t_Array (t_Array u8 (sz 34)) v_K = seeds in
                  let _:usize = temp_1_ in
                  true)
              seeds
              (fun seeds j ->
                  let seeds:t_Array (t_Array u8 (sz 34)) v_K = seeds in
                  let j:usize = j in
                  let seeds:t_Array (t_Array u8 (sz 34)) v_K =
                    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize seeds
                      j
                      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (seeds.[ j ]
                            <:
                            t_Array u8 (sz 34))
                          (sz 32)
                          (cast (i <: usize) <: u8)
                        <:
                        t_Array u8 (sz 34))
                  in
                  let seeds:t_Array (t_Array u8 (sz 34)) v_K =
                    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize seeds
                      j
                      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (seeds.[ j ]
                            <:
                            t_Array u8 (sz 34))
                          (sz 33)
                          (cast (j <: usize) <: u8)
                        <:
                        t_Array u8 (sz 34))
                  in
                  seeds)
          in
          let sampled:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K =
            Libcrux_ml_kem.Sampling.sample_from_xof v_K #v_Vector #v_Hasher seeds
          in
          Rust_primitives.Hax.Folds.fold_enumerated_slice sampled
            (fun v_A_transpose temp_1_ ->
                let v_A_transpose:t_Array
                  (t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K) v_K =
                  v_A_transpose
                in
                let _:usize = temp_1_ in
                true)
            v_A_transpose
            (fun v_A_transpose temp_1_ ->
                let v_A_transpose:t_Array
                  (t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K) v_K =
                  v_A_transpose
                in
                let j, sample:(usize & Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
                  temp_1_
                in
                if transpose
                then
                  let v_A_transpose:t_Array
                    (t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K) v_K =
                    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A_transpose
                      j
                      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A_transpose.[ j
                            ]
                            <:
                            t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K
                          )
                          i
                          sample
                        <:
                        t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K)
                  in
                  v_A_transpose
                else
                  let v_A_transpose:t_Array
                    (t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K) v_K =
                    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A_transpose
                      i
                      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A_transpose.[ i
                            ]
                            <:
                            t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K
                          )
                          j
                          sample
                        <:
                        t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K)
                  in
                  v_A_transpose))
  in
  let hax_temp_output:Prims.unit = () <: Prims.unit in
  v_A_transpose
