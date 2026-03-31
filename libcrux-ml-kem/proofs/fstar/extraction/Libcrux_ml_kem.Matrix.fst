module Libcrux_ml_kem.Matrix
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open FStar.Mul
open Core_models

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_kem.Hash_functions in
  let open Libcrux_ml_kem.Vector.Traits in
  ()

#push-options "--z3rlimit 400 --ext context_pruning --split_queries always"

let sample_matrix_A
      (v_K: usize)
      (#v_Vector #v_Hasher: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K)
      (v_A_transpose:
          t_Array (t_Array (Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector) v_K) v_K)
      (seed: t_Array u8 (mk_usize 34))
      (transpose: bool)
     =
  let v_A_transpose:t_Array (t_Array (Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector) v_K)
    v_K =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      v_K
      (fun v_A_transpose i ->
          let v_A_transpose:t_Array
            (t_Array (Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector) v_K) v_K =
            v_A_transpose
          in
          let i:usize = i in
          if transpose
          then
            forall (k: usize).
              b2t (k <. v_K <: bool) ==>
              (forall (l: usize).
                  b2t (l <. v_K <: bool) ==>
                  (if k <. i
                    then
                      Libcrux_ml_kem.Polynomial.Spec.is_bounded_poly #v_Vector
                        (mk_usize 3328)
                        ((v_A_transpose.[ l ]
                            <:
                            t_Array (Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector) v_K).[ k
                          ]
                          <:
                          Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector)
                    else b2t true))
          else
            forall (k: usize).
              b2t (k <. v_K <: bool) ==>
              (forall (l: usize).
                  b2t (l <. v_K <: bool) ==>
                  (if k <. i
                    then
                      Libcrux_ml_kem.Polynomial.Spec.is_bounded_poly #v_Vector
                        (mk_usize 3328)
                        ((v_A_transpose.[ k ]
                            <:
                            t_Array (Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector) v_K).[ l
                          ]
                          <:
                          Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector)
                    else b2t true)))
      v_A_transpose
      (fun v_A_transpose i ->
          let v_A_transpose:t_Array
            (t_Array (Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector) v_K) v_K =
            v_A_transpose
          in
          let i:usize = i in
          let seeds:t_Array (t_Array u8 (mk_usize 34)) v_K =
            Rust_primitives.Hax.repeat (Core_models.Clone.f_clone #(t_Array u8 (mk_usize 34))
                  #FStar.Tactics.Typeclasses.solve
                  seed
                <:
                t_Array u8 (mk_usize 34))
              v_K
          in
          let seeds:t_Array (t_Array u8 (mk_usize 34)) v_K =
            Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
              v_K
              (fun seeds temp_1_ ->
                  let seeds:t_Array (t_Array u8 (mk_usize 34)) v_K = seeds in
                  let _:usize = temp_1_ in
                  true)
              seeds
              (fun seeds j ->
                  let seeds:t_Array (t_Array u8 (mk_usize 34)) v_K = seeds in
                  let j:usize = j in
                  let seeds:t_Array (t_Array u8 (mk_usize 34)) v_K =
                    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize seeds
                      j
                      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (seeds.[ j ]
                            <:
                            t_Array u8 (mk_usize 34))
                          (mk_usize 32)
                          (cast (i <: usize) <: u8)
                        <:
                        t_Array u8 (mk_usize 34))
                  in
                  let seeds:t_Array (t_Array u8 (mk_usize 34)) v_K =
                    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize seeds
                      j
                      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (seeds.[ j ]
                            <:
                            t_Array u8 (mk_usize 34))
                          (mk_usize 33)
                          (cast (j <: usize) <: u8)
                        <:
                        t_Array u8 (mk_usize 34))
                  in
                  seeds)
          in
          let sampled:t_Array (Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector) v_K =
            Libcrux_ml_kem.Sampling.sample_from_xof v_K #v_Vector #v_Hasher seeds
          in
          Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
            v_K
            (fun v_A_transpose j ->
                let v_A_transpose:t_Array
                  (t_Array (Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector) v_K) v_K =
                  v_A_transpose
                in
                let j:usize = j in
                if transpose
                then
                  forall (k: usize).
                    b2t (k <. v_K <: bool) ==>
                    (forall (l: usize).
                        b2t (l <. v_K <: bool) ==>
                        (if k <. i || k =. i && l <. j
                          then
                            Libcrux_ml_kem.Polynomial.Spec.is_bounded_poly #v_Vector
                              (mk_usize 3328)
                              ((v_A_transpose.[ l ]
                                  <:
                                  t_Array (Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector)
                                    v_K).[ k ]
                                <:
                                Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector)
                          else b2t true))
                else
                  forall (k: usize).
                    b2t (k <. v_K <: bool) ==>
                    (forall (l: usize).
                        b2t (l <. v_K <: bool) ==>
                        (if k <. i || k =. i && l <. j
                          then
                            Libcrux_ml_kem.Polynomial.Spec.is_bounded_poly #v_Vector
                              (mk_usize 3328)
                              ((v_A_transpose.[ k ]
                                  <:
                                  t_Array (Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector)
                                    v_K).[ l ]
                                <:
                                Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector)
                          else b2t true)))
            v_A_transpose
            (fun v_A_transpose j ->
                let v_A_transpose:t_Array
                  (t_Array (Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector) v_K) v_K =
                  v_A_transpose
                in
                let j:usize = j in
                if transpose
                then
                  let v_A_transpose:t_Array
                    (t_Array (Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector) v_K) v_K =
                    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A_transpose
                      j
                      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A_transpose.[ j
                            ]
                            <:
                            t_Array (Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector) v_K)
                          i
                          (sampled.[ j ] <: Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector)
                        <:
                        t_Array (Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector) v_K)
                  in
                  v_A_transpose
                else
                  let v_A_transpose:t_Array
                    (t_Array (Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector) v_K) v_K =
                    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v_A_transpose
                      i
                      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (v_A_transpose.[ i
                            ]
                            <:
                            t_Array (Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector) v_K)
                          j
                          (sampled.[ j ] <: Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector)
                        <:
                        t_Array (Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector) v_K)
                  in
                  v_A_transpose))
  in
  v_A_transpose

#pop-options

#push-options "--z3rlimit 200 --ext context_pruning"

let compute_message
      (v_K: usize)
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (v: Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector)
      (secret_as_ntt u_as_ntt: t_Array (Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector) v_K)
     =
  let result:Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector =
    Libcrux_ml_kem.Polynomial.impl__ZERO #v_Vector ()
  in
  let _:Prims.unit =
    Hax_lib.assert_prop (Libcrux_ml_kem.Polynomial.Spec.is_bounded_poly #v_Vector
          (mk_usize 0)
          result)
  in
  let _:Prims.unit = () in
  let result:Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      v_K
      (fun result i ->
          let result:Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector = result in
          let i:usize = i in
          Libcrux_ml_kem.Polynomial.Spec.is_bounded_poly #v_Vector
            (i *! mk_usize 3328 <: usize)
            result)
      result
      (fun result i ->
          let result:Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector = result in
          let i:usize = i in
          let product:Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector =
            Libcrux_ml_kem.Polynomial.impl__ntt_multiply #v_Vector
              (secret_as_ntt.[ i ] <: Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector)
              (u_as_ntt.[ i ] <: Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector)
          in
          let result:Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector =
            Libcrux_ml_kem.Polynomial.impl__add_to_ring_element #v_Vector
              result
              product
              (i *! mk_usize 3328 <: usize)
          in
          result)
  in
  let result:Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector =
    Libcrux_ml_kem.Invert_ntt.invert_ntt_montgomery v_K #v_Vector result
  in
  let result:Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector =
    Libcrux_ml_kem.Polynomial.impl__subtract_reduce #v_Vector v result
  in
  result

#pop-options

#push-options "--z3rlimit 200 --ext context_pruning"

let compute_ring_element_v
      (v_K: usize)
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (tt_as_ntt r_as_ntt: t_Array (Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector) v_K)
      (error_2_ message: Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector)
     =
  let result:Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector =
    Libcrux_ml_kem.Polynomial.impl__ZERO #v_Vector ()
  in
  let result:Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      v_K
      (fun result i ->
          let result:Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector = result in
          let i:usize = i in
          Libcrux_ml_kem.Polynomial.Spec.is_bounded_poly #v_Vector
            (i *! mk_usize 3328 <: usize)
            result)
      result
      (fun result i ->
          let result:Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector = result in
          let i:usize = i in
          let product:Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector =
            Libcrux_ml_kem.Polynomial.impl__ntt_multiply #v_Vector
              (tt_as_ntt.[ i ] <: Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector)
              (r_as_ntt.[ i ] <: Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector)
          in
          let result:Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector =
            Libcrux_ml_kem.Polynomial.impl__add_to_ring_element #v_Vector
              result
              product
              (i *! mk_usize 3328 <: usize)
          in
          result)
  in
  let result:Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector =
    Libcrux_ml_kem.Invert_ntt.invert_ntt_montgomery v_K #v_Vector result
  in
  let result:Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector =
    Libcrux_ml_kem.Polynomial.impl__add_message_error_reduce #v_Vector error_2_ message result
  in
  result

#pop-options

#push-options "--z3rlimit 200 --ext context_pruning"

let compute_vector_u
      (v_K: usize)
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (a_as_ntt: t_Array (t_Array (Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector) v_K) v_K)
      (r_as_ntt error_1_: t_Array (Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector) v_K)
     =
  let result:t_Array (Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector) v_K =
    Core_models.Array.from_fn #(Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector)
      v_K
      #(usize -> Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector)
      (fun e_i ->
          let e_i:usize = e_i in
          Libcrux_ml_kem.Polynomial.impl__ZERO #v_Vector ()
          <:
          Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector)
  in
  let result:t_Array (Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector) v_K =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      v_K
      (fun result i ->
          let result:t_Array (Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector) v_K =
            result
          in
          let i:usize = i in
          forall (j: usize).
            if j <. v_K
            then
              if j <. i
              then
                Libcrux_ml_kem.Polynomial.Spec.is_bounded_poly #v_Vector
                  (mk_usize 3328)
                  (result.[ j ] <: Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector)
              else
                Libcrux_ml_kem.Polynomial.Spec.is_bounded_poly #v_Vector
                  (mk_usize 0)
                  (result.[ j ] <: Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector)
            else b2t true)
      result
      (fun result i ->
          let result:t_Array (Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector) v_K =
            result
          in
          let i:usize = i in
          let e_result:t_Array (Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector) v_K =
            result
          in
          let result:t_Array (Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector) v_K =
            Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
              v_K
              (fun result j ->
                  let result:t_Array (Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector) v_K =
                    result
                  in
                  let j:usize = j in
                  Libcrux_ml_kem.Polynomial.Spec.is_bounded_poly #v_Vector
                    (j *! mk_usize 3328 <: usize)
                    (result.[ i ] <: Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector) /\
                  (forall (k: usize).
                      b2t ((k <. v_K <: bool) && (k <>. i <: bool)) ==>
                      (result.[ k ] <: Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector) ==
                      (e_result.[ k ] <: Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector)))
              result
              (fun result j ->
                  let result:t_Array (Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector) v_K =
                    result
                  in
                  let j:usize = j in
                  let product:Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector =
                    Libcrux_ml_kem.Polynomial.impl__ntt_multiply #v_Vector
                      ((a_as_ntt.[ i ]
                          <:
                          t_Array (Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector) v_K).[ j
                        ]
                        <:
                        Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector)
                      (r_as_ntt.[ j ] <: Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector)
                  in
                  let result:t_Array (Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector) v_K =
                    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
                      i
                      (Libcrux_ml_kem.Polynomial.impl__add_to_ring_element #v_Vector
                          (result.[ i ] <: Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector)
                          product
                          (j *! mk_usize 3328 <: usize)
                        <:
                        Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector)
                  in
                  result)
          in
          let result:t_Array (Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector) v_K =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
              i
              (Libcrux_ml_kem.Invert_ntt.invert_ntt_montgomery v_K
                  #v_Vector
                  (result.[ i ] <: Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector)
                <:
                Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector)
          in
          let result:t_Array (Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector) v_K =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
              i
              (Libcrux_ml_kem.Polynomial.impl__add_error_reduce #v_Vector
                  (result.[ i ] <: Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector)
                  (error_1_.[ i ] <: Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector)
                <:
                Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector)
          in
          result)
  in
  result

#pop-options

#push-options "--z3rlimit 200 --ext context_pruning"

let compute_As_plus_e
      (v_K: usize)
      (#v_Vector: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector)
      (tt_as_ntt: t_Array (Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector) v_K)
      (matrix_A: t_Array (t_Array (Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector) v_K) v_K)
      (s_as_ntt error_as_ntt: t_Array (Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector) v_K)
     =
  let tt_as_ntt:t_Array (Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector) v_K =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      v_K
      (fun tt_as_ntt i ->
          let tt_as_ntt:t_Array (Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector) v_K =
            tt_as_ntt
          in
          let i:usize = i in
          forall (j: usize).
            b2t (j <. i <: bool) ==>
            Libcrux_ml_kem.Polynomial.Spec.is_bounded_poly #v_Vector
              (mk_usize 3328)
              (tt_as_ntt.[ j ] <: Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector))
      tt_as_ntt
      (fun tt_as_ntt i ->
          let tt_as_ntt:t_Array (Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector) v_K =
            tt_as_ntt
          in
          let i:usize = i in
          let tt_as_ntt:t_Array (Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector) v_K =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize tt_as_ntt
              i
              (Libcrux_ml_kem.Polynomial.impl__ZERO #v_Vector ()
                <:
                Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector)
          in
          let tt_as_ntt:t_Array (Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector) v_K =
            Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
              v_K
              (fun tt_as_ntt j ->
                  let tt_as_ntt:t_Array (Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector) v_K
                  =
                    tt_as_ntt
                  in
                  let j:usize = j in
                  Libcrux_ml_kem.Polynomial.Spec.is_bounded_poly #v_Vector
                    (j *! mk_usize 3328 <: usize)
                    (tt_as_ntt.[ i ] <: Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector) /\
                  (forall (k: usize).
                      b2t (k <. i <: bool) ==>
                      Libcrux_ml_kem.Polynomial.Spec.is_bounded_poly #v_Vector
                        (mk_usize 3328)
                        (tt_as_ntt.[ k ] <: Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector))
              )
              tt_as_ntt
              (fun tt_as_ntt j ->
                  let tt_as_ntt:t_Array (Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector) v_K
                  =
                    tt_as_ntt
                  in
                  let j:usize = j in
                  let product:Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector =
                    Libcrux_ml_kem.Polynomial.impl__ntt_multiply #v_Vector
                      ((matrix_A.[ i ]
                          <:
                          t_Array (Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector) v_K).[ j
                        ]
                        <:
                        Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector)
                      (s_as_ntt.[ j ] <: Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector)
                  in
                  let tt_as_ntt:t_Array (Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector) v_K
                  =
                    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize tt_as_ntt
                      i
                      (Libcrux_ml_kem.Polynomial.impl__add_to_ring_element #v_Vector
                          (tt_as_ntt.[ i ] <: Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector
                          )
                          product
                          (j *! mk_usize 3328 <: usize)
                        <:
                        Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector)
                  in
                  tt_as_ntt)
          in
          let tt_as_ntt:t_Array (Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector) v_K =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize tt_as_ntt
              i
              (Libcrux_ml_kem.Polynomial.impl__add_standard_error_reduce #v_Vector
                  (tt_as_ntt.[ i ] <: Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector)
                  (error_as_ntt.[ i ] <: Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector)
                <:
                Libcrux_ml_kem.Vector.t_PolynomialRingElement v_Vector)
          in
          tt_as_ntt)
  in
  tt_as_ntt

#pop-options
