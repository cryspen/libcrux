module Libcrux_ml_kem.Matrix
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let compute_As_plus_e
      (v_K: usize)
      (#v_Vector: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Simd.Simd_trait.t_Operations v_Vector)
      (matrix_A:
          t_Array (t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K) v_K)
      (s_as_ntt error_as_ntt:
          t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K)
     =
  let result:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K =
    Rust_primitives.Hax.repeat (Libcrux_ml_kem.Polynomial.impl__ZERO ()
        <:
        Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      v_K
  in
  let result:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
              (Core.Slice.impl__iter (Rust_primitives.unsize matrix_A
                    <:
                    t_Slice
                    (t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K))
                <:
                Core.Slice.Iter.t_Iter
                (t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K))
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate
            (Core.Slice.Iter.t_Iter
              (t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K)))
        <:
        Core.Iter.Adapters.Enumerate.t_Enumerate
        (Core.Slice.Iter.t_Iter
          (t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K)))
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
            Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
                      (Core.Slice.impl__iter (Rust_primitives.unsize row
                            <:
                            t_Slice (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector))
                        <:
                        Core.Slice.Iter.t_Iter
                        (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector))
                    <:
                    Core.Iter.Adapters.Enumerate.t_Enumerate
                    (Core.Slice.Iter.t_Iter
                      (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)))
                <:
                Core.Iter.Adapters.Enumerate.t_Enumerate
                (Core.Slice.Iter.t_Iter (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
                ))
              result
              (fun result temp_1_ ->
                  let result:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
                    v_K =
                    result
                  in
                  let j, matrix_element:(usize &
                    Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) =
                    temp_1_
                  in
                  let product:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
                    Libcrux_ml_kem.Polynomial.impl__ntt_multiply matrix_element
                      (s_as_ntt.[ j ] <: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
                  in
                  let result:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
                    v_K =
                    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
                      i
                      (Libcrux_ml_kem.Polynomial.impl__add_to_ring_element v_K
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
              (Libcrux_ml_kem.Polynomial.impl__add_standard_error_reduce (error_as_ntt.[ i ]
                    <:
                    Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
                  (result.[ i ] <: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
                <:
                Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
          in
          result)
  in
  result

let compute_message
      (v_K: usize)
      (#v_Vector: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Simd.Simd_trait.t_Operations v_Vector)
      (v: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (secret_as_ntt u_as_ntt:
          t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K)
     =
  let result:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
    Libcrux_ml_kem.Polynomial.impl__ZERO ()
  in
  let result:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = v_K
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      result
      (fun result i ->
          let result:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = result in
          let i:usize = i in
          let product:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
            Libcrux_ml_kem.Polynomial.impl__ntt_multiply (secret_as_ntt.[ i ]
                <:
                Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
              (u_as_ntt.[ i ] <: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
          in
          let result:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
            Libcrux_ml_kem.Polynomial.impl__add_to_ring_element v_K result product
          in
          result)
  in
  let result:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
    Libcrux_ml_kem.Ntt.impl__invert_ntt_montgomery v_K result
  in
  let result:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
    Libcrux_ml_kem.Polynomial.impl__subtract_reduce v result
  in
  result

let compute_ring_element_v
      (v_K: usize)
      (#v_Vector: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Simd.Simd_trait.t_Operations v_Vector)
      (tt_as_ntt r_as_ntt: t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K)
      (error_2_ message: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
     =
  let result:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
    Libcrux_ml_kem.Polynomial.impl__ZERO ()
  in
  let result:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = v_K
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      result
      (fun result i ->
          let result:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = result in
          let i:usize = i in
          let product:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
            Libcrux_ml_kem.Polynomial.impl__ntt_multiply (tt_as_ntt.[ i ]
                <:
                Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
              (r_as_ntt.[ i ] <: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
          in
          let result:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
            Libcrux_ml_kem.Polynomial.impl__add_to_ring_element v_K result product
          in
          result)
  in
  let result:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
    Libcrux_ml_kem.Ntt.impl__invert_ntt_montgomery v_K result
  in
  let result:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector =
    Libcrux_ml_kem.Polynomial.impl__add_message_error_reduce error_2_ message result
  in
  result

let compute_vector_u
      (v_K: usize)
      (#v_Vector: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Simd.Simd_trait.t_Operations v_Vector)
      (a_as_ntt:
          t_Array (t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K) v_K)
      (r_as_ntt error_1_: t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K)
     =
  let result:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K =
    Rust_primitives.Hax.repeat (Libcrux_ml_kem.Polynomial.impl__ZERO ()
        <:
        Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      v_K
  in
  let result:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
              (Core.Slice.impl__iter (Rust_primitives.unsize a_as_ntt
                    <:
                    t_Slice
                    (t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K))
                <:
                Core.Slice.Iter.t_Iter
                (t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K))
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate
            (Core.Slice.Iter.t_Iter
              (t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K)))
        <:
        Core.Iter.Adapters.Enumerate.t_Enumerate
        (Core.Slice.Iter.t_Iter
          (t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K)))
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
            Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
                      (Core.Slice.impl__iter (Rust_primitives.unsize row
                            <:
                            t_Slice (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector))
                        <:
                        Core.Slice.Iter.t_Iter
                        (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector))
                    <:
                    Core.Iter.Adapters.Enumerate.t_Enumerate
                    (Core.Slice.Iter.t_Iter
                      (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)))
                <:
                Core.Iter.Adapters.Enumerate.t_Enumerate
                (Core.Slice.Iter.t_Iter (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
                ))
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
                    Libcrux_ml_kem.Polynomial.impl__ntt_multiply a_element
                      (r_as_ntt.[ j ] <: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
                  in
                  let result:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
                    v_K =
                    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
                      i
                      (Libcrux_ml_kem.Polynomial.impl__add_to_ring_element v_K
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
              (Libcrux_ml_kem.Ntt.impl__invert_ntt_montgomery v_K
                  (result.[ i ] <: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
                <:
                Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
          in
          let result:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize result
              i
              (Libcrux_ml_kem.Polynomial.impl__add_error_reduce (error_1_.[ i ]
                    <:
                    Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
                  (result.[ i ] <: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
                <:
                Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
          in
          result)
  in
  result

let sample_matrix_A
      (v_K: usize)
      (#v_Vector: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i1:
          Libcrux_ml_kem.Simd.Simd_trait.t_Operations v_Vector)
      (seed: t_Array u8 (sz 34))
      (transpose: bool)
     =
  let v_A_transpose:t_Array
    (t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K) v_K =
    Rust_primitives.Hax.repeat (Rust_primitives.Hax.repeat (Libcrux_ml_kem.Polynomial.impl__ZERO ()
            <:
            Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
          v_K
        <:
        t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K)
      v_K
  in
  let v_A_transpose:t_Array
    (t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K) v_K =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = v_K
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      v_A_transpose
      (fun v_A_transpose i ->
          let v_A_transpose:t_Array
            (t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K) v_K =
            v_A_transpose
          in
          let i:usize = i in
          let seeds:t_Array (t_Array u8 (sz 34)) v_K = Rust_primitives.Hax.repeat seed v_K in
          let seeds:t_Array (t_Array u8 (sz 34)) v_K =
            Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
                      Core.Ops.Range.f_start = sz 0;
                      Core.Ops.Range.f_end = v_K
                    }
                    <:
                    Core.Ops.Range.t_Range usize)
                <:
                Core.Ops.Range.t_Range usize)
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
            Libcrux_ml_kem.Sampling.sample_from_xof v_K seeds
          in
          Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
                    Core.Ops.Range.f_start = sz 0;
                    Core.Ops.Range.f_end = v_K
                  }
                  <:
                  Core.Ops.Range.t_Range usize)
              <:
              Core.Ops.Range.t_Range usize)
            v_A_transpose
            (fun v_A_transpose j ->
                let v_A_transpose:t_Array
                  (t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K) v_K =
                  v_A_transpose
                in
                let j:usize = j in
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
                          (sampled.[ j ]
                            <:
                            Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
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
                          (sampled.[ j ]
                            <:
                            Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
                        <:
                        t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K)
                  in
                  v_A_transpose))
  in
  v_A_transpose
