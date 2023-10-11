module Hacspec_kyber.Matrix
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

let transpose
      (matrix:
          array
            (Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
                (sz 256)
                (sz 3)) (sz 3))
    : array
      (Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256) (sz 3))
      (sz 3) =
  let transpose:array
    (Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256) (sz 3))
    (sz 3) =
    Rust_primitives.Hax.repeat Hacspec_lib.Vector.impl__ZERO (sz 3)
  in
  let transpose:array
    (Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256) (sz 3))
    (sz 3) =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
              (Core.Slice.impl__iter (Rust_primitives.unsize matrix
                    <:
                    slice
                    (Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
                        (sz 256)
                        (sz 3)))
                <:
                Core.Slice.Iter.t_Iter
                (Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
                    (sz 256)
                    (sz 3)))
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate
            (Core.Slice.Iter.t_Iter
              (Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
                  (sz 256)
                  (sz 3))))
        <:
        (Core.Iter.Traits.Collect.impl
          (Core.Iter.Adapters.Enumerate.t_Enumerate
            (Core.Slice.Iter.t_Iter
              (Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
                  (sz 256)
                  (sz 3)))))
          .f_IntoIter)
      transpose
      (fun transpose (i, row) ->
          Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
                    (Hacspec_lib.Vector.impl__iter row
                      <:
                      Core.Slice.Iter.t_Iter
                      (Hacspec_lib.Ring.t_PolynomialRingElement
                          (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256)))
                  <:
                  Core.Iter.Adapters.Enumerate.t_Enumerate
                  (Core.Slice.Iter.t_Iter
                    (Hacspec_lib.Ring.t_PolynomialRingElement
                        (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256))))
              <:
              (Core.Iter.Traits.Collect.impl
                (Core.Iter.Adapters.Enumerate.t_Enumerate
                  (Core.Slice.Iter.t_Iter
                    (Hacspec_lib.Ring.t_PolynomialRingElement
                        (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256)))))
                .f_IntoIter)
            transpose
            (fun transpose (j, matrix_element) ->
                Rust_primitives.Hax.update_at transpose
                  j
                  (Rust_primitives.Hax.update_at (transpose.[ j ]
                        <:
                        Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
                          (sz 256)
                          (sz 3))
                      i
                      matrix_element
                    <:
                    Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
                      (sz 256)
                      (sz 3))
                <:
                array
                  (Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
                      (sz 256)
                      (sz 3)) (sz 3))
          <:
          array
            (Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
                (sz 256)
                (sz 3)) (sz 3))
  in
  transpose

let multiply_matrix_by_column
      (matrix:
          array
            (Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
                (sz 256)
                (sz 3)) (sz 3))
      (vector:
          Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256) (sz 3)
        )
    : Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256) (sz 3) =
  let result:Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
    (sz 256)
    (sz 3) =
    Hacspec_lib.Vector.impl__ZERO
  in
  let transposed:array
    (Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256) (sz 3))
    (sz 3) =
    transpose matrix
  in
  let result:Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
    (sz 256)
    (sz 3) =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
              (Core.Slice.impl__iter (Rust_primitives.unsize transposed
                    <:
                    slice
                    (Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
                        (sz 256)
                        (sz 3)))
                <:
                Core.Slice.Iter.t_Iter
                (Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
                    (sz 256)
                    (sz 3)))
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate
            (Core.Slice.Iter.t_Iter
              (Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
                  (sz 256)
                  (sz 3))))
        <:
        (Core.Iter.Traits.Collect.impl
          (Core.Iter.Adapters.Enumerate.t_Enumerate
            (Core.Slice.Iter.t_Iter
              (Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
                  (sz 256)
                  (sz 3)))))
          .f_IntoIter)
      result
      (fun result (i, row) ->
          Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_enumerate
                    (Hacspec_lib.Vector.impl__iter row
                      <:
                      Core.Slice.Iter.t_Iter
                      (Hacspec_lib.Ring.t_PolynomialRingElement
                          (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256)))
                  <:
                  Core.Iter.Adapters.Enumerate.t_Enumerate
                  (Core.Slice.Iter.t_Iter
                    (Hacspec_lib.Ring.t_PolynomialRingElement
                        (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256))))
              <:
              (Core.Iter.Traits.Collect.impl
                (Core.Iter.Adapters.Enumerate.t_Enumerate
                  (Core.Slice.Iter.t_Iter
                    (Hacspec_lib.Ring.t_PolynomialRingElement
                        (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256)))))
                .f_IntoIter)
            result
            (fun result (j, matrix_element) ->
                let product:Hacspec_lib.Ring.t_PolynomialRingElement
                  (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256) =
                  Hacspec_kyber.Ntt.multiply_ntts matrix_element
                    (vector.[ j ]
                      <:
                      Hacspec_lib.Ring.t_PolynomialRingElement
                        (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256))
                in
                let result:Hacspec_lib.Vector.t_Vector
                  (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256) (sz 3) =
                  Rust_primitives.Hax.update_at result
                    i
                    ((result.[ i ]
                        <:
                        Hacspec_lib.Ring.t_PolynomialRingElement
                          (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256)) +!
                      product
                      <:
                      (Hacspec_lib.Ring.impl_6 (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
                          (sz 256))
                        .f_Output)
                in
                result)
          <:
          Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256) (sz 3)
      )
  in
  result

let multiply_column_by_row
      (column_vector row_vector:
          Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256) (sz 3)
        )
    : Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
      (sz 256) =
  let result:Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
    (sz 256) =
    Hacspec_lib.Ring.impl_2__ZERO
  in
  let result =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.f_into_iter (Core.Iter.Traits.Iterator.f_zip
              (Hacspec_lib.Vector.impl__iter column_vector
                <:
                Core.Slice.Iter.t_Iter
                (Hacspec_lib.Ring.t_PolynomialRingElement
                    (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256)))
              (Hacspec_lib.Vector.impl__iter row_vector
                <:
                Core.Slice.Iter.t_Iter
                (Hacspec_lib.Ring.t_PolynomialRingElement
                    (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256)))
            <:
            Core.Iter.Adapters.Zip.t_Zip
              (Core.Slice.Iter.t_Iter
                (Hacspec_lib.Ring.t_PolynomialRingElement
                    (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256)))
              (Core.Iter.Traits.Collect.impl
                (Core.Slice.Iter.t_Iter
                  (Hacspec_lib.Ring.t_PolynomialRingElement
                      (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256))))
                .f_IntoIter)
        <:
        (Core.Iter.Traits.Collect.impl
          (Core.Iter.Adapters.Zip.t_Zip
              (Core.Slice.Iter.t_Iter
                (Hacspec_lib.Ring.t_PolynomialRingElement
                    (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256)))
              (Core.Slice.Iter.t_Iter
                (Hacspec_lib.Ring.t_PolynomialRingElement
                    (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256)))))
          .f_IntoIter)
      result
      (fun result (column_element, row_element) ->
          result +!
          (Hacspec_kyber.Ntt.multiply_ntts column_element row_element
            <:
            Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
              (sz 256))
          <:
          (Hacspec_lib.Ring.impl_6 (Hacspec_lib.Field.t_PrimeFieldElement 3329us) (sz 256)).f_Output
      )
  in
  result