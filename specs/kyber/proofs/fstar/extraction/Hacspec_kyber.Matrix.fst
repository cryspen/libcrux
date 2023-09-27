module Hacspec_kyber.Matrix
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

let transpose
      (matrix:
          array
            (Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz 3sz)
            3sz)
    : array (Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz 3sz)
      3sz =
  let transpose:array
    (Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz 3sz) 3sz =
    Rust_primitives.Hax.repeat Hacspec_lib.Vector.v_ZERO_under_impl 3sz
  in
  let transpose:array
    (Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz 3sz) 3sz =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter (Core.Iter.Traits.Iterator.Iterator.enumerate
              (Core.Slice.iter_under_impl (Rust_primitives.unsize matrix
                    <:
                    slice
                    (Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
                        256sz
                        3sz))
                <:
                Core.Slice.Iter.t_Iter
                (Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
                    256sz
                    3sz))
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate
            (Core.Slice.Iter.t_Iter
              (Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz 3sz)
            ))
        <:
        _)
      transpose
      (fun transpose (i, row) ->
          Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter (Core.Iter.Traits.Iterator.Iterator.enumerate
                    (Hacspec_lib.Vector.iter_under_impl row
                      <:
                      Core.Slice.Iter.t_Iter
                      (Hacspec_lib.Ring.t_PolynomialRingElement
                          (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz))
                  <:
                  Core.Iter.Adapters.Enumerate.t_Enumerate
                  (Core.Slice.Iter.t_Iter
                    (Hacspec_lib.Ring.t_PolynomialRingElement
                        (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz)))
              <:
              _)
            transpose
            (fun transpose (j, matrix_element) ->
                Rust_primitives.Hax.update_at transpose
                  j
                  (Rust_primitives.Hax.update_at (transpose.[ j ]
                        <:
                        Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
                          256sz
                          3sz)
                      i
                      matrix_element
                    <:
                    Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
                      256sz
                      3sz)
                <:
                array
                  (Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
                      256sz
                      3sz) 3sz)
          <:
          array
            (Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz 3sz)
            3sz)
  in
  transpose

let multiply_matrix_by_column
      (matrix:
          array
            (Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz 3sz)
            3sz)
      (vector: Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz 3sz)
    : Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz 3sz =
  let result:Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz 3sz =
    Hacspec_lib.Vector.v_ZERO_under_impl
  in
  let transposed:array
    (Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz 3sz) 3sz =
    transpose matrix
  in
  let result:Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz 3sz =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter (Core.Iter.Traits.Iterator.Iterator.enumerate
              (Core.Slice.iter_under_impl (Rust_primitives.unsize transposed
                    <:
                    slice
                    (Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
                        256sz
                        3sz))
                <:
                Core.Slice.Iter.t_Iter
                (Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
                    256sz
                    3sz))
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate
            (Core.Slice.Iter.t_Iter
              (Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz 3sz)
            ))
        <:
        _)
      result
      (fun result (i, row) ->
          Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter (Core.Iter.Traits.Iterator.Iterator.enumerate
                    (Hacspec_lib.Vector.iter_under_impl row
                      <:
                      Core.Slice.Iter.t_Iter
                      (Hacspec_lib.Ring.t_PolynomialRingElement
                          (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz))
                  <:
                  Core.Iter.Adapters.Enumerate.t_Enumerate
                  (Core.Slice.Iter.t_Iter
                    (Hacspec_lib.Ring.t_PolynomialRingElement
                        (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz)))
              <:
              _)
            result
            (fun result (j, matrix_element) ->
                let product:Hacspec_lib.Ring.t_PolynomialRingElement
                  (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz =
                  Hacspec_kyber.Ntt.multiply_ntts matrix_element
                    (vector.[ j ]
                      <:
                      Hacspec_lib.Ring.t_PolynomialRingElement
                        (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz)
                in
                let result:Hacspec_lib.Vector.t_Vector
                  (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz 3sz =
                  Rust_primitives.Hax.update_at result
                    i
                    ((result.[ i ]
                        <:
                        Hacspec_lib.Ring.t_PolynomialRingElement
                          (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz) +.
                      product
                      <:
                      _)
                in
                result)
          <:
          Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz 3sz)
  in
  result

let multiply_column_by_row
      (column_vector row_vector:
          Hacspec_lib.Vector.t_Vector (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz 3sz)
    : Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz =
  let result:Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
    256sz =
    Hacspec_lib.Ring.v_ZERO_under_impl_2
  in
  let result =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter (Core.Iter.Traits.Iterator.Iterator.zip
              (Hacspec_lib.Vector.iter_under_impl column_vector
                <:
                Core.Slice.Iter.t_Iter
                (Hacspec_lib.Ring.t_PolynomialRingElement
                    (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz))
              (Hacspec_lib.Vector.iter_under_impl row_vector
                <:
                Core.Slice.Iter.t_Iter
                (Hacspec_lib.Ring.t_PolynomialRingElement
                    (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz))
            <:
            Core.Iter.Adapters.Zip.t_Zip
              (Core.Slice.Iter.t_Iter
                (Hacspec_lib.Ring.t_PolynomialRingElement
                    (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz)) _)
        <:
        _)
      result
      (fun result (column_element, row_element) ->
          result +.
          (Hacspec_kyber.Ntt.multiply_ntts column_element row_element
            <:
            Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
              256sz)
          <:
          _)
  in
  result