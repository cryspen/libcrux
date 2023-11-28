module Libcrux.Kem.Kyber.Matrix
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let compute_As_plus_e
      (v_K: usize)
      (matrix_A: t_Array (t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K) v_K)
      (s_as_ntt error_as_ntt: t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K)
    : FStar.HyperStack.ST.St (t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K) =
  let result:t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K =
    Rust_primitives.Hax.repeat Libcrux.Kem.Kyber.Arithmetic.impl__PolynomialRingElement__ZERO v_K
  in
  let _:Prims.unit =
    Rust_primitives.f_for_loop (sz 0)
      (Core.Slice.impl__len (Rust_primitives.unsize matrix_A
            <:
            t_Slice (t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K))
        <:
        usize)
      (fun i ->
          let i:usize = i in
          let row:t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K =
            matrix_A.[ i ]
          in
          let _:Prims.unit =
            Rust_primitives.f_for_loop (sz 0)
              (Core.Slice.impl__len (Rust_primitives.unsize row
                    <:
                    t_Slice Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement)
                <:
                usize)
              (fun j ->
                  let j:usize = j in
                  let matrix_element:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
                    row.[ j ]
                  in
                  let product:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
                    Libcrux.Kem.Kyber.Ntt.ntt_multiply matrix_element
                      (s_as_ntt.[ j ] <: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement)
                  in
                  let _:Prims.unit =
                    Libcrux.Kem.Kyber.Arithmetic.add_to_ring_element v_K
                      (result.[ i ] <: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement)
                      product
                  in
                  ())
          in
          Rust_primitives.f_for_loop (sz 0)
            Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT
            (fun j ->
                let j:usize = j in
                let result_i:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement = result.[ i ] in
                let error_as_ntt_i:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
                  error_as_ntt.[ i ]
                in
                let coefficient_normal_form:i32 =
                  Libcrux.Kem.Kyber.Arithmetic.to_standard_domain (result_i
                        .Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ j ]
                      <:
                      i32)
                in
                Rust_primitives.Hax.Monomorphized_update_at.update_array_at_usize (result.[ i ]
                    <:
                    Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement)
                    .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                  j
                  (Libcrux.Kem.Kyber.Arithmetic.barrett_reduce (coefficient_normal_form +!
                        (error_as_ntt_i.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ j ] <: i32)
                        <:
                        i32)
                    <:
                    i32)))
  in
  result

let compute_message
      (v_K: usize)
      (v: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement)
      (secret_as_ntt u_as_ntt: t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K)
    : FStar.HyperStack.ST.St Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
  let result:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
    Libcrux.Kem.Kyber.Arithmetic.impl__PolynomialRingElement__ZERO
  in
  let _:Prims.unit =
    Rust_primitives.f_for_loop (sz 0)
      v_K
      (fun i ->
          let i:usize = i in
          let product:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
            Libcrux.Kem.Kyber.Ntt.ntt_multiply (secret_as_ntt.[ i ]
                <:
                Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement)
              (u_as_ntt.[ i ] <: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement)
          in
          let _:Prims.unit = Libcrux.Kem.Kyber.Arithmetic.add_to_ring_element v_K result product in
          ())
  in
  let _:Prims.unit = Libcrux.Kem.Kyber.Ntt.invert_ntt_montgomery v_K result in
  let _:Prims.unit =
    Rust_primitives.f_for_loop (sz 0)
      Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT
      (fun i ->
          let i:usize = i in
          let coefficient_normal_form:i32 =
            Libcrux.Kem.Kyber.Arithmetic.montgomery_reduce ((result
                    .Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ i ]
                  <:
                  i32) *!
                1441l
                <:
                i32)
          in
          let _:Prims.unit =
            Rust_primitives.Hax.Monomorphized_update_at.update_array_at_usize result
                .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              i
              (Libcrux.Kem.Kyber.Arithmetic.barrett_reduce ((v
                        .Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ i ]
                      <:
                      i32) -!
                    coefficient_normal_form
                    <:
                    i32)
                <:
                i32)
          in
          ())
  in
  result

let compute_ring_element_v
      (v_K: usize)
      (tt_as_ntt r_as_ntt: t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K)
      (error_2_ message: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement)
    : FStar.HyperStack.ST.St Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
  let result:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
    Libcrux.Kem.Kyber.Arithmetic.impl__PolynomialRingElement__ZERO
  in
  let _:Prims.unit =
    Rust_primitives.f_for_loop (sz 0)
      v_K
      (fun i ->
          let i:usize = i in
          let product:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
            Libcrux.Kem.Kyber.Ntt.ntt_multiply (tt_as_ntt.[ i ]
                <:
                Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement)
              (r_as_ntt.[ i ] <: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement)
          in
          let _:Prims.unit = Libcrux.Kem.Kyber.Arithmetic.add_to_ring_element v_K result product in
          ())
  in
  let _:Prims.unit = Libcrux.Kem.Kyber.Ntt.invert_ntt_montgomery v_K result in
  let _:Prims.unit =
    Rust_primitives.f_for_loop (sz 0)
      Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT
      (fun i ->
          let i:usize = i in
          let coefficient_normal_form:i32 =
            Libcrux.Kem.Kyber.Arithmetic.montgomery_reduce ((result
                    .Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ i ]
                  <:
                  i32) *!
                1441l
                <:
                i32)
          in
          let _:Prims.unit =
            Rust_primitives.Hax.Monomorphized_update_at.update_array_at_usize result
                .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
              i
              (Libcrux.Kem.Kyber.Arithmetic.barrett_reduce ((coefficient_normal_form +!
                      (error_2_.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ i ] <: i32)
                      <:
                      i32) +!
                    (message.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ i ] <: i32)
                    <:
                    i32)
                <:
                i32)
          in
          ())
  in
  result

let compute_vector_u
      (v_K: usize)
      (a_as_ntt: t_Array (t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K) v_K)
      (r_as_ntt error_1_: t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K)
    : FStar.HyperStack.ST.St (t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K) =
  let result:t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K =
    Rust_primitives.Hax.repeat Libcrux.Kem.Kyber.Arithmetic.impl__PolynomialRingElement__ZERO v_K
  in
  let _:Prims.unit =
    Rust_primitives.f_for_loop (sz 0)
      (Core.Slice.impl__len (Rust_primitives.unsize a_as_ntt
            <:
            t_Slice (t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K))
        <:
        usize)
      (fun i ->
          let i:usize = i in
          let row:t_Array Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement v_K =
            a_as_ntt.[ i ]
          in
          let _:Prims.unit =
            Rust_primitives.f_for_loop (sz 0)
              (Core.Slice.impl__len (Rust_primitives.unsize row
                    <:
                    t_Slice Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement)
                <:
                usize)
              (fun j ->
                  let j:usize = j in
                  let a_element:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement = row.[ j ] in
                  let product:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
                    Libcrux.Kem.Kyber.Ntt.ntt_multiply a_element
                      (r_as_ntt.[ j ] <: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement)
                  in
                  let _:Prims.unit =
                    Libcrux.Kem.Kyber.Arithmetic.add_to_ring_element v_K
                      (result.[ i ] <: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement)
                      product
                  in
                  ())
          in
          let _:Prims.unit =
            Libcrux.Kem.Kyber.Ntt.invert_ntt_montgomery v_K
              (result.[ i ] <: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement)
          in
          Rust_primitives.f_for_loop (sz 0)
            Libcrux.Kem.Kyber.Constants.v_COEFFICIENTS_IN_RING_ELEMENT
            (fun j ->
                let j:usize = j in
                let result_i:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement = result.[ i ] in
                let error_1_i:Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement =
                  error_1_.[ i ]
                in
                let coefficient_normal_form:i32 =
                  Libcrux.Kem.Kyber.Arithmetic.montgomery_reduce ((result_i
                          .Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ j ]
                        <:
                        i32) *!
                      1441l
                      <:
                      i32)
                in
                let _:Prims.unit =
                  Rust_primitives.Hax.Monomorphized_update_at.update_array_at_usize (result.[ i ]
                      <:
                      Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement)
                      .Libcrux.Kem.Kyber.Arithmetic.f_coefficients
                    j
                    (Libcrux.Kem.Kyber.Arithmetic.barrett_reduce (coefficient_normal_form +!
                          (error_1_i.Libcrux.Kem.Kyber.Arithmetic.f_coefficients.[ j ] <: i32)
                          <:
                          i32)
                      <:
                      i32)
                in
                ()))
  in
  result
