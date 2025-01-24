module Libcrux_ml_kem.Matrix
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_kem.Hash_functions in
  let open Libcrux_ml_kem.Vector.Traits in
  ()

val sample_matrix_A
      (v_K: usize)
      (#v_Vector #v_Hasher: Type0)
      {| i2: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      {| i3: Libcrux_ml_kem.Hash_functions.t_Hash v_Hasher v_K |}
      (v_A_transpose:
          t_Array (t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K) v_K)
      (seed: t_Array u8 (sz 34))
      (transpose: bool)
    : Prims.Pure
      (t_Array (t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K) v_K)
      (requires Spec.MLKEM.is_rank v_K)
      (ensures
        fun v_A_transpose_future ->
          let v_A_transpose_future:t_Array
            (t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K) v_K =
            v_A_transpose_future
          in
          let matrix_A, valid = Spec.MLKEM.sample_matrix_A_ntt (Seq.slice seed 0 32) in
          valid ==>
          (if transpose
            then Libcrux_ml_kem.Polynomial.to_spec_matrix_t v_A_transpose_future == matrix_A
            else
              Libcrux_ml_kem.Polynomial.to_spec_matrix_t v_A_transpose_future ==
              Spec.MLKEM.matrix_transpose matrix_A))

/// The following functions compute various expressions involving
/// vectors and matrices. The computation of these expressions has been
/// abstracted away into these functions in order to save on loop iterations.
/// Compute v − InverseNTT(sᵀ ◦ NTT(u))
val compute_message
      (v_K: usize)
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (v: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (secret_as_ntt u_as_ntt:
          t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K)
    : Prims.Pure (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (requires Spec.MLKEM.is_rank v_K)
      (ensures
        fun res ->
          let res:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = res in
          let open Libcrux_ml_kem.Polynomial in
          let secret_spec = to_spec_vector_t secret_as_ntt in
          let u_spec = to_spec_vector_t u_as_ntt in
          let v_spec = to_spec_poly_t v in
          to_spec_poly_t res ==
          Spec.MLKEM.(poly_sub v_spec
              (poly_inv_ntt (vector_dot_product_ntt #v_K secret_spec u_spec))) /\
          Libcrux_ml_kem.Serialize.coefficients_field_modulus_range res)

/// Compute InverseNTT(tᵀ ◦ r\u{302}) + e₂ + message
val compute_ring_element_v
      (v_K: usize)
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (tt_as_ntt r_as_ntt: t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K)
      (error_2_ message: Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
    : Prims.Pure (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
      (requires Spec.MLKEM.is_rank v_K)
      (ensures
        fun res ->
          let res:Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector = res in
          let open Libcrux_ml_kem.Polynomial in
          let tt_spec = to_spec_vector_t tt_as_ntt in
          let r_spec = to_spec_vector_t r_as_ntt in
          let e2_spec = to_spec_poly_t error_2_ in
          let m_spec = to_spec_poly_t message in
          let res_spec = to_spec_poly_t res in
          res_spec ==
          Spec.MLKEM.(poly_add (poly_add (vector_dot_product_ntt #v_K tt_spec r_spec) e2_spec)
              m_spec) /\ Libcrux_ml_kem.Serialize.coefficients_field_modulus_range res)

/// Compute u := InvertNTT(Aᵀ ◦ r\u{302}) + e₁
val compute_vector_u
      (v_K: usize)
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (a_as_ntt:
          t_Array (t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K) v_K)
      (r_as_ntt error_1_: t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K)
    : Prims.Pure (t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K)
      (requires Spec.MLKEM.is_rank v_K)
      (ensures
        fun res ->
          let res:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K = res in
          let open Libcrux_ml_kem.Polynomial in
          let a_spec = to_spec_matrix_t a_as_ntt in
          let r_spec = to_spec_vector_t r_as_ntt in
          let e_spec = to_spec_vector_t error_1_ in
          let res_spec = to_spec_vector_t res in
          res_spec ==
          Spec.MLKEM.(vector_add (vector_inv_ntt (matrix_vector_mul_ntt a_spec r_spec)) e_spec) /\
          (forall (i: nat).
              i < v v_K ==>
              Libcrux_ml_kem.Serialize.coefficients_field_modulus_range (Seq.index res i)))

/// Compute Â ◦ ŝ + ê
val compute_As_plus_e
      (v_K: usize)
      (#v_Vector: Type0)
      {| i1: Libcrux_ml_kem.Vector.Traits.t_Operations v_Vector |}
      (tt_as_ntt: t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K)
      (matrix_A:
          t_Array (t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K) v_K)
      (s_as_ntt error_as_ntt:
          t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K)
    : Prims.Pure (t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector) v_K)
      (requires Spec.MLKEM.is_rank v_K)
      (ensures
        fun tt_as_ntt_future ->
          let tt_as_ntt_future:t_Array (Libcrux_ml_kem.Polynomial.t_PolynomialRingElement v_Vector)
            v_K =
            tt_as_ntt_future
          in
          let open Libcrux_ml_kem.Polynomial in
          to_spec_vector_t tt_as_ntt_future =
          Spec.MLKEM.compute_As_plus_e_ntt (to_spec_matrix_t matrix_A)
            (to_spec_vector_t s_as_ntt)
            (to_spec_vector_t error_as_ntt) /\
          (forall (i: nat).
              i < v v_K ==>
              Libcrux_ml_kem.Serialize.coefficients_field_modulus_range (Seq.index tt_as_ntt_future
                    i)))
