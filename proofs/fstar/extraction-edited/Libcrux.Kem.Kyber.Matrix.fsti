module Libcrux.Kem.Kyber.Matrix
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul


val compute_As_plus_e (#p:Spec.Kyber.params)
      (v_K: usize)
      (matrix_A: t_Array (t_Array Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement v_K) v_K)
      (s_as_ntt error_as_ntt: t_Array Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement v_K)
    : Pure (t_Array Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement v_K) 
           (requires (v_K == p.v_RANK))
           (ensures fun res ->
             let open Libcrux.Kem.Kyber.Arithmetic in
             v_K == p.v_RANK /\
             to_spec_vector_b #p res =
             Spec.Kyber.compute_As_plus_e #p
               (to_spec_matrix_b #p matrix_A) 
               (to_spec_vector_b #p s_as_ntt) 
               (to_spec_vector_b #p error_as_ntt))


val compute_message (#p:Spec.Kyber.params)
      (v_K: usize)
      (poly_v: Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement)
      (secret_as_ntt u_as_ntt: t_Array Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement v_K)
    : Pure (Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement)
      (requires (v_K == p.v_RANK))
      (ensures (fun res -> 
        let secret_spec = Libcrux.Kem.Kyber.Arithmetic.to_spec_vector_b #p secret_as_ntt in
        let u_spec = Libcrux.Kem.Kyber.Arithmetic.to_spec_vector_b #p u_as_ntt in
        let v_spec = Libcrux.Kem.Kyber.Arithmetic.to_spec_poly_b poly_v in
        Libcrux.Kem.Kyber.Arithmetic.to_spec_poly_b res ==
        Spec.Kyber.(poly_sub v_spec (poly_inv_ntt #p (vector_dot_product secret_spec u_spec)))))

// TODO: error_2_ changed from `t_PolynomialRingElement_b 3` to `t_PolynomialRingElement_b 7`
val compute_ring_element_v (#p:Spec.Kyber.params)
      (v_K: usize)
      (tt_as_ntt r_as_ntt: t_Array Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement v_K)
      (error_2_: Libcrux.Kem.Kyber.Arithmetic.t_PolynomialRingElement_b 7)
      (message: Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement)
    : Pure (Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement)
      (requires (v_K == p.v_RANK))
      (ensures fun res ->
        let tt_spec = Libcrux.Kem.Kyber.Arithmetic.to_spec_vector_b #p tt_as_ntt in
        let r_spec = Libcrux.Kem.Kyber.Arithmetic.to_spec_vector_b #p r_as_ntt in
        let e2_spec = Libcrux.Kem.Kyber.Arithmetic.to_spec_poly_b error_2_ in
        let m_spec = Libcrux.Kem.Kyber.Arithmetic.to_spec_poly_b message in
        let res_spec = Libcrux.Kem.Kyber.Arithmetic.to_spec_poly_b res in
        res_spec == Spec.Kyber.(poly_add (poly_add (vector_dot_product tt_spec r_spec) e2_spec) m_spec))

val compute_vector_u (#p:Spec.Kyber.params)
      (v_K: usize)
      (a_as_ntt: t_Array (t_Array Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement v_K) v_K)
      (r_as_ntt error_1_: t_Array Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement v_K)
    : Pure (t_Array Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement v_K)
      (requires (v_K == p.v_RANK))
      (ensures fun res ->
        let a_spec = Libcrux.Kem.Kyber.Arithmetic.to_spec_matrix_b #p a_as_ntt in
        let r_spec = Libcrux.Kem.Kyber.Arithmetic.to_spec_vector_b #p r_as_ntt in
        let e_spec = Libcrux.Kem.Kyber.Arithmetic.to_spec_vector_b #p error_1_ in
        let res_spec = Libcrux.Kem.Kyber.Arithmetic.to_spec_vector_b #p res in
        res_spec == Spec.Kyber.(vector_add (vector_inv_ntt (matrix_vector_mul a_spec r_spec)) e_spec))



val sample_matrix_A (#p:Spec.Kyber.params) (v_K: usize) (seed: t_Array u8 (sz 34)) (transpose: bool)
    : Pure (t_Array (t_Array Libcrux.Kem.Kyber.Arithmetic.wfPolynomialRingElement v_K) v_K)
      (requires (v_K == p.v_RANK))
      (ensures fun res ->
        let matrix_A = Spec.Kyber.sample_matrix_A #p (Seq.slice seed 0 32) in
        if transpose then Libcrux.Kem.Kyber.Arithmetic.to_spec_matrix_b #p res == matrix_A
        else Libcrux.Kem.Kyber.Arithmetic.to_spec_matrix_b #p res == Spec.Kyber.matrix_transpose matrix_A)
