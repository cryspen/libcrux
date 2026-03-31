module Hacspec_ml_dsa.Matrix
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

/// Multiply a k×ℓ matrix (in NTT domain) by an ℓ-vector (in NTT domain).
/// Returns a k-vector where result[i] = Σ_j A_hat[i][j] ∘ v_hat[j].
let matrix_vector_ntt
      (v_K v_L: usize)
      (a_hat: t_Array (t_Array (t_Array i32 (mk_usize 256)) v_L) v_K)
      (vv_hat: t_Array (t_Array i32 (mk_usize 256)) v_L)
    : t_Array (t_Array i32 (mk_usize 256)) v_K =
  Hacspec_ml_dsa.createi #(t_Array i32 (mk_usize 256))
    v_K
    #(usize -> t_Array i32 (mk_usize 256))
    (fun i ->
        let i:usize = i in
        let acc:t_Array i32 (mk_usize 256) = Hacspec_ml_dsa.Parameters.v_ZERO_POLY in
        let acc:t_Array i32 (mk_usize 256) =
          Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
            v_L
            (fun acc temp_1_ ->
                let acc:t_Array i32 (mk_usize 256) = acc in
                let _:usize = temp_1_ in
                true)
            acc
            (fun acc j ->
                let acc:t_Array i32 (mk_usize 256) = acc in
                let j:usize = j in
                let product:t_Array i32 (mk_usize 256) =
                  Hacspec_ml_dsa.Polynomial.poly_pointwise_mul ((a_hat.[ i ]
                        <:
                        t_Array (t_Array i32 (mk_usize 256)) v_L).[ j ]
                      <:
                      t_Array i32 (mk_usize 256))
                    (vv_hat.[ j ] <: t_Array i32 (mk_usize 256))
                in
                let acc:t_Array i32 (mk_usize 256) =
                  Hacspec_ml_dsa.Polynomial.poly_add acc product
                in
                acc)
        in
        acc)
