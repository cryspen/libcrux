module Hacspec_ml_dsa.Ml_dsa
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

#push-options "--z3rlimit 300"

/// ML-DSA.KeyGen_internal(ξ) — FIPS 204, Algorithm 6.
/// Generates a public-private key pair from a 32-byte seed ξ.
let keygen_internal
      (v_K v_L v_PK_SIZE v_SK_SIZE: usize)
      (xi: t_Array u8 (mk_usize 32))
      (params: Hacspec_ml_dsa.Parameters.t_MlDsaParams)
    : Prims.Pure (t_Array u8 v_PK_SIZE & t_Array u8 v_SK_SIZE)
      (requires
        v_K <=. mk_usize 8 && v_L <=. mk_usize 8 &&
        v_PK_SIZE =. (mk_usize 32 +! (mk_usize 320 *! v_K <: usize) <: usize) &&
        (params.Hacspec_ml_dsa.Parameters.f_eta =. mk_usize 2 ||
        params.Hacspec_ml_dsa.Parameters.f_eta =. mk_usize 4) &&
        v_SK_SIZE >=.
        ((mk_usize 128 +! ((v_L +! v_K <: usize) *! mk_usize 128 <: usize) <: usize) +!
          (v_K *! mk_usize 416 <: usize)
          <:
          usize))
      (fun _ -> Prims.l_True) =
  let seed_input:t_Array u8 (mk_usize 34) = Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 34) in
  let seed_input:t_Array u8 (mk_usize 34) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range_to seed_input
      ({ Core_models.Ops.Range.f_end = mk_usize 32 } <: Core_models.Ops.Range.t_RangeTo usize)
      (Core_models.Slice.impl__copy_from_slice #u8
          (seed_input.[ { Core_models.Ops.Range.f_end = mk_usize 32 }
              <:
              Core_models.Ops.Range.t_RangeTo usize ]
            <:
            t_Slice u8)
          (xi <: t_Slice u8)
        <:
        t_Slice u8)
  in
  let seed_input:t_Array u8 (mk_usize 34) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize seed_input
      (mk_usize 32)
      (cast (params.Hacspec_ml_dsa.Parameters.f_k <: usize) <: u8)
  in
  let seed_input:t_Array u8 (mk_usize 34) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize seed_input
      (mk_usize 33)
      (cast (params.Hacspec_ml_dsa.Parameters.f_l <: usize) <: u8)
  in
  let (expanded: t_Array u8 (mk_usize 128)):t_Array u8 (mk_usize 128) =
    Hacspec_ml_dsa.Hash_functions.h (mk_usize 128) (seed_input <: t_Slice u8)
  in
  let rho:t_Array u8 (mk_usize 32) = Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 32) in
  let rho:t_Array u8 (mk_usize 32) =
    Core_models.Slice.impl__copy_from_slice #u8
      rho
      (expanded.[ { Core_models.Ops.Range.f_end = mk_usize 32 }
          <:
          Core_models.Ops.Range.t_RangeTo usize ]
        <:
        t_Slice u8)
  in
  let rho_prime:t_Array u8 (mk_usize 64) = Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 64) in
  let rho_prime:t_Array u8 (mk_usize 64) =
    Core_models.Slice.impl__copy_from_slice #u8
      rho_prime
      (expanded.[ {
            Core_models.Ops.Range.f_start = mk_usize 32;
            Core_models.Ops.Range.f_end = mk_usize 96
          }
          <:
          Core_models.Ops.Range.t_Range usize ]
        <:
        t_Slice u8)
  in
  let key:t_Array u8 (mk_usize 32) = Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 32) in
  let key:t_Array u8 (mk_usize 32) =
    Core_models.Slice.impl__copy_from_slice #u8
      key
      (expanded.[ {
            Core_models.Ops.Range.f_start = mk_usize 96;
            Core_models.Ops.Range.f_end = mk_usize 128
          }
          <:
          Core_models.Ops.Range.t_Range usize ]
        <:
        t_Slice u8)
  in
  let (a_hat: t_Array (t_Array (t_Array i32 (mk_usize 256)) v_L) v_K):t_Array
    (t_Array (t_Array i32 (mk_usize 256)) v_L) v_K =
    Hacspec_ml_dsa.Sampling.expand_a v_K v_L rho
  in
  let s1, s2:(t_Array (t_Array i32 (mk_usize 256)) v_L & t_Array (t_Array i32 (mk_usize 256)) v_K) =
    Hacspec_ml_dsa.Sampling.expand_s v_K v_L rho_prime params.Hacspec_ml_dsa.Parameters.f_eta
  in
  let s1_hat:t_Array (t_Array i32 (mk_usize 256)) v_L =
    Hacspec_ml_dsa.Polynomial.vector_ntt v_L s1
  in
  let as1_hat:t_Array (t_Array i32 (mk_usize 256)) v_K =
    Hacspec_ml_dsa.Matrix.matrix_vector_ntt v_K v_L a_hat s1_hat
  in
  let as1:t_Array (t_Array i32 (mk_usize 256)) v_K =
    Hacspec_ml_dsa.Polynomial.vector_intt v_K as1_hat
  in
  let t:t_Array (t_Array i32 (mk_usize 256)) v_K =
    Hacspec_ml_dsa.Polynomial.vector_add v_K as1 s2
  in
  let _:Prims.unit =
    assume (forall i.
          i < Seq.length t ==>
          (forall j.
              j < 256 ==>
              Rust_primitives.Integers.v (Seq.index (Seq.index t i) j) >= 0 /\
              Rust_primitives.Integers.v (Seq.index (Seq.index t i) j) <
              Rust_primitives.Integers.v Hacspec_ml_dsa.Parameters.v_Q))
  in
  let (t1: t_Array (t_Array i32 (mk_usize 256)) v_K), (t0: t_Array (t_Array i32 (mk_usize 256)) v_K)
  =
    Hacspec_ml_dsa.Polynomial.vector_power2round v_K t
  in
  let (pk: t_Array u8 v_PK_SIZE):t_Array u8 v_PK_SIZE =
    Hacspec_ml_dsa.Encoding.pk_encode v_K v_PK_SIZE rho t1
  in
  let (tr: t_Array u8 (mk_usize 64)):t_Array u8 (mk_usize 64) =
    Hacspec_ml_dsa.Hash_functions.h (mk_usize 64) (pk <: t_Slice u8)
  in
  let (sk: t_Array u8 v_SK_SIZE):t_Array u8 v_SK_SIZE =
    Hacspec_ml_dsa.Encoding.sk_encode v_K v_L v_SK_SIZE rho key tr s1 s2 t0 params
  in
  pk, sk <: (t_Array u8 v_PK_SIZE & t_Array u8 v_SK_SIZE)

#pop-options

#push-options "--admit_smt_queries true"

/// ML-DSA.Sign_internal(sk, M', rnd) — FIPS 204, Algorithm 7.
/// Generates a signature for formatted message M' using private key sk.
/// Returns None if all rejection sampling attempts fail (probability < 2⁻¹²⁸).
let sign_internal
      (v_K v_L v_SIG_SIZE v_W1_BYTES v_CC_TILDE_LEN: usize)
      (sk m_prime: t_Slice u8)
      (rnd: t_Array u8 (mk_usize 32))
      (params: Hacspec_ml_dsa.Parameters.t_MlDsaParams)
    : Core_models.Option.t_Option (t_Array u8 v_SIG_SIZE) =
  let
  (rho: t_Array u8 (mk_usize 32)),
  (key: t_Array u8 (mk_usize 32)),
  (tr: t_Array u8 (mk_usize 64)),
  (s1: t_Array (t_Array i32 (mk_usize 256)) v_L),
  (s2: t_Array (t_Array i32 (mk_usize 256)) v_K),
  (t0: t_Array (t_Array i32 (mk_usize 256)) v_K) =
    Hacspec_ml_dsa.Encoding.sk_decode v_K v_L sk params
  in
  let s1_hat:t_Array (t_Array i32 (mk_usize 256)) v_L =
    Hacspec_ml_dsa.Polynomial.vector_ntt v_L s1
  in
  let s2_hat:t_Array (t_Array i32 (mk_usize 256)) v_K =
    Hacspec_ml_dsa.Polynomial.vector_ntt v_K s2
  in
  let t0_hat:t_Array (t_Array i32 (mk_usize 256)) v_K =
    Hacspec_ml_dsa.Polynomial.vector_ntt v_K t0
  in
  let (a_hat: t_Array (t_Array (t_Array i32 (mk_usize 256)) v_L) v_K):t_Array
    (t_Array (t_Array i32 (mk_usize 256)) v_L) v_K =
    Hacspec_ml_dsa.Sampling.expand_a v_K v_L rho
  in
  let (mu: t_Array u8 (mk_usize 64)):t_Array u8 (mk_usize 64) =
    Hacspec_ml_dsa.Hash_functions.h2 (mk_usize 64) (tr <: t_Slice u8) m_prime
  in
  let (rho_pp: t_Array u8 (mk_usize 64)):t_Array u8 (mk_usize 64) =
    Hacspec_ml_dsa.Hash_functions.h3 (mk_usize 64) key rnd mu
  in
  let (result: Core_models.Option.t_Option (t_Array u8 v_SIG_SIZE)):Core_models.Option.t_Option
  (t_Array u8 v_SIG_SIZE) =
    Core_models.Option.Option_None <: Core_models.Option.t_Option (t_Array u8 v_SIG_SIZE)
  in
  let kappa:usize = mk_usize 0 in
  let (kappa: usize), (result: Core_models.Option.t_Option (t_Array u8 v_SIG_SIZE)) =
    Rust_primitives.Hax.Folds.fold_range (mk_i32 0)
      (mk_i32 1000)
      (fun temp_0_ temp_1_ ->
          let (kappa: usize), (result: Core_models.Option.t_Option (t_Array u8 v_SIG_SIZE)) =
            temp_0_
          in
          let _:i32 = temp_1_ in
          true)
      (kappa, result <: (usize & Core_models.Option.t_Option (t_Array u8 v_SIG_SIZE)))
      (fun temp_0_ e_attempt ->
          let (kappa: usize), (result: Core_models.Option.t_Option (t_Array u8 v_SIG_SIZE)) =
            temp_0_
          in
          let e_attempt:i32 = e_attempt in
          if Core_models.Option.impl__is_none #(t_Array u8 v_SIG_SIZE) result <: bool
          then
            let (y: t_Array (t_Array i32 (mk_usize 256)) v_L):t_Array (t_Array i32 (mk_usize 256))
              v_L =
              Hacspec_ml_dsa.Sampling.expand_mask v_L
                rho_pp
                kappa
                params.Hacspec_ml_dsa.Parameters.f_gamma1
            in
            let y_hat:t_Array (t_Array i32 (mk_usize 256)) v_L =
              Hacspec_ml_dsa.Polynomial.vector_ntt v_L y
            in
            let w_hat:t_Array (t_Array i32 (mk_usize 256)) v_K =
              Hacspec_ml_dsa.Matrix.matrix_vector_ntt v_K v_L a_hat y_hat
            in
            let (w: t_Array (t_Array i32 (mk_usize 256)) v_K):t_Array (t_Array i32 (mk_usize 256))
              v_K =
              Hacspec_ml_dsa.Polynomial.vector_intt v_K w_hat
            in
            let (w1: t_Array (t_Array i32 (mk_usize 256)) v_K):t_Array (t_Array i32 (mk_usize 256))
              v_K =
              Hacspec_ml_dsa.Polynomial.vector_high_bits v_K
                w
                params.Hacspec_ml_dsa.Parameters.f_gamma2
            in
            let (w1_encoded: t_Array u8 v_W1_BYTES):t_Array u8 v_W1_BYTES =
              Hacspec_ml_dsa.Encoding.w1_encode v_K v_W1_BYTES w1 params
            in
            let hash_input:t_Array u8 (mk_usize 1088) =
              Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 1088)
            in
            let hash_input:t_Array u8 (mk_usize 1088) =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_range_to hash_input
                ({ Core_models.Ops.Range.f_end = mk_usize 64 }
                  <:
                  Core_models.Ops.Range.t_RangeTo usize)
                (Core_models.Slice.impl__copy_from_slice #u8
                    (hash_input.[ { Core_models.Ops.Range.f_end = mk_usize 64 }
                        <:
                        Core_models.Ops.Range.t_RangeTo usize ]
                      <:
                      t_Slice u8)
                    (mu <: t_Slice u8)
                  <:
                  t_Slice u8)
            in
            let hash_input:t_Array u8 (mk_usize 1088) =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_range hash_input
                ({
                    Core_models.Ops.Range.f_start = mk_usize 64;
                    Core_models.Ops.Range.f_end = mk_usize 64 +! v_W1_BYTES <: usize
                  }
                  <:
                  Core_models.Ops.Range.t_Range usize)
                (Core_models.Slice.impl__copy_from_slice #u8
                    (hash_input.[ {
                          Core_models.Ops.Range.f_start = mk_usize 64;
                          Core_models.Ops.Range.f_end = mk_usize 64 +! v_W1_BYTES <: usize
                        }
                        <:
                        Core_models.Ops.Range.t_Range usize ]
                      <:
                      t_Slice u8)
                    (w1_encoded <: t_Slice u8)
                  <:
                  t_Slice u8)
            in
            let (c_tilde_full: t_Array u8 (mk_usize 64)):t_Array u8 (mk_usize 64) =
              Hacspec_ml_dsa.Hash_functions.h (mk_usize 64)
                (hash_input.[ { Core_models.Ops.Range.f_end = mk_usize 64 +! v_W1_BYTES <: usize }
                    <:
                    Core_models.Ops.Range.t_RangeTo usize ]
                  <:
                  t_Slice u8)
            in
            let c_tilde:t_Array u8 v_CC_TILDE_LEN =
              Rust_primitives.Hax.repeat (mk_u8 0) v_CC_TILDE_LEN
            in
            let c_tilde:t_Array u8 v_CC_TILDE_LEN =
              Core_models.Slice.impl__copy_from_slice #u8
                c_tilde
                (c_tilde_full.[ { Core_models.Ops.Range.f_end = v_CC_TILDE_LEN }
                    <:
                    Core_models.Ops.Range.t_RangeTo usize ]
                  <:
                  t_Slice u8)
            in
            let c:t_Array i32 (mk_usize 256) =
              Hacspec_ml_dsa.Sampling.sample_in_ball (c_tilde <: t_Slice u8)
                params.Hacspec_ml_dsa.Parameters.f_tau
            in
            let c_hat:t_Array i32 (mk_usize 256) = Hacspec_ml_dsa.Ntt.ntt c in
            let (cs1_hat: t_Array (t_Array i32 (mk_usize 256)) v_L):t_Array
              (t_Array i32 (mk_usize 256)) v_L =
              Hacspec_ml_dsa.Polynomial.scalar_vector_ntt v_L c_hat s1_hat
            in
            let (cs1: t_Array (t_Array i32 (mk_usize 256)) v_L):t_Array (t_Array i32 (mk_usize 256))
              v_L =
              Hacspec_ml_dsa.Polynomial.vector_intt v_L cs1_hat
            in
            let (cs2_hat: t_Array (t_Array i32 (mk_usize 256)) v_K):t_Array
              (t_Array i32 (mk_usize 256)) v_K =
              Hacspec_ml_dsa.Polynomial.scalar_vector_ntt v_K c_hat s2_hat
            in
            let (cs2: t_Array (t_Array i32 (mk_usize 256)) v_K):t_Array (t_Array i32 (mk_usize 256))
              v_K =
              Hacspec_ml_dsa.Polynomial.vector_intt v_K cs2_hat
            in
            let (z: t_Array (t_Array i32 (mk_usize 256)) v_L):t_Array (t_Array i32 (mk_usize 256))
              v_L =
              Hacspec_ml_dsa.Polynomial.vector_add v_L y cs1
            in
            let (w_minus_cs2: t_Array (t_Array i32 (mk_usize 256)) v_K):t_Array
              (t_Array i32 (mk_usize 256)) v_K =
              Hacspec_ml_dsa.Polynomial.vector_sub v_K w cs2
            in
            let (r0: t_Array (t_Array i32 (mk_usize 256)) v_K):t_Array (t_Array i32 (mk_usize 256))
              v_K =
              Hacspec_ml_dsa.Polynomial.vector_low_bits v_K
                w_minus_cs2
                params.Hacspec_ml_dsa.Parameters.f_gamma2
            in
            if
              (Hacspec_ml_dsa.Polynomial.vector_infinity_norm v_L z <: i32) >=.
              (params.Hacspec_ml_dsa.Parameters.f_gamma1 -! params.Hacspec_ml_dsa.Parameters.f_beta
                <:
                i32) ||
              (Hacspec_ml_dsa.Polynomial.vector_infinity_norm v_K r0 <: i32) >=.
              (params.Hacspec_ml_dsa.Parameters.f_gamma2 -! params.Hacspec_ml_dsa.Parameters.f_beta
                <:
                i32)
            then
              let kappa:usize = kappa +! params.Hacspec_ml_dsa.Parameters.f_l in
              kappa, result <: (usize & Core_models.Option.t_Option (t_Array u8 v_SIG_SIZE))
            else
              let (ct0_hat: t_Array (t_Array i32 (mk_usize 256)) v_K):t_Array
                (t_Array i32 (mk_usize 256)) v_K =
                Hacspec_ml_dsa.Polynomial.scalar_vector_ntt v_K c_hat t0_hat
              in
              let (ct0: t_Array (t_Array i32 (mk_usize 256)) v_K):t_Array
                (t_Array i32 (mk_usize 256)) v_K =
                Hacspec_ml_dsa.Polynomial.vector_intt v_K ct0_hat
              in
              let (neg_ct0: t_Array (t_Array i32 (mk_usize 256)) v_K):t_Array
                (t_Array i32 (mk_usize 256)) v_K =
                Hacspec_ml_dsa.createi #(t_Array i32 (mk_usize 256))
                  v_K
                  #(usize -> t_Array i32 (mk_usize 256))
                  (fun i ->
                      let i:usize = i in
                      let p:t_Array i32 (mk_usize 256) = Hacspec_ml_dsa.Parameters.v_ZERO_POLY in
                      let p:t_Array i32 (mk_usize 256) =
                        Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
                          (mk_usize 256)
                          (fun p temp_1_ ->
                              let p:t_Array i32 (mk_usize 256) = p in
                              let _:usize = temp_1_ in
                              true)
                          p
                          (fun p j ->
                              let p:t_Array i32 (mk_usize 256) = p in
                              let j:usize = j in
                              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize p
                                j
                                (if
                                    ((ct0.[ i ] <: t_Array i32 (mk_usize 256)).[ j ] <: i32) =.
                                    mk_i32 0
                                    <:
                                    bool
                                  then mk_i32 0
                                  else
                                    Hacspec_ml_dsa.Parameters.v_Q -!
                                    ((ct0.[ i ] <: t_Array i32 (mk_usize 256)).[ j ] <: i32)
                                    <:
                                    i32)
                              <:
                              t_Array i32 (mk_usize 256))
                      in
                      p)
              in
              let (w_cs2_ct0: t_Array (t_Array i32 (mk_usize 256)) v_K):t_Array
                (t_Array i32 (mk_usize 256)) v_K =
                Hacspec_ml_dsa.Polynomial.vector_add v_K w_minus_cs2 ct0
              in
              let (hint: t_Array (t_Array bool (mk_usize 256)) v_K), (hint_count: usize) =
                Hacspec_ml_dsa.Polynomial.vector_make_hint v_K
                  neg_ct0
                  w_cs2_ct0
                  params.Hacspec_ml_dsa.Parameters.f_gamma2
              in
              if
                (Hacspec_ml_dsa.Polynomial.vector_infinity_norm v_K ct0 <: i32) >=.
                params.Hacspec_ml_dsa.Parameters.f_gamma2 ||
                hint_count >. params.Hacspec_ml_dsa.Parameters.f_omega
              then
                let kappa:usize = kappa +! params.Hacspec_ml_dsa.Parameters.f_l in
                kappa, result <: (usize & Core_models.Option.t_Option (t_Array u8 v_SIG_SIZE))
              else
                let (z_centered: t_Array (t_Array i32 (mk_usize 256)) v_L):t_Array
                  (t_Array i32 (mk_usize 256)) v_L =
                  Hacspec_ml_dsa.createi #(t_Array i32 (mk_usize 256))
                    v_L
                    #(usize -> t_Array i32 (mk_usize 256))
                    (fun i ->
                        let i:usize = i in
                        Hacspec_ml_dsa.Polynomial.poly_mod_pm (z.[ i ] <: t_Array i32 (mk_usize 256)
                          )
                        <:
                        t_Array i32 (mk_usize 256))
                in
                let result:Core_models.Option.t_Option (t_Array u8 v_SIG_SIZE) =
                  Core_models.Option.Option_Some
                  (Hacspec_ml_dsa.Encoding.sig_encode v_K
                      v_L
                      v_SIG_SIZE
                      (c_tilde <: t_Slice u8)
                      z_centered
                      hint
                      params)
                  <:
                  Core_models.Option.t_Option (t_Array u8 v_SIG_SIZE)
                in
                kappa, result <: (usize & Core_models.Option.t_Option (t_Array u8 v_SIG_SIZE))
          else kappa, result <: (usize & Core_models.Option.t_Option (t_Array u8 v_SIG_SIZE)))
  in
  result

#pop-options

#push-options "--z3rlimit 300"

/// ML-DSA.Verify_internal(pk, M\', σ) — FIPS 204, Algorithm 8.
/// Verifies signature σ for formatted message M\' using public key pk.
let verify_internal
      (v_K v_L v_CC_TILDE_LEN v_W1_BYTES: usize)
      (pk m_prime sigma: t_Slice u8)
      (params: Hacspec_ml_dsa.Parameters.t_MlDsaParams)
    : Prims.Pure bool
      (requires
        v_K <=. mk_usize 8 && v_L <=. mk_usize 8 && v_CC_TILDE_LEN <=. mk_usize 64 &&
        v_W1_BYTES >=. (v_K *! mk_usize 192 <: usize) &&
        v_W1_BYTES <=. mk_usize 1024 &&
        params.Hacspec_ml_dsa.Parameters.f_tau <=. mk_usize 256 &&
        params.Hacspec_ml_dsa.Parameters.f_omega <=. mk_usize 256 &&
        params.Hacspec_ml_dsa.Parameters.f_beta >=. mk_i32 0 &&
        params.Hacspec_ml_dsa.Parameters.f_gamma1 >. params.Hacspec_ml_dsa.Parameters.f_beta &&
        params.Hacspec_ml_dsa.Parameters.f_gamma2 >. params.Hacspec_ml_dsa.Parameters.f_beta &&
        (params.Hacspec_ml_dsa.Parameters.f_gamma1 =. (mk_i32 1 <<! mk_i32 17 <: i32) ||
        params.Hacspec_ml_dsa.Parameters.f_gamma1 =. (mk_i32 1 <<! mk_i32 19 <: i32)) &&
        (params.Hacspec_ml_dsa.Parameters.f_gamma2 =.
        ((Hacspec_ml_dsa.Parameters.v_Q -! mk_i32 1 <: i32) /! mk_i32 88 <: i32) ||
        params.Hacspec_ml_dsa.Parameters.f_gamma2 =.
        ((Hacspec_ml_dsa.Parameters.v_Q -! mk_i32 1 <: i32) /! mk_i32 32 <: i32)) &&
        (Core_models.Slice.impl__len #u8 pk <: usize) >=.
        (mk_usize 32 +! (mk_usize 320 *! v_K <: usize) <: usize) &&
        (Core_models.Slice.impl__len #u8 sigma <: usize) >=.
        (((v_CC_TILDE_LEN +! (v_L *! mk_usize 640 <: usize) <: usize) +!
            params.Hacspec_ml_dsa.Parameters.f_omega
            <:
            usize) +!
          v_K
          <:
          usize))
      (fun _ -> Prims.l_True) =
  let rho, t1:(t_Array u8 (mk_usize 32) & t_Array (t_Array i32 (mk_usize 256)) v_K) =
    Hacspec_ml_dsa.Encoding.pk_decode v_K pk
  in
  match
    Hacspec_ml_dsa.Encoding.sig_decode v_K v_L v_CC_TILDE_LEN sigma params
    <:
    Core_models.Option.t_Option
    (t_Array u8 v_CC_TILDE_LEN & t_Array (t_Array i32 (mk_usize 256)) v_L &
      t_Array (t_Array bool (mk_usize 256)) v_K)
  with
  | Core_models.Option.Option_None  -> false
  | Core_models.Option.Option_Some (c_tilde, z, h_arr) ->
    if
      (Hacspec_ml_dsa.Polynomial.vector_infinity_norm v_L z <: i32) >=.
      (params.Hacspec_ml_dsa.Parameters.f_gamma1 -! params.Hacspec_ml_dsa.Parameters.f_beta <: i32)
    then false
    else
      let (a_hat: t_Array (t_Array (t_Array i32 (mk_usize 256)) v_L) v_K):t_Array
        (t_Array (t_Array i32 (mk_usize 256)) v_L) v_K =
        Hacspec_ml_dsa.Sampling.expand_a v_K v_L rho
      in
      let (tr: t_Array u8 (mk_usize 64)):t_Array u8 (mk_usize 64) =
        Hacspec_ml_dsa.Hash_functions.h (mk_usize 64) pk
      in
      let (mu: t_Array u8 (mk_usize 64)):t_Array u8 (mk_usize 64) =
        Hacspec_ml_dsa.Hash_functions.h2 (mk_usize 64) (tr <: t_Slice u8) m_prime
      in
      let c:t_Array i32 (mk_usize 256) =
        Hacspec_ml_dsa.Sampling.sample_in_ball (c_tilde <: t_Slice u8)
          params.Hacspec_ml_dsa.Parameters.f_tau
      in
      let z_hat:t_Array (t_Array i32 (mk_usize 256)) v_L =
        Hacspec_ml_dsa.Polynomial.vector_ntt v_L z
      in
      let az_hat:t_Array (t_Array i32 (mk_usize 256)) v_K =
        Hacspec_ml_dsa.Matrix.matrix_vector_ntt v_K v_L a_hat z_hat
      in
      let c_hat:t_Array i32 (mk_usize 256) = Hacspec_ml_dsa.Ntt.ntt c in
      let two_d:i32 = mk_i32 1 <<! Hacspec_ml_dsa.Parameters.v_D in
      let (t1_scaled: t_Array (t_Array i32 (mk_usize 256)) v_K):t_Array (t_Array i32 (mk_usize 256))
        v_K =
        Hacspec_ml_dsa.createi #(t_Array i32 (mk_usize 256))
          v_K
          #(usize -> t_Array i32 (mk_usize 256))
          (fun i ->
              let i:usize = i in
              Hacspec_ml_dsa.createi #i32
                (mk_usize 256)
                #(usize -> i32)
                (fun j ->
                    let j:usize = j in
                    Hacspec_ml_dsa.Arithmetic.mod_q ((cast ((t1.[ i ] <: t_Array i32 (mk_usize 256)).[
                                j ]
                              <:
                              i32)
                          <:
                          i64) *!
                        (cast (two_d <: i32) <: i64)
                        <:
                        i64)
                    <:
                    i32)
              <:
              t_Array i32 (mk_usize 256))
      in
      let t1_2d_hat:t_Array (t_Array i32 (mk_usize 256)) v_K =
        Hacspec_ml_dsa.Polynomial.vector_ntt v_K t1_scaled
      in
      let (ct1_hat: t_Array (t_Array i32 (mk_usize 256)) v_K):t_Array (t_Array i32 (mk_usize 256))
        v_K =
        Hacspec_ml_dsa.createi #(t_Array i32 (mk_usize 256))
          v_K
          #(usize -> t_Array i32 (mk_usize 256))
          (fun i ->
              let i:usize = i in
              Hacspec_ml_dsa.Polynomial.poly_pointwise_mul c_hat
                (t1_2d_hat.[ i ] <: t_Array i32 (mk_usize 256))
              <:
              t_Array i32 (mk_usize 256))
      in
      let (w_approx_hat: t_Array (t_Array i32 (mk_usize 256)) v_K):t_Array
        (t_Array i32 (mk_usize 256)) v_K =
        Hacspec_ml_dsa.createi #(t_Array i32 (mk_usize 256))
          v_K
          #(usize -> t_Array i32 (mk_usize 256))
          (fun i ->
              let i:usize = i in
              Hacspec_ml_dsa.Polynomial.poly_sub (az_hat.[ i ] <: t_Array i32 (mk_usize 256))
                (ct1_hat.[ i ] <: t_Array i32 (mk_usize 256))
              <:
              t_Array i32 (mk_usize 256))
      in
      let (w_approx: t_Array (t_Array i32 (mk_usize 256)) v_K):t_Array (t_Array i32 (mk_usize 256))
        v_K =
        Hacspec_ml_dsa.Polynomial.vector_intt v_K w_approx_hat
      in
      let _:Prims.unit =
        assume (forall i.
              i < Seq.length w_approx ==>
              (forall j.
                  j < 256 ==>
                  Rust_primitives.Integers.v (Seq.index (Seq.index w_approx i) j) >= 0 /\
                  Rust_primitives.Integers.v (Seq.index (Seq.index w_approx i) j) <
                  Rust_primitives.Integers.v Hacspec_ml_dsa.Parameters.v_Q))
      in
      let (w1_prime: t_Array (t_Array i32 (mk_usize 256)) v_K):t_Array (t_Array i32 (mk_usize 256))
        v_K =
        Hacspec_ml_dsa.Polynomial.vector_use_hint v_K
          h_arr
          w_approx
          params.Hacspec_ml_dsa.Parameters.f_gamma2
      in
      let (w1_encoded: t_Array u8 v_W1_BYTES):t_Array u8 v_W1_BYTES =
        Hacspec_ml_dsa.Encoding.w1_encode v_K v_W1_BYTES w1_prime params
      in
      let hash_input:t_Array u8 (mk_usize 1088) =
        Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 1088)
      in
      let hash_input:t_Array u8 (mk_usize 1088) =
        Rust_primitives.Hax.Monomorphized_update_at.update_at_range_to hash_input
          ({ Core_models.Ops.Range.f_end = mk_usize 64 } <: Core_models.Ops.Range.t_RangeTo usize)
          (Core_models.Slice.impl__copy_from_slice #u8
              (hash_input.[ { Core_models.Ops.Range.f_end = mk_usize 64 }
                  <:
                  Core_models.Ops.Range.t_RangeTo usize ]
                <:
                t_Slice u8)
              (mu <: t_Slice u8)
            <:
            t_Slice u8)
      in
      let hash_input:t_Array u8 (mk_usize 1088) =
        Rust_primitives.Hax.Monomorphized_update_at.update_at_range hash_input
          ({
              Core_models.Ops.Range.f_start = mk_usize 64;
              Core_models.Ops.Range.f_end = mk_usize 64 +! v_W1_BYTES <: usize
            }
            <:
            Core_models.Ops.Range.t_Range usize)
          (Core_models.Slice.impl__copy_from_slice #u8
              (hash_input.[ {
                    Core_models.Ops.Range.f_start = mk_usize 64;
                    Core_models.Ops.Range.f_end = mk_usize 64 +! v_W1_BYTES <: usize
                  }
                  <:
                  Core_models.Ops.Range.t_Range usize ]
                <:
                t_Slice u8)
              (w1_encoded <: t_Slice u8)
            <:
            t_Slice u8)
      in
      let (c_tilde_prime_full: t_Array u8 (mk_usize 64)):t_Array u8 (mk_usize 64) =
        Hacspec_ml_dsa.Hash_functions.h (mk_usize 64)
          (hash_input.[ { Core_models.Ops.Range.f_end = mk_usize 64 +! v_W1_BYTES <: usize }
              <:
              Core_models.Ops.Range.t_RangeTo usize ]
            <:
            t_Slice u8)
      in
      let c_tilde_prime:t_Array u8 v_CC_TILDE_LEN =
        Rust_primitives.Hax.repeat (mk_u8 0) v_CC_TILDE_LEN
      in
      let c_tilde_prime:t_Array u8 v_CC_TILDE_LEN =
        Core_models.Slice.impl__copy_from_slice #u8
          c_tilde_prime
          (c_tilde_prime_full.[ { Core_models.Ops.Range.f_end = v_CC_TILDE_LEN }
              <:
              Core_models.Ops.Range.t_RangeTo usize ]
            <:
            t_Slice u8)
      in
      let hint_count:usize = Hacspec_ml_dsa.Polynomial.count_hints v_K h_arr in
      if hint_count >. params.Hacspec_ml_dsa.Parameters.f_omega
      then false
      else c_tilde =. c_tilde_prime

#pop-options
