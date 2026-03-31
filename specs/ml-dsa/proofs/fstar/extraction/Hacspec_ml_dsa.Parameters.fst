module Hacspec_ml_dsa.Parameters
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

/// ML-DSA parameters — FIPS 204, Section 4.
/// Field modulus q = 2^23 - 2^13 + 1.
let v_Q: i32 = mk_i32 8380417

/// Number of dropped bits from t — FIPS 204, Table 1.
let v_D: usize = mk_usize 13

/// Primitive 512th root of unity in Z_q.
let v_ZETA: i32 = mk_i32 1753

/// Coefficients per polynomial.
let v_N: usize = mk_usize 256

/// A zero polynomial.
let v_ZERO_POLY: t_Array i32 (mk_usize 256) = Rust_primitives.Hax.repeat (mk_i32 0) (mk_usize 256)

/// ML-DSA parameter set — FIPS 204, Table 1.
type t_MlDsaParams = {
  f_k:usize;
  f_l:usize;
  f_tau:usize;
  f_lambda:usize;
  f_gamma1:i32;
  f_gamma2:i32;
  f_eta:usize;
  f_omega:usize;
  f_beta:i32
}

/// Public key size in bytes: 32 + 32·k·(bitlen(q-1) - d).
let pk_size (params: t_MlDsaParams)
    : Prims.Pure usize (requires params.f_k <=. mk_usize 16) (fun _ -> Prims.l_True) =
  mk_usize 32 +! ((mk_usize 32 *! params.f_k <: usize) *! mk_usize 10 <: usize)

/// Private key size in bytes.
let sk_size (params: t_MlDsaParams)
    : Prims.Pure usize
      (requires
        params.f_k <=. mk_usize 16 && params.f_l <=. mk_usize 16 && params.f_eta <=. mk_usize 8)
      (fun _ -> Prims.l_True) =
  let eta_bits:usize = if params.f_eta =. mk_usize 2 then mk_usize 3 else mk_usize 4 in
  (((mk_usize 32 +! mk_usize 32 <: usize) +! mk_usize 64 <: usize) +!
    ((mk_usize 32 *! (params.f_l +! params.f_k <: usize) <: usize) *! eta_bits <: usize)
    <:
    usize) +!
  ((mk_usize 32 *! params.f_k <: usize) *! v_D <: usize)

/// Signature size in bytes.
let sig_size (params: t_MlDsaParams)
    : Prims.Pure usize
      (requires
        params.f_k <=. mk_usize 16 && params.f_l <=. mk_usize 16 &&
        params.f_lambda <=. mk_usize 1024 &&
        params.f_omega <=. mk_usize 256)
      (fun _ -> Prims.l_True) =
  let gamma1_bits:usize =
    if params.f_gamma1 =. (mk_i32 1 <<! mk_i32 17 <: i32) then mk_usize 18 else mk_usize 20
  in
  (((params.f_lambda /! mk_usize 4 <: usize) +!
      ((mk_usize 32 *! params.f_l <: usize) *! gamma1_bits <: usize)
      <:
      usize) +!
    params.f_omega
    <:
    usize) +!
  params.f_k

/// ML-DSA-44 — FIPS 204, Table 1.
let v_ML_DSA_44_: t_MlDsaParams =
  {
    f_k = mk_usize 4;
    f_l = mk_usize 4;
    f_tau = mk_usize 39;
    f_lambda = mk_usize 128;
    f_gamma1 = mk_i32 1 <<! mk_i32 17;
    f_gamma2 = (v_Q -! mk_i32 1 <: i32) /! mk_i32 88;
    f_eta = mk_usize 2;
    f_omega = mk_usize 80;
    f_beta = mk_i32 39 *! mk_i32 2
  }
  <:
  t_MlDsaParams

/// ML-DSA-65 — FIPS 204, Table 1.
let v_ML_DSA_65_: t_MlDsaParams =
  {
    f_k = mk_usize 6;
    f_l = mk_usize 5;
    f_tau = mk_usize 49;
    f_lambda = mk_usize 192;
    f_gamma1 = mk_i32 1 <<! mk_i32 19;
    f_gamma2 = (v_Q -! mk_i32 1 <: i32) /! mk_i32 32;
    f_eta = mk_usize 4;
    f_omega = mk_usize 55;
    f_beta = mk_i32 49 *! mk_i32 4
  }
  <:
  t_MlDsaParams

/// ML-DSA-87 — FIPS 204, Table 1.
let v_ML_DSA_87_: t_MlDsaParams =
  {
    f_k = mk_usize 8;
    f_l = mk_usize 7;
    f_tau = mk_usize 60;
    f_lambda = mk_usize 256;
    f_gamma1 = mk_i32 1 <<! mk_i32 19;
    f_gamma2 = (v_Q -! mk_i32 1 <: i32) /! mk_i32 32;
    f_eta = mk_usize 2;
    f_omega = mk_usize 75;
    f_beta = mk_i32 60 *! mk_i32 2
  }
  <:
  t_MlDsaParams

let v_ML_DSA_44_PK_SIZE: usize = mk_usize 1312

let v_ML_DSA_44_SK_SIZE: usize = mk_usize 2560

let v_ML_DSA_44_SIG_SIZE: usize = mk_usize 2420

let v_ML_DSA_65_PK_SIZE: usize = mk_usize 1952

let v_ML_DSA_65_SK_SIZE: usize = mk_usize 4032

let v_ML_DSA_65_SIG_SIZE: usize = mk_usize 3309

let v_ML_DSA_87_PK_SIZE: usize = mk_usize 2592

let v_ML_DSA_87_SK_SIZE: usize = mk_usize 4896

let v_ML_DSA_87_SIG_SIZE: usize = mk_usize 4627

let v_ML_DSA_44_W1_SIZE: usize = mk_usize 768

let v_ML_DSA_65_W1_SIZE: usize = mk_usize 768

let v_ML_DSA_87_W1_SIZE: usize = mk_usize 1024

let v_ML_DSA_44_C_TILDE_LEN: usize = mk_usize 32

let v_ML_DSA_65_C_TILDE_LEN: usize = mk_usize 48

let v_ML_DSA_87_C_TILDE_LEN: usize = mk_usize 64

#push-options "--z3rlimit 150"

/// bitlen(n): number of bits needed to represent n.
let bitlen (n: usize)
    : Prims.Pure usize
      Prims.l_True
      (ensures
        fun result ->
          let result:usize = result in
          result <=. mk_usize 64) =
  let bits:usize = mk_usize 0 in
  let v:usize = n in
  let (bits: usize), (v: usize) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      (mk_usize 64)
      (fun temp_0_ e_i ->
          let (bits: usize), (v: usize) = temp_0_ in
          let e_i:usize = e_i in
          bits <=. e_i <: bool)
      (bits, v <: (usize & usize))
      (fun temp_0_ e_i ->
          let (bits: usize), (v: usize) = temp_0_ in
          let e_i:usize = e_i in
          if v >. mk_usize 0 <: bool
          then
            let bits:usize = bits +! mk_usize 1 in
            let v:usize = v >>! mk_i32 1 in
            bits, v <: (usize & usize)
          else bits, v <: (usize & usize))
  in
  bits

#pop-options
