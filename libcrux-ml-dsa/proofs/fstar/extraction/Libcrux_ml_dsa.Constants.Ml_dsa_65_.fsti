module Libcrux_ml_dsa.Constants.Ml_dsa_65_
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let v_ROWS_IN_A: usize = mk_usize 6

let v_COLUMNS_IN_A: usize = mk_usize 5

let v_ETA: Libcrux_ml_dsa.Constants.t_Eta =
  Libcrux_ml_dsa.Constants.Eta_Four <: Libcrux_ml_dsa.Constants.t_Eta

let v_BITS_PER_ERROR_COEFFICIENT: usize = mk_usize 4

let v_GAMMA1_EXPONENT: usize = mk_usize 19

let v_GAMMA2: i32 = (Libcrux_ml_dsa.Constants.v_FIELD_MODULUS -! mk_i32 1 <: i32) /! mk_i32 32

let v_BITS_PER_GAMMA1_COEFFICIENT: usize = mk_usize 20

let v_MAX_ONES_IN_HINT: usize = mk_usize 55

let v_ONES_IN_VERIFIER_CHALLENGE: usize = mk_usize 49

let v_COMMITMENT_HASH_SIZE: usize = mk_usize 48

let v_BITS_PER_COMMITMENT_COEFFICIENT: usize = mk_usize 4
