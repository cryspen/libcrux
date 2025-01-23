module Libcrux_ml_dsa.Constants.Ml_dsa_87_
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let v_ROWS_IN_A: usize = sz 8

let v_COLUMNS_IN_A: usize = sz 7

let v_ETA: Libcrux_ml_dsa.Constants.t_Eta =
  Libcrux_ml_dsa.Constants.Eta_Two <: Libcrux_ml_dsa.Constants.t_Eta

let v_BITS_PER_ERROR_COEFFICIENT: usize = sz 3

let v_GAMMA1_EXPONENT: usize = sz 19

let v_BITS_PER_GAMMA1_COEFFICIENT: usize = sz 20

let v_MAX_ONES_IN_HINT: usize = sz 75

let v_ONES_IN_VERIFIER_CHALLENGE: usize = sz 60

let v_GAMMA2: i32 = (Libcrux_ml_dsa.Constants.v_FIELD_MODULUS -! 1l <: i32) /! 32l

let v_BITS_PER_COMMITMENT_COEFFICIENT: usize = sz 4

let v_COMMITMENT_HASH_SIZE: usize = sz 64
