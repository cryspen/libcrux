module Libcrux_ml_dsa.Constants.V65
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let v_BITS_PER_ERROR_COEFFICIENT: usize = sz 4

let v_COLUMNS_IN_A: usize = sz 5

let v_ETA: Libcrux_ml_dsa.Constants.t_Eta =
  Libcrux_ml_dsa.Constants.Eta_Four <: Libcrux_ml_dsa.Constants.t_Eta

let v_ROWS_IN_A: usize = sz 6
