module Libcrux_ml_dsa.Constants.V87
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let v_BITS_PER_ERROR_COEFFICIENT: usize = sz 3

let v_COLUMNS_IN_A: usize = sz 7

let v_ETA: Libcrux_ml_dsa.Constants.t_Eta =
  Libcrux_ml_dsa.Constants.Eta_Two <: Libcrux_ml_dsa.Constants.t_Eta

let v_ROWS_IN_A: usize = sz 8