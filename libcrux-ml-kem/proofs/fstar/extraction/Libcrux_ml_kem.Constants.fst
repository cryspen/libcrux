module Libcrux_ml_kem.Constants
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

let ranked_bytes_per_ring_element (rank: usize) =
  (rank *! v_BITS_PER_RING_ELEMENT <: usize) /! mk_usize 8
