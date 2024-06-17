module Libcrux_ml_kem.Vector.Rej_sample_table
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let v_REJECTION_SAMPLE_SHUFFLE_TABLE: t_Array (t_Array u8 (sz 16)) (sz 256) =
  Rust_primitives.Hax.dropped_body
