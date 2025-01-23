module Libcrux_ml_dsa.Simd.Traits
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let vv_zero (_: Prims.unit) = Rust_primitives.Hax.repeat (mk_i32 0) (mk_usize 8)
