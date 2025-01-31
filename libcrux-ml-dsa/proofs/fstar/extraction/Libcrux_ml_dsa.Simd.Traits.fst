module Libcrux_ml_dsa.Simd.Traits
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open Core
open FStar.Mul

let int_in_i32_range (i: Hax_lib.Int.t_Int) =
  i <= (Rust_primitives.Hax.Int.from_machine Core.Num.impl_i32__MAX <: Hax_lib.Int.t_Int) &&
  i >= (Rust_primitives.Hax.Int.from_machine Core.Num.impl_i32__MIN <: Hax_lib.Int.t_Int)
