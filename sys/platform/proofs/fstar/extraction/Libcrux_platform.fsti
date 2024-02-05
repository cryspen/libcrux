module Libcrux_platform
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

val simd128_support: Prims.unit -> Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)
