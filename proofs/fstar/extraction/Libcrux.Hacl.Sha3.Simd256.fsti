module Libcrux.Hacl.Sha3.Simd256
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Rust_primitives
open Core

val shake128 (v_LEN: usize) (payload0: t_Slice u8) (payload1: t_Slice u8) (payload2: t_Slice u8) (payload3: t_Slice u8): ((t_Array u8 v_LEN) & (t_Array u8 v_LEN) & (t_Array u8 v_LEN) & (t_Array u8 v_LEN))
