module Libcrux_sha3.Neon.X2
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let shake256 (v_LEN: usize) (input0 input1: t_Slice u8) (out: t_Array (t_Array u8 v_LEN) (sz 2)) =
  let out:t_Array (t_Array u8 v_LEN) (sz 2) =
    Libcrux_sha3.Neon.keccakx2 (sz 136)
      v_LEN
      31uy
      (let list = [input0; input1] in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
        Rust_primitives.Hax.array_of_list 2 list)
      out
  in
  out
