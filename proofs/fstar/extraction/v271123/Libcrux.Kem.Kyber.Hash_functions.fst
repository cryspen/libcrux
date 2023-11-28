module Libcrux.Kem.Kyber.Hash_functions
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let v_G (input: t_Slice u8) : FStar.HyperStack.ST.St (t_Array u8 (sz 64)) =
  Libcrux.Digest.sha3_512_ input

let v_H (input: t_Slice u8) : FStar.HyperStack.ST.St (t_Array u8 (sz 32)) =
  Libcrux.Digest.sha3_256_ input

let v_PRF (v_LEN: usize) (input: t_Slice u8) : FStar.HyperStack.ST.St (t_Array u8 v_LEN) =
  Libcrux.Digest.shake256 v_LEN input

let v_XOFx4 (v_LEN v_K: usize) (input: t_Array (t_Array u8 (sz 34)) v_K)
    : FStar.HyperStack.ST.St (t_Array (t_Array u8 v_LEN) v_K) =
  let out:t_Array (t_Array u8 v_LEN) v_K =
    Rust_primitives.Hax.repeat (Rust_primitives.Hax.repeat 0uy v_LEN <: t_Array u8 v_LEN) v_K
  in
  let _:Prims.unit =
    Rust_primitives.f_for_loop (sz 0)
      v_K
      (fun i ->
          let i:usize = i in
          Rust_primitives.Hax.Monomorphized_update_at.update_array_at_usize out
            i
            (Libcrux.Digest.shake128 v_LEN
                (Rust_primitives.unsize (input.[ i ] <: t_Array u8 (sz 34)) <: t_Slice u8)
              <:
              t_Array u8 v_LEN)
          <:
          Prims.unit)
  in
  out
