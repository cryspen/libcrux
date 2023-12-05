module Libcrux.Kem.Kyber.Hash_functions
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let v_G (input: t_Slice u8) =
  let res = Libcrux.Digest.sha3_512_ input in
  admit(); // We assume that sha3_512 correctly implements G
  res

let v_H (input: t_Slice u8) =
  let res = Libcrux.Digest.sha3_256_ input in
  admit(); // We assume that sha3_512 correctly implements H
  res

let v_PRF (v_LEN: usize) (input: t_Slice u8) =
  let res = Libcrux.Digest.shake256 v_LEN input in
  admit(); // We assume that sha3_512 correctly implements H
  res

let v_XOFx4 (v_LEN v_K: usize) (input: t_Array (t_Array u8 (sz 34)) v_K) =
  let out:t_Array (t_Array u8 v_LEN) v_K =
    Rust_primitives.Hax.repeat (Rust_primitives.Hax.repeat 0uy v_LEN <: t_Array u8 v_LEN) v_K
  in
  let out:t_Array (t_Array u8 v_LEN) v_K =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = v_K
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      out
      (fun out i ->
          let out:t_Array (t_Array u8 v_LEN) v_K = out in
          let i:usize = i in
          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
            i
            (Libcrux.Digest.shake128 v_LEN
                (Rust_primitives.unsize (input.[ i ] <: t_Array u8 (sz 34)) <: t_Slice u8)
              <:
              t_Array u8 v_LEN)
          <:
          t_Array (t_Array u8 v_LEN) v_K)
  in
  admit(); // We should prove that v_XOFx4 correctly implements Keccakx4
  out
