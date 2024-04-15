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

let v_XOFx4 v_K (input: t_Array (t_Array u8 (sz 34)) v_K) =
  assert (v v_K >= 2);
  let out:t_Array (t_Array u8 (sz 840)) v_K =
    Rust_primitives.Hax.repeat (Rust_primitives.Hax.repeat 0uy (sz 840) <: t_Array u8 (sz 840)) v_K
  in
  let out:t_Array (t_Array u8 (sz 840)) v_K =
    if ~.(Libcrux_platform.Platform.simd256_support () <: bool)
    then
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
            let out:t_Array (t_Array u8 (sz 840)) v_K = out in
            let i:usize = i in
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
              i
              (Libcrux.Digest.shake128 (sz 840)
                  (Rust_primitives.unsize (input.[ i ] <: t_Array u8 (sz 34)) <: t_Slice u8)
                <:
                t_Array u8 (sz 840))
            <:
            t_Array (t_Array u8 (sz 840)) v_K)
    else
      let out:t_Array (t_Array u8 (sz 840)) v_K =
        match cast (v_K <: usize) <: u8 with
        | 2uy ->
          let d0, d1, _, _:(t_Array u8 (sz 840) & t_Array u8 (sz 840) & t_Array u8 (sz 840) &
            t_Array u8 (sz 840)) =
            Libcrux.Digest.shake128x4 (sz 840)
              (Rust_primitives.unsize (input.[ sz 0 ] <: t_Array u8 (sz 34)) <: t_Slice u8)
              (Rust_primitives.unsize (input.[ sz 1 ] <: t_Array u8 (sz 34)) <: t_Slice u8)
              (Rust_primitives.unsize (input.[ sz 0 ] <: t_Array u8 (sz 34)) <: t_Slice u8)
              (Rust_primitives.unsize (input.[ sz 1 ] <: t_Array u8 (sz 34)) <: t_Slice u8)
          in
          let out:t_Array (t_Array u8 (sz 840)) v_K =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (sz 0) d0
          in
          let out:t_Array (t_Array u8 (sz 840)) v_K =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (sz 1) d1
          in
          out
        | 3uy ->
          assert (v (cast v_K <: u8) = 3);
          let d0, d1, d2, _:(t_Array u8 (sz 840) & t_Array u8 (sz 840) & t_Array u8 (sz 840) &
            t_Array u8 (sz 840)) =
            Libcrux.Digest.shake128x4 (sz 840)
              (Rust_primitives.unsize (input.[ sz 0 ] <: t_Array u8 (sz 34)) <: t_Slice u8)
              (Rust_primitives.unsize (input.[ sz 1 ] <: t_Array u8 (sz 34)) <: t_Slice u8)
              (Rust_primitives.unsize (input.[ sz 2 ] <: t_Array u8 (sz 34)) <: t_Slice u8)
              (Rust_primitives.unsize (input.[ sz 0 ] <: t_Array u8 (sz 34)) <: t_Slice u8)
          in
          let out:t_Array (t_Array u8 (sz 840)) v_K =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (sz 0) d0
          in
          let out:t_Array (t_Array u8 (sz 840)) v_K =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (sz 1) d1
          in
          let out:t_Array (t_Array u8 (sz 840)) v_K =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (sz 2) d2
          in
          out
        | 4uy ->
          assert (v (cast v_K <: u8) = 4);
          let d0, d1, d2, d3:(t_Array u8 (sz 840) & t_Array u8 (sz 840) & t_Array u8 (sz 840) &
            t_Array u8 (sz 840)) =
            Libcrux.Digest.shake128x4 (sz 840)
              (Rust_primitives.unsize (input.[ sz 0 ] <: t_Array u8 (sz 34)) <: t_Slice u8)
              (Rust_primitives.unsize (input.[ sz 1 ] <: t_Array u8 (sz 34)) <: t_Slice u8)
              (Rust_primitives.unsize (input.[ sz 2 ] <: t_Array u8 (sz 34)) <: t_Slice u8)
              (Rust_primitives.unsize (input.[ sz 3 ] <: t_Array u8 (sz 34)) <: t_Slice u8)
          in
          let out:t_Array (t_Array u8 (sz 840)) v_K =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (sz 0) d0
          in
          let out:t_Array (t_Array u8 (sz 840)) v_K =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (sz 1) d1
          in
          let out:t_Array (t_Array u8 (sz 840)) v_K =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (sz 2) d2
          in
          let out:t_Array (t_Array u8 (sz 840)) v_K =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out (sz 3) d3
          in
          out
        | _ -> out
      in
      out
  in
  admit(); // We assume that shake128x4 correctly implements XOFx4
  out 
