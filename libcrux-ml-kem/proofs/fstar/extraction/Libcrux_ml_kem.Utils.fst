module Libcrux_ml_kem.Utils
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

let into_padded_array (v_LEN: usize) (slice: t_Slice u8) =
  let out:t_Array u8 v_LEN = Rust_primitives.Hax.repeat 0uy v_LEN in
  let out:t_Array u8 v_LEN =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range out
      ({
          Core.Ops.Range.f_start = sz 0;
          Core.Ops.Range.f_end = Core.Slice.impl__len #u8 slice <: usize
        }
        <:
        Core.Ops.Range.t_Range usize)
      (Core.Slice.impl__copy_from_slice #u8
          (out.[ {
                Core.Ops.Range.f_start = sz 0;
                Core.Ops.Range.f_end = Core.Slice.impl__len #u8 slice <: usize
              }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
          slice
        <:
        t_Slice u8)
  in
  let _:Prims.unit = assert (Seq.slice out 0 (Seq.length slice) == slice) in
  let _:Prims.unit =
    assert (Seq.slice out (Seq.length slice) (v v_LEN) ==
        Seq.slice (Seq.create (v v_LEN) 0uy) (Seq.length slice) (v v_LEN))
  in
  let _:Prims.unit =
    assert (forall i. i < Seq.length slice ==> Seq.index out i == Seq.index slice i)
  in
  let _:Prims.unit =
    assert (forall i.
          (i >= Seq.length slice && i < v v_LEN) ==>
          Seq.index out i ==
          Seq.index (Seq.slice out (Seq.length slice) (v v_LEN)) (i - Seq.length slice))
  in
  let _:Prims.unit =
    Seq.lemma_eq_intro out (Seq.append slice (Seq.create (v v_LEN - Seq.length slice) 0uy))
  in
  out
