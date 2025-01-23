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

#push-options "--z3rlimit 200"

let prf_input_inc (v_K: usize) (prf_inputs: t_Array (t_Array u8 (sz 33)) v_K) (domain_separator: u8) =
  let v__domain_separator_init:u8 = domain_separator in
  let v__prf_inputs_init:t_Array (t_Array u8 (sz 33)) v_K =
    Core.Clone.f_clone #(t_Array (t_Array u8 (sz 33)) v_K)
      #FStar.Tactics.Typeclasses.solve
      prf_inputs
  in
  let domain_separator, prf_inputs:(u8 & t_Array (t_Array u8 (sz 33)) v_K) =
    Rust_primitives.Hax.Folds.fold_range (sz 0)
      v_K
      (fun temp_0_ i ->
          let domain_separator, prf_inputs:(u8 & t_Array (t_Array u8 (sz 33)) v_K) = temp_0_ in
          let i:usize = i in
          v domain_separator == v v__domain_separator_init + v i /\
          (v i < v v_K ==>
            (forall (j: nat).
                (j >= v i /\ j < v v_K) ==> prf_inputs.[ sz j ] == v__prf_inputs_init.[ sz j ])) /\
          (forall (j: nat).
              j < v i ==>
              v (Seq.index (Seq.index prf_inputs j) 32) == v v__domain_separator_init + j /\
              Seq.slice (Seq.index prf_inputs j) 0 32 ==
              Seq.slice (Seq.index v__prf_inputs_init j) 0 32))
      (domain_separator, prf_inputs <: (u8 & t_Array (t_Array u8 (sz 33)) v_K))
      (fun temp_0_ i ->
          let domain_separator, prf_inputs:(u8 & t_Array (t_Array u8 (sz 33)) v_K) = temp_0_ in
          let i:usize = i in
          let prf_inputs:t_Array (t_Array u8 (sz 33)) v_K =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize prf_inputs
              i
              (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (prf_inputs.[ i ]
                    <:
                    t_Array u8 (sz 33))
                  (sz 32)
                  domain_separator
                <:
                t_Array u8 (sz 33))
          in
          let domain_separator:u8 = domain_separator +! 1uy in
          domain_separator, prf_inputs <: (u8 & t_Array (t_Array u8 (sz 33)) v_K))
  in
  let hax_temp_output:u8 = domain_separator in
  prf_inputs, hax_temp_output <: (t_Array (t_Array u8 (sz 33)) v_K & u8)

#pop-options
