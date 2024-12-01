module Libcrux_ml_kem.Utils
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

val prf_input_inc (v_K: usize) (prf_inputs: t_Array (t_Array u8 (sz 33)) v_K) (domain_separator: u8)
    : Prims.Pure (t_Array (t_Array u8 (sz 33)) v_K & u8)
      (requires range (v domain_separator + v v_K) u8_inttype)
      (ensures
        fun temp_0_ ->
          let prf_inputs_future, ds:(t_Array (t_Array u8 (sz 33)) v_K & u8) = temp_0_ in
          v ds == v domain_separator + v v_K /\
          (forall (i: nat).
              i < v v_K ==>
              v (Seq.index (Seq.index prf_inputs_future i) 32) == v domain_separator + i /\
              Seq.slice (Seq.index prf_inputs_future i) 0 32 ==
              Seq.slice (Seq.index prf_inputs i) 0 32))

/// Pad the `slice` with `0`s at the end.
val into_padded_array (v_LEN: usize) (slice: t_Slice u8)
    : Prims.Pure (t_Array u8 v_LEN)
      (requires (Core.Slice.impl__len #u8 slice <: usize) <=. v_LEN)
      (ensures
        fun result ->
          let result:t_Array u8 v_LEN = result in
          result == Seq.append slice (Seq.create (v v_LEN - v (Core.Slice.impl__len #u8 slice)) 0uy)
      )
