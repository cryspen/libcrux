module Libcrux.Kem.Kyber.Hash_functions
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

val v_G (input: t_Slice u8)
        : Pure (t_Array u8 (sz 64))
          (requires True)
          (ensures (fun res -> res == Spec.Kyber.v_G input))

val v_H (input: t_Slice u8)
        : Pure (t_Array u8 (sz 32))
          (requires True)
          (ensures (fun res -> res == Spec.Kyber.v_H input))

val v_PRF (v_LEN: usize) (input: t_Slice u8)
        : Pure (t_Array u8 v_LEN)
          (requires True)
          (ensures (fun res -> res == Spec.Kyber.v_PRF v_LEN input))

val v_XOFx4 (v_LEN v_K: usize) (input: t_Array (t_Array u8 (sz 34)) v_K)
        : Pure (t_Array (t_Array u8 v_LEN) v_K)
          (requires True)
          (ensures (fun res ->
            (forall i. i < v v_K ==> Seq.index res i == Spec.Kyber.v_XOF v_LEN (Seq.index input i))))
          
