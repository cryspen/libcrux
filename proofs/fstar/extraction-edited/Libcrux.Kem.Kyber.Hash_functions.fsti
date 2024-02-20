module Libcrux.Kem.Kyber.Hash_functions
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

val v_G (input: t_Slice u8) : Prims.Pure (t_Array u8 (sz 64)) Prims.l_True
          (ensures (fun res -> res == Spec.Kyber.v_G input))

val v_H (input: t_Slice u8) : Prims.Pure (t_Array u8 (sz 32)) Prims.l_True
          (ensures (fun res -> res == Spec.Kyber.v_H input))

val v_PRF (v_LEN: usize) (input: t_Slice u8)
    : Prims.Pure (t_Array u8 v_LEN) Prims.l_True
          (ensures (fun res -> res == Spec.Kyber.v_PRF v_LEN input))
          
val v_XOFx4 (v_K: usize{v v_K >= 2 /\ v v_K <= 4}) (input: t_Array (t_Array u8 (sz 34)) v_K)
    : Prims.Pure (t_Array (t_Array u8 (sz 840)) v_K) Prims.l_True
          (ensures (fun res ->
            (forall i. i < v v_K ==> Seq.index res i == Spec.Kyber.v_XOF (sz 840) (Seq.index input i))))
