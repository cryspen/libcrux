module Libcrux_ml_dsa.Proof_utils
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open FStar.Mul
open Core_models

assume
val lemma_movemask_ps_bound (a: Libcrux_core_models.Abstractions.Bitvec.t_BitVec (mk_u64 256))
    : Lemma
      (ensures
        v (Libcrux_intrinsics.Avx2.mm256_movemask_ps a) >= 0 /\
        v (Libcrux_intrinsics.Avx2.mm256_movemask_ps a) < 256)

assume
val lemma_count_ones_nibble (x: i32)
    : Lemma (requires v x >= 0 /\ v x < 16)
      (ensures v (Core_models.Num.impl_i32__count_ones x) <= 4)

assume
val lemma_count_ones_byte (x: i32)
    : Lemma (requires v x >= 0 /\ v x < 256)
      (ensures v (Core_models.Num.impl_i32__count_ones x) <= 8)

assume
val lemma_count_ones_byte_exact (m: i32) (b0 b1 b2 b3 b4 b5 b6 b7: bool)
    : Lemma
      (requires
        v m ==
        (if b0 then 1 else 0) + (if b1 then 2 else 0) + (if b2 then 4 else 0) +
        (if b3 then 8 else 0) + (if b4 then 16 else 0) + (if b5 then 32 else 0) +
        (if b6 then 64 else 0) + (if b7 then 128 else 0))
      (ensures
        v (Core_models.Num.impl_i32__count_ones m) ==
        (if b0 then 1 else 0) + (if b1 then 1 else 0) + (if b2 then 1 else 0) +
        (if b3 then 1 else 0) + (if b4 then 1 else 0) + (if b5 then 1 else 0) +
        (if b6 then 1 else 0) + (if b7 then 1 else 0))
