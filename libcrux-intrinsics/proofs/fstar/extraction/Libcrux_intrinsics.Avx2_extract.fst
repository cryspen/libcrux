module Libcrux_intrinsics.Avx2_extract
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open Core
open FStar.Mul

include BitVec.Intrinsics {mm256_and_si256 as mm256_and_si256}
val lemma_mm256_set1_epi16 lhs rhs
  : Lemma (   vec256_as_i16x16 (mm256_and_si256 lhs rhs)
           == Spec.Utils.map2 (&.) (vec256_as_i16x16 lhs) (vec256_as_i16x16 rhs)
          )
          [SMTPat (vec256_as_i16x16 (mm256_and_si256 lhs rhs))]
