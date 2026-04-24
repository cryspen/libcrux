module Libcrux_sha3.Proof_utils.Lemmas
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open FStar.Mul
open Core_models

let lemma_div_mul_mod (a b: usize)
    : Lemma
        (requires b <>. mk_usize 0)
        (ensures (a /! b) *! b +! (a %! b) =. a)
    = ()

let rec lemma_mul_succ_le (k n d: usize)
  : Lemma
    (requires (v k) < (v n))
    (ensures (v k) * (v d) + (v d) <= (v n) * (v d))
    (decreases (v n)) =
  if v n = 0 then ()
  else if v k = v n - 1 then ()
  else lemma_mul_succ_le k (n -! mk_usize 1) d
