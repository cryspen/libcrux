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

let lemma_shl_xor_shr_is_rotate_left (x: u64) (v_LEFT v_RIGHT: i32)
  : Lemma
      (requires
        v v_LEFT >= 0 /\ v v_LEFT < 64 /\
        v v_RIGHT > 0 /\ v v_RIGHT < 64 /\
        v v_LEFT + v v_RIGHT == 64)
      (ensures
        ((x <<! v_LEFT) ^. (x >>! v_RIGHT)) ==
        Core_models.Num.impl_u64__rotate_left x (cast (v_LEFT <: i32) <: u32))
  = admit ()
