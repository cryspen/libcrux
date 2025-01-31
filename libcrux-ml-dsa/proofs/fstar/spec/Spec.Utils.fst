module Spec.Utils
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
open FStar.Mul
open Core

#push-options "--z3rlimit 100 --split_queries always"
let lemma_range_at_percent (v:int) (p:int{p>0/\ p%2=0 /\ v < p/2 /\ v >= -p / 2}):
  Lemma (v @% p == v) =
    let m = v % p in
    if v < 0 then (
      Math.Lemmas.lemma_mod_plus v 1 p;
      assert ((v + p) % p == v % p);
      assert (v + p >= 0);
      assert (v + p < p);
      Math.Lemmas.modulo_lemma (v+p) p;
      assert (m == v + p);
      assert (m >= p/2);
      assert (v @% p == m - p);
      assert (v @% p == v))
    else (
      assert (v >= 0 /\ v < p);
      Math.Lemmas.modulo_lemma v p;
      assert (v % p == v);
      assert (m < p/2);
      assert (v @% p == v)
    )
#pop-options

let lemma_div_at_percent (v:int) (p:int{p>0/\ p%2=0 /\ (v/p) < p/2 /\ (v/p) >= -p / 2}):
  Lemma ((v / p) @% p == v / p) = 
    lemma_range_at_percent (v/p) p

/// Bounded integers

let is_intb (l:nat) (x:int) = (x <= l) && (x >= -l)

let is_i32b (l:nat) (x:i32) = is_intb l (v x)
let is_i64b (l:nat) (x:i64) = is_intb l (v x)

let is_i32b_array (l:nat) (x:t_Slice i32) = forall i. i < Seq.length x ==> is_i32b l (Seq.index x i)

#push-options "--z3rlimit 200"
val lemma_mul_i32b (b1 b2: nat) (n1 n2: i32) 
    : Lemma (requires (is_i32b b1 n1 /\ is_i32b b2 n2 /\ b1 * b2 < pow2 63))
      (ensures (range (v n1 * v n2) i64_inttype /\ 
                is_i64b (b1 * b2) ((cast n1 <: i64) *! (cast n2 <: i64)) /\
                v ((cast n1 <: i64) *! (cast n2 <: i64)) == v n1 * v n2))
      
let lemma_mul_i32b (b1 b2: nat) (n1 n2: i32) =
  if v n1 = 0 || v n2 = 0
  then ()
  else 
    let open FStar.Math.Lemmas in
    lemma_abs_bound (v n1) b1;
    lemma_abs_bound (v n2) b2;
    lemma_abs_mul (v n1) (v n2);
    lemma_mult_le_left (abs (v n1)) (abs (v n2)) b2;
    lemma_mult_le_right b2 (abs (v n1)) b1;
    lemma_abs_bound (v n1 * v n2) (b1 * b2)
#pop-options
