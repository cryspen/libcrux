module RmMe2
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"

open FStar.Mul
open FStar.FunctionalExtensionality

unfold type fnarr (n: nat) (t: Type0) = i:nat {i < n} ^-> t

assume val i32: Type0

assume val bv: Type0
assume val from_i32x8: fnarr 8 i32 -> bv
assume val to_i32x8: bv -> fnarr 8 i32

let to_from_i32x8 (x: fnarr 8 i32) (i: nat {i < 8})
  : Lemma (to_i32x8 (from_i32x8 x) i == x i) 
    [SMTPat (to_i32x8 (from_i32x8 x) i)] = admit ()

let to_from_i32x8' (x: fnarr 8 i32)
  : Lemma (to_i32x8 (from_i32x8 x) == x) 
    [SMTPat (to_i32x8 (from_i32x8 x))]= admit ()

assume val spec: i32 -> i32 -> i32

let body (lhs rhs: bv): fnarr 8 i32 =
  (FStar.FunctionalExtensionality.on_domain (i:
        nat { i < 8 })
      (fun i ->
          match i with
          | 0 -> spec (to_i32x8 lhs 0) (to_i32x8 rhs 0)
          | 1 -> spec (to_i32x8 lhs 1) (to_i32x8 rhs 1)
          | 2 -> spec (to_i32x8 lhs 2) (to_i32x8 rhs 2)
          | 3 -> spec (to_i32x8 lhs 3) (to_i32x8 rhs 3)
          | 4 -> spec (to_i32x8 lhs 4) (to_i32x8 rhs 4)
          | 5 -> spec (to_i32x8 lhs 5) (to_i32x8 rhs 5)
          | 6 -> spec (to_i32x8 lhs 6) (to_i32x8 rhs 6)
          | 7 -> spec (to_i32x8 lhs 7) (to_i32x8 rhs 7)))

unfold let test (lhs rhs: bv) = from_i32x8 (body lhs rhs)

let test_lemma (lhs rhs: bv) =
    // to_from_i32x8 (body lhs rhs) 0;
    assert (
        to_i32x8 (test lhs rhs) 0
     == spec (to_i32x8 lhs 0) (to_i32x8 rhs 0)
    )
