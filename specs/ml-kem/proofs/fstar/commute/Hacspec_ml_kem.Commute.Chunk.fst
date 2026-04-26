module Hacspec_ml_kem.Commute.Chunk
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open FStar.Mul
open Core_models
open Libcrux_ml_kem.Vector.Traits.Spec

(* Layer 0 — field-element scalar commute lemmas.
   Each consumes an existing impl post of the form `v r % 3329 == <eqn>`
   and produces a `t_FieldElement`-level equation via `i16_to_spec_fe` or
   `mont_i16_to_spec_fe`.  These are the primitive bridges from the impl's
   raw mod-q arithmetic to the hacspec FE algebra. *)

module P  = Hacspec_ml_kem.Parameters
module L  = FStar.Math.Lemmas
module T  = Libcrux_ml_kem.Vector.Traits
module TS = Libcrux_ml_kem.Vector.Traits.Spec
module N  = Hacspec_ml_kem.Ntt
module IN = Hacspec_ml_kem.Invert_ntt
module CP = Hacspec_ml_kem.Compress

(* Basic sanity: the two lifts produce valid FEs by construction. *)
let lemma_i16_to_spec_fe_bounded (x: i16) :
    Lemma ((i16_to_spec_fe x).P.f_val <. P.v_FIELD_MODULUS)
  = ()

let lemma_mont_i16_to_spec_fe_bounded (x: i16) :
    Lemma ((mont_i16_to_spec_fe x).P.f_val <. P.v_FIELD_MODULUS)
  = ()

(* Addition commutes with `i16_to_spec_fe` whenever the impl post states
   the algebraic identity at the int level.  Since `add` is linear, the
   same lemma holds when both sides are lifted via `mont_i16_to_spec_fe`. *)
let lemma_add_fe_commute_plain (a b r: i16) :
    Lemma (requires v r == v a + v b)
          (ensures  P.impl_FieldElement__add (i16_to_spec_fe a) (i16_to_spec_fe b)
                    == i16_to_spec_fe r)
  = ()

let lemma_add_fe_commute_mont (a b r: i16) :
    Lemma (requires v r == v a + v b)
          (ensures  P.impl_FieldElement__add
                        (mont_i16_to_spec_fe a) (mont_i16_to_spec_fe b)
                    == mont_i16_to_spec_fe r)
  = ()

let lemma_sub_fe_commute_plain (a b r: i16) :
    Lemma (requires v r == v a - v b)
          (ensures  P.impl_FieldElement__sub (i16_to_spec_fe a) (i16_to_spec_fe b)
                    == i16_to_spec_fe r)
  = ()

let lemma_sub_fe_commute_mont (a b r: i16) :
    Lemma (requires v r == v a - v b)
          (ensures  P.impl_FieldElement__sub
                        (mont_i16_to_spec_fe a) (mont_i16_to_spec_fe b)
                    == mont_i16_to_spec_fe r)
  = ()

(* Barrett reduction preserves value mod q, i.e. is identity under the
   plain lift. *)
let lemma_barrett_fe_commute (a r: i16) :
    Lemma (requires v r % 3329 == v a % 3329)
          (ensures  i16_to_spec_fe r == i16_to_spec_fe a)
  = ()

(* Zeta cancellation: the impl stores zetas pre-multiplied by R, so
   `mont_i16_to_spec_fe zeta_mont` recovers the plain abstract zeta.
   Its post exactly matches the canonical nonneg form of both lifts. *)
let lemma_mont_zeta_cancel (zeta_mont zeta_plain: i16) :
    Lemma (requires (v zeta_mont * 169) % 3329 == v zeta_plain % 3329)
          (ensures  mont_i16_to_spec_fe zeta_mont == i16_to_spec_fe zeta_plain)
  = ()

(* The `v .f_val` equalities for `i16_to_spec_fe` / `mont_i16_to_spec_fe`
   are now delivered by each lift's return refinement, so the only helper
   we still need is the one that exposes the f_val of `impl_FieldElement__mul`. *)
let lemma_impl_mul_v_val (x y: P.t_FieldElement) :
    Lemma (v (P.impl_FieldElement__mul x y).P.f_val
             == (v x.P.f_val * v y.P.f_val) % 3329)
  = ()

let lemma_impl_add_v_val (x y: P.t_FieldElement) :
    Lemma (v (P.impl_FieldElement__add x y).P.f_val
             == (v x.P.f_val + v y.P.f_val) % 3329)
  = ()

let lemma_impl_sub_v_val (x y: P.t_FieldElement) :
    Lemma (v (P.impl_FieldElement__sub x y).P.f_val
             == (v x.P.f_val - v y.P.f_val) % 3329)
  = ()

(* Scalar modular-arithmetic cores.  Proved at the `int` level so the
   wrapping lemmas only have to line up `v`-value equalities. *)

let lemma_mont_mul_mod_core (a b r: int) :
    Lemma (requires r % 3329 == (a * b * 169) % 3329)
          (ensures  (((a * 169) % 3329) * ((b * 169) % 3329)) % 3329
                    == (r * 169) % 3329)
  = let q : pos = 3329 in
    L.lemma_mod_mul_distr_l (a * 169) ((b * 169) % q) q;
    L.lemma_mod_mul_distr_r (a * 169) (b * 169) q;
    assert ((a * 169) * (b * 169) == a * b * 169 * 169);
    L.lemma_mod_mul_distr_l (a * b * 169) 169 q;
    L.lemma_mod_mul_distr_l r 169 q

let lemma_mont_plain_mul_mod_core (a b r: int) :
    Lemma (requires r % 3329 == (a * b * 169) % 3329)
          (ensures  (((a * 169) % 3329) * (b % 3329)) % 3329 == r % 3329)
  = let q : pos = 3329 in
    L.lemma_mod_mul_distr_l (a * 169) (b % q) q;
    L.lemma_mod_mul_distr_r (a * 169) b q;
    assert ((a * 169) * b == a * b * 169)

let lemma_mul_const_mod_core (a c r: int) :
    Lemma (requires r == a * c)
          (ensures  ((a % 3329) * (c % 3329)) % 3329 == r % 3329)
  = let q : pos = 3329 in
    L.lemma_mod_mul_distr_l a (c % q) q;
    L.lemma_mod_mul_distr_r a c q

(* Integer-level modular cores for the mod-aware add / sub lifts.
   Each shows that under the mont lift, residue equality at the i16 level
   transfers to f_val equality. *)

let lemma_add_mont_mod_core (a b r: int) :
    Lemma (requires r % 3329 == (a + b) % 3329)
          (ensures  (((a * 169) % 3329) + ((b * 169) % 3329)) % 3329
                    == (r * 169) % 3329)
  = let q : pos = 3329 in
    L.lemma_mod_add_distr ((a * 169) % q) (b * 169) q;
    L.lemma_mod_add_distr (b * 169) (a * 169) q;
    assert (a * 169 + b * 169 == (a + b) * 169);
    L.lemma_mod_mul_distr_l (a + b) 169 q;
    L.lemma_mod_mul_distr_l r 169 q

let lemma_sub_mont_mod_core (a b r: int) :
    Lemma (requires r % 3329 == (a - b) % 3329)
          (ensures  (((a * 169) % 3329) - ((b * 169) % 3329)) % 3329
                    == (r * 169) % 3329)
  = let q : pos = 3329 in
    L.lemma_mod_sub_distr ((a * 169) % q) (b * 169) q;
    L.lemma_mod_add_distr (- ((b * 169) % q)) (a * 169) q;
    assert (a * 169 - b * 169 == (a - b) * 169);
    L.lemma_mod_mul_distr_l (a - b) 169 q;
    L.lemma_mod_mul_distr_l r 169 q

(* Mod-aware addition: same hypothesis shape as
   `ntt_spec` / `inv_ntt_spec` give for the butterfly outputs. *)
let lemma_add_fe_commute_mont_mod (a b r: i16) :
    Lemma (requires v r % 3329 == (v a + v b) % 3329)
          (ensures  P.impl_FieldElement__add
                        (mont_i16_to_spec_fe a) (mont_i16_to_spec_fe b)
                    == mont_i16_to_spec_fe r)
  = lemma_impl_add_v_val (mont_i16_to_spec_fe a) (mont_i16_to_spec_fe b);
    lemma_add_mont_mod_core (v a) (v b) (v r)

let lemma_sub_fe_commute_mont_mod (a b r: i16) :
    Lemma (requires v r % 3329 == (v a - v b) % 3329)
          (ensures  P.impl_FieldElement__sub
                        (mont_i16_to_spec_fe a) (mont_i16_to_spec_fe b)
                    == mont_i16_to_spec_fe r)
  = lemma_impl_sub_v_val (mont_i16_to_spec_fe a) (mont_i16_to_spec_fe b);
    lemma_sub_mont_mod_core (v a) (v b) (v r)

(* Butterfly commute lemmas.  `Spec.Utils.ntt_spec` (and `inv_ntt_spec`)
   produce exactly one of these residue hypotheses per lane; the
   portable impl's `ntt_layer_1_step` wrapper folds them across 4
   butterfly pairs to discharge `forall4`-pointwise FE equalities. *)

let lemma_butterfly_mod_core (a b z r: int) :
    Lemma (requires r % 3329 == (a + b * z * 169) % 3329)
          (ensures  ((a * 169) % 3329
                     + (((z * 169) % 3329) * ((b * 169) % 3329)) % 3329) % 3329
                    == (r * 169) % 3329)
  = let q : pos = 3329 in
    L.lemma_mod_mul_distr_l (z * 169) ((b * 169) % q) q;
    L.lemma_mod_mul_distr_r (z * 169) (b * 169) q;
    assert ((z * 169) * (b * 169) == b * z * 169 * 169);
    L.lemma_mod_add_distr ((a * 169) % q) (b * z * 169 * 169) q;
    L.lemma_mod_add_distr (b * z * 169 * 169) (a * 169) q;
    assert (a * 169 + b * z * 169 * 169 == (a + b * z * 169) * 169);
    L.lemma_mod_mul_distr_l (a + b * z * 169) 169 q;
    L.lemma_mod_mul_distr_l r 169 q

let lemma_butterfly_fe_commute_plus (vec_i vec_j zeta result_i: i16) :
  Lemma (requires v result_i % 3329
                  == (v vec_i + v vec_j * v zeta * 169) % 3329)
        (ensures  mont_i16_to_spec_fe result_i ==
                  P.impl_FieldElement__add
                    (mont_i16_to_spec_fe vec_i)
                    (P.impl_FieldElement__mul
                      (mont_i16_to_spec_fe zeta)
                      (mont_i16_to_spec_fe vec_j)))
  = let prod_fe = P.impl_FieldElement__mul (mont_i16_to_spec_fe zeta)
                                            (mont_i16_to_spec_fe vec_j) in
    lemma_impl_mul_v_val (mont_i16_to_spec_fe zeta) (mont_i16_to_spec_fe vec_j);
    lemma_impl_add_v_val (mont_i16_to_spec_fe vec_i) prod_fe;
    lemma_butterfly_mod_core (v vec_i) (v vec_j) (v zeta) (v result_i)

let lemma_butterfly_sub_mod_core (a b z r: int) :
    Lemma (requires r % 3329 == (a - b * z * 169) % 3329)
          (ensures  ((a * 169) % 3329
                     - (((z * 169) % 3329) * ((b * 169) % 3329)) % 3329) % 3329
                    == (r * 169) % 3329)
  = let q : pos = 3329 in
    L.lemma_mod_mul_distr_l (z * 169) ((b * 169) % q) q;
    L.lemma_mod_mul_distr_r (z * 169) (b * 169) q;
    assert ((z * 169) * (b * 169) == b * z * 169 * 169);
    L.lemma_mod_sub_distr ((a * 169) % q) (b * z * 169 * 169) q;
    L.lemma_mod_add_distr (- (b * z * 169 * 169)) (a * 169) q;
    assert (a * 169 - b * z * 169 * 169 == (a - b * z * 169) * 169);
    L.lemma_mod_mul_distr_l (a - b * z * 169) 169 q;
    L.lemma_mod_mul_distr_l r 169 q

let lemma_butterfly_fe_commute_minus (vec_i vec_j zeta result_j: i16) :
  Lemma (requires v result_j % 3329
                  == (v vec_i - v vec_j * v zeta * 169) % 3329)
        (ensures  mont_i16_to_spec_fe result_j ==
                  P.impl_FieldElement__sub
                    (mont_i16_to_spec_fe vec_i)
                    (P.impl_FieldElement__mul
                      (mont_i16_to_spec_fe zeta)
                      (mont_i16_to_spec_fe vec_j)))
  = let prod_fe = P.impl_FieldElement__mul (mont_i16_to_spec_fe zeta)
                                            (mont_i16_to_spec_fe vec_j) in
    lemma_impl_mul_v_val (mont_i16_to_spec_fe zeta) (mont_i16_to_spec_fe vec_j);
    lemma_impl_sub_v_val (mont_i16_to_spec_fe vec_i) prod_fe;
    lemma_butterfly_sub_mod_core (v vec_i) (v vec_j) (v zeta) (v result_j)

(* Combined plus/minus: a single call produces both output-lane FE
   equations for one butterfly pair from its two `ntt_spec` residues. *)
let lemma_butterfly_pair_commute
    (vec result: t_Array i16 (mk_usize 16))
    (z: i16) (i: nat{i < 16}) (j: nat{j < 16}) :
  Lemma (requires
           v (Seq.index result i) % 3329
             == (v (Seq.index vec i) + v (Seq.index vec j) * v z * 169) % 3329 /\
           v (Seq.index result j) % 3329
             == (v (Seq.index vec i) - v (Seq.index vec j) * v z * 169) % 3329)
        (ensures
           mont_i16_to_spec_fe (Seq.index result i) ==
             P.impl_FieldElement__add
               (mont_i16_to_spec_fe (Seq.index vec i))
               (P.impl_FieldElement__mul (mont_i16_to_spec_fe z)
                                         (mont_i16_to_spec_fe (Seq.index vec j))) /\
           mont_i16_to_spec_fe (Seq.index result j) ==
             P.impl_FieldElement__sub
               (mont_i16_to_spec_fe (Seq.index vec i))
               (P.impl_FieldElement__mul (mont_i16_to_spec_fe z)
                                         (mont_i16_to_spec_fe (Seq.index vec j))))
  = lemma_butterfly_fe_commute_plus (Seq.index vec i) (Seq.index vec j) z (Seq.index result i);
    lemma_butterfly_fe_commute_minus (Seq.index vec i) (Seq.index vec j) z (Seq.index result j)

(* Inverse-butterfly (Gentleman–Sande) commute.  `inv_ntt_spec vec z i j
   result` gives:
     v result[i] % 3329 == (v vec[j] + v vec[i]) % 3329
     v result[j] % 3329 == ((v vec[j] − v vec[i]) · z · 169) % 3329
   and in FE algebra:
     mont_fe result[i] == mont_fe vec[i] + mont_fe vec[j]
     mont_fe result[j] == mont_fe z · (mont_fe vec[j] − mont_fe vec[i]). *)

let lemma_inv_butterfly_mul_diff_core (a b z r: int) :
    Lemma (requires r % 3329 == ((b - a) * z * 169) % 3329)
          (ensures  (((z * 169) % 3329)
                     * (((b * 169) % 3329 - (a * 169) % 3329) % 3329)) % 3329
                    == (r * 169) % 3329)
  = let q : pos = 3329 in
    L.lemma_mod_sub_distr ((b * 169) % q) (a * 169) q;
    L.lemma_mod_add_distr (- (a * 169)) (b * 169) q;
    assert (b * 169 - a * 169 == (b - a) * 169);
    L.lemma_mod_mul_distr_l (z * 169) (((b - a) * 169) % q) q;
    L.lemma_mod_mul_distr_r (z * 169) ((b - a) * 169) q;
    assert ((z * 169) * ((b - a) * 169) == (b - a) * z * 169 * 169);
    L.lemma_mod_mul_distr_l ((b - a) * z * 169) 169 q;
    L.lemma_mod_mul_distr_l r 169 q

let lemma_inv_butterfly_fe_commute_mul_diff (vec_i vec_j zeta result_j: i16) :
  Lemma (requires v result_j % 3329
                  == ((v vec_j - v vec_i) * v zeta * 169) % 3329)
        (ensures  mont_i16_to_spec_fe result_j ==
                  P.impl_FieldElement__mul
                    (mont_i16_to_spec_fe zeta)
                    (P.impl_FieldElement__sub
                      (mont_i16_to_spec_fe vec_j)
                      (mont_i16_to_spec_fe vec_i)))
  = let diff_fe = P.impl_FieldElement__sub (mont_i16_to_spec_fe vec_j)
                                            (mont_i16_to_spec_fe vec_i) in
    lemma_impl_sub_v_val (mont_i16_to_spec_fe vec_j) (mont_i16_to_spec_fe vec_i);
    lemma_impl_mul_v_val (mont_i16_to_spec_fe zeta) diff_fe;
    lemma_inv_butterfly_mul_diff_core (v vec_i) (v vec_j) (v zeta) (v result_j)

(* `base_case_multiply_even` commute.  The impl's `ntt_multiply_binomials_post`
   residue for the even lane is
     v r % q == ((a0*b0 + a1*b1*z*169) * 169) % q
   and the hacspec FE form is
     mont_fe r == (mont_fe a0 · mont_fe b0) + ((mont_fe a1 · mont_fe b1) · mont_fe z).

   Pending — C4e-followup.  Content is a direct analog of
   `lemma_butterfly_mod_core` with one extra Montgomery-unwrap level, and
   in isolation satisfies the ensures under a full mod-distr chain
   (`lemma_mod_mul_distr_l/r`, `lemma_mod_add_distr`).  Z3 does not
   converge on this encoding at r-limit 300 with `--split_queries
   always`: queries 1-4 succeed in 14, 54, 123, 642 ms but query 5 runs
   15+ minutes before timing out.  The auto-retry has been observed to
   succeed in 369 ms (one-off), confirming the math.  Deferred to a
   future pass — replace with the `butterfly` / `mont-mul` composition
   and/or per-level helper lemmas, or split the residue into two
   sub-lemmas. *)
#push-options "--z3rlimit 400"
let lemma_base_case_mult_even_mod_core (a0 a1 b0 b1 z r: int) :
    Lemma (requires r % 3329 == ((a0 * b0 + a1 * b1 * z * 169) * 169) % 3329)
          (ensures  ((((a0 * 169) % 3329 * (b0 * 169) % 3329) % 3329)
                     + ((((a1 * 169) % 3329 * (b1 * 169) % 3329) % 3329)
                        * ((z * 169) % 3329)) % 3329) % 3329
                    == (r * 169) % 3329)
  = let result = ((((a0 * 169) % 3329 * (b0 * 169) % 3329) % 3329)
                     + ((((a1 * 169) % 3329 * (b1 * 169) % 3329) % 3329)
                        * ((z * 169) % 3329)) % 3329) % 3329 in
    calc (==) {
      ((a0 * 169) % 3329) * (b0 * 169) % 3329;
      (==) {FStar.Math.Lemmas.lemma_mod_mul_distr_l
            (a0 * 169) (b0 * 169) 3329}
      ((a0 * 169) * (b0 * 169)) % 3329;
    };
    FStar.Math.Lemmas.lemma_mod_mod
      (((a0 * 169) * (b0 * 169)) % 3329)
      ((a0 * 169) * (b0 * 169))
      3329;
    calc (==) {
      ((a1 * 169) % 3329) * (b1 * 169) % 3329;
      (==) {FStar.Math.Lemmas.lemma_mod_mul_distr_l
            (a1 * 169) (b1 * 169) 3329}
      ((a1 * 169) * (b1 * 169)) % 3329;
    };
    FStar.Math.Lemmas.lemma_mod_mod
      (((a1 * 169) * (b1 * 169)) % 3329)
      ((a1 * 169) * (b1 * 169))
      3329;
    calc (==) {
     ((((a1 * 169) % 3329 * (b1 * 169) % 3329) % 3329)
                        * ((z * 169) % 3329)) % 3329;
     (==) { () }
     (((a1 * 169) * (b1 * 169)) % 3329
      * ((z * 169) % 3329)) % 3329;
     (==) { FStar.Math.Lemmas.lemma_mod_mul_distr_l
          ((a1 * 169) * (b1 * 169))
          ((z * 169) % 3329)
          3329}
     (((a1 * 169) * (b1 * 169))
      * ((z * 169) % 3329)) % 3329;
     (==) { FStar.Math.Lemmas.lemma_mod_mul_distr_r
          ((a1 * 169) * (b1 * 169))
          (z * 169)
          3329}
     (((a1 * 169) * (b1 * 169)) * (z * 169)) % 3329;
    };
    calc (==) {
      result;
      (==) { () }
      (((a0 * 169) * (b0 * 169)) % 3329 +
       (((a1 * 169) * (b1 * 169)) * (z * 169)) % 3329) % 3329;
      (==) { FStar.Math.Lemmas.lemma_mod_plus_distr_l
        ((a0 * 169) * (b0 * 169))
        ((((a1 * 169) * (b1 * 169)) * (z * 169)) % 3329)
        3329
        }
      (((a0 * 169) * (b0 * 169)) +
       (((a1 * 169) * (b1 * 169)) * (z * 169)) % 3329) % 3329;
      (==) { FStar.Math.Lemmas.lemma_mod_plus_distr_r
        ((a0 * 169) * (b0 * 169))
        ((((a1 * 169) * (b1 * 169)) * (z * 169)))
        3329
        }
      (((a0 * 169) * (b0 * 169)) +
       (((a1 * 169) * (b1 * 169)) * (z * 169))) % 3329;
    };
    calc (==) {
      (r * 169) % 3329;
      (==) { FStar.Math.Lemmas.lemma_mod_mul_distr_l r 169 3329}
      (r % 3329 * 169) % 3329;
      (==) { () }
      ((((a0 * b0 + a1 * b1 * z * 169) * 169) % 3329) * 169) % 3329;
      (==) { FStar.Math.Lemmas.lemma_mod_mul_distr_l
      ((a0 * b0 + a1 * b1 * z * 169) * 169)
      169 3329}
      (((a0 * b0 + a1 * b1 * z * 169) * 169) * 169) % 3329;
    };
    assert ((r * 169) % 3329 ==
      (((a0 * b0 + a1 * b1 * z * 169) * 169) * 169) % 3329)
#pop-options

(* Int-level FE-chain bridge for A1.  The chain
   `impl_add (impl_mul (mont a0) (mont b0)) (impl_mul (impl_mul (mont a1)
   (mont b1)) (mont z))` produces an f_val with both factors of each
   inner product inner-modded (`((a*169)%q) * ((b*169)%q)`).  A1's
   ensures has only the first factor inner-modded.  This wrapper does
   the two `lemma_mod_mul_distr_r` absorptions and invokes A1, so the
   FE-level lemma A2 is a clean chain. *)
let lemma_base_case_mult_even_mod_core_fe_form
    (a0 a1 b0 b1 z r: int) :
    Lemma (requires r % 3329 == ((a0 * b0 + a1 * b1 * z * 169) * 169) % 3329)
          (ensures  ((((a0 * 169) % 3329) * ((b0 * 169) % 3329)) % 3329
                     + ((((a1 * 169) % 3329) * ((b1 * 169) % 3329)) % 3329
                        * ((z * 169) % 3329)) % 3329) % 3329
                    == (r * 169) % 3329)
  = L.lemma_mod_mul_distr_r ((a0 * 169) % 3329) (b0 * 169) 3329;
    L.lemma_mod_mul_distr_r ((a1 * 169) % 3329) (b1 * 169) 3329;
    lemma_base_case_mult_even_mod_core a0 a1 b0 b1 z r

let lemma_base_case_mult_even_fe_commute
    (a0 a1 b0 b1 zeta result: i16) :
  Lemma (requires v result % 3329
                  == ((v a0 * v b0 + v a1 * v b1 * v zeta * 169) * 169) % 3329)
        (ensures
           mont_i16_to_spec_fe result ==
             P.impl_FieldElement__add
               (P.impl_FieldElement__mul (mont_i16_to_spec_fe a0) (mont_i16_to_spec_fe b0))
               (P.impl_FieldElement__mul
                 (P.impl_FieldElement__mul (mont_i16_to_spec_fe a1) (mont_i16_to_spec_fe b1))
                 (mont_i16_to_spec_fe zeta)))
  = let a0_fe = mont_i16_to_spec_fe a0 in
    let b0_fe = mont_i16_to_spec_fe b0 in
    let a1_fe = mont_i16_to_spec_fe a1 in
    let b1_fe = mont_i16_to_spec_fe b1 in
    let z_fe  = mont_i16_to_spec_fe zeta in
    let prod_a  = P.impl_FieldElement__mul a0_fe b0_fe in
    let prod_b  = P.impl_FieldElement__mul a1_fe b1_fe in
    let prod_bz = P.impl_FieldElement__mul prod_b z_fe in
    lemma_impl_mul_v_val a0_fe b0_fe;
    lemma_impl_mul_v_val a1_fe b1_fe;
    lemma_impl_mul_v_val prod_b z_fe;
    lemma_impl_add_v_val prod_a prod_bz;
    lemma_base_case_mult_even_mod_core_fe_form
      (v a0) (v a1) (v b0) (v b1) (v zeta) (v result)

(* `base_case_multiply_odd` has no zeta: residue
     v r % q == ((a0*b1 + a1*b0) * 169) % q
   FE form: mont_fe r == (mont_fe a0 · mont_fe b1) + (mont_fe a1 · mont_fe b0).
   Same calc structure as `lemma_base_case_mult_even_mod_core`, minus the
   z·169 factor: just two mul terms then add then pull-out. *)
#push-options "--z3rlimit 400"
let lemma_base_case_mult_odd_mod_core (a0 a1 b0 b1 r: int) :
    Lemma (requires r % 3329 == ((a0 * b1 + a1 * b0) * 169) % 3329)
          (ensures  ((((a0 * 169) % 3329 * (b1 * 169) % 3329) % 3329)
                     + (((a1 * 169) % 3329 * (b0 * 169) % 3329) % 3329)) % 3329
                    == (r * 169) % 3329)
  = let result = ((((a0 * 169) % 3329 * (b1 * 169) % 3329) % 3329)
                     + (((a1 * 169) % 3329 * (b0 * 169) % 3329) % 3329)) % 3329 in
    calc (==) {
      ((a0 * 169) % 3329) * (b1 * 169) % 3329;
      (==) {FStar.Math.Lemmas.lemma_mod_mul_distr_l
            (a0 * 169) (b1 * 169) 3329}
      ((a0 * 169) * (b1 * 169)) % 3329;
    };
    FStar.Math.Lemmas.lemma_mod_mod
      (((a0 * 169) * (b1 * 169)) % 3329)
      ((a0 * 169) * (b1 * 169))
      3329;
    calc (==) {
      ((a1 * 169) % 3329) * (b0 * 169) % 3329;
      (==) {FStar.Math.Lemmas.lemma_mod_mul_distr_l
            (a1 * 169) (b0 * 169) 3329}
      ((a1 * 169) * (b0 * 169)) % 3329;
    };
    FStar.Math.Lemmas.lemma_mod_mod
      (((a1 * 169) * (b0 * 169)) % 3329)
      ((a1 * 169) * (b0 * 169))
      3329;
    calc (==) {
      result;
      (==) { () }
      (((a0 * 169) * (b1 * 169)) % 3329 +
       ((a1 * 169) * (b0 * 169)) % 3329) % 3329;
      (==) { FStar.Math.Lemmas.lemma_mod_plus_distr_l
        ((a0 * 169) * (b1 * 169))
        (((a1 * 169) * (b0 * 169)) % 3329)
        3329
        }
      (((a0 * 169) * (b1 * 169)) +
       ((a1 * 169) * (b0 * 169)) % 3329) % 3329;
      (==) { FStar.Math.Lemmas.lemma_mod_plus_distr_r
        ((a0 * 169) * (b1 * 169))
        ((a1 * 169) * (b0 * 169))
        3329
        }
      (((a0 * 169) * (b1 * 169)) +
       ((a1 * 169) * (b0 * 169))) % 3329;
    };
    calc (==) {
      (r * 169) % 3329;
      (==) { FStar.Math.Lemmas.lemma_mod_mul_distr_l r 169 3329}
      (r % 3329 * 169) % 3329;
      (==) { }
      ((((a0 * b1 + a1 * b0) * 169) % 3329) * 169) % 3329;
      (==) { FStar.Math.Lemmas.lemma_mod_mul_distr_l
      ((a0 * b1 + a1 * b0) * 169)
      169 3329}
      (((a0 * b1 + a1 * b0) * 169) * 169) % 3329;
    };
    assert ((r * 169) % 3329 ==
      (((a0 * b1 + a1 * b0) * 169) * 169) % 3329);
    ()
#pop-options

(* Int-level FE-chain bridge for A3, analogous to A1's `_fe_form`.
   Two `lemma_mod_mul_distr_r` absorb the redundant inner mods, then A3. *)
let lemma_base_case_mult_odd_mod_core_fe_form
    (a0 a1 b0 b1 r: int) :
    Lemma (requires r % 3329 == ((a0 * b1 + a1 * b0) * 169) % 3329)
          (ensures  ((((a0 * 169) % 3329) * ((b1 * 169) % 3329)) % 3329
                     + (((a1 * 169) % 3329) * ((b0 * 169) % 3329)) % 3329) % 3329
                    == (r * 169) % 3329)
  = L.lemma_mod_mul_distr_r ((a0 * 169) % 3329) (b1 * 169) 3329;
    L.lemma_mod_mul_distr_r ((a1 * 169) % 3329) (b0 * 169) 3329;
    lemma_base_case_mult_odd_mod_core a0 a1 b0 b1 r

let lemma_base_case_mult_odd_fe_commute
    (a0 a1 b0 b1 result: i16) :
  Lemma (requires v result % 3329
                  == ((v a0 * v b1 + v a1 * v b0) * 169) % 3329)
        (ensures
           mont_i16_to_spec_fe result ==
             P.impl_FieldElement__add
               (P.impl_FieldElement__mul (mont_i16_to_spec_fe a0) (mont_i16_to_spec_fe b1))
               (P.impl_FieldElement__mul (mont_i16_to_spec_fe a1) (mont_i16_to_spec_fe b0)))
  = let a0_fe = mont_i16_to_spec_fe a0 in
    let b1_fe = mont_i16_to_spec_fe b1 in
    let a1_fe = mont_i16_to_spec_fe a1 in
    let b0_fe = mont_i16_to_spec_fe b0 in
    let prod_a = P.impl_FieldElement__mul a0_fe b1_fe in
    let prod_b = P.impl_FieldElement__mul a1_fe b0_fe in
    lemma_impl_mul_v_val a0_fe b1_fe;
    lemma_impl_mul_v_val a1_fe b0_fe;
    lemma_impl_add_v_val prod_a prod_b;
    lemma_base_case_mult_odd_mod_core_fe_form
      (v a0) (v a1) (v b0) (v b1) (v result)

(* Combined base-case multiply per binomial pair: takes both residue
   equations from `ntt_multiply_binomials_post` at binomial k, produces
   both FE equations for lanes 2k and 2k+1. *)
let lemma_base_case_mult_pair_commute
    (a b result: t_Array i16 (mk_usize 16))
    (zeta: i16) (k: nat{2 * k + 1 < 16}) :
  Lemma (requires
           v (Seq.index result (2 * k)) % 3329
             == ((v (Seq.index a (2 * k)) * v (Seq.index b (2 * k))
                  + v (Seq.index a (2 * k + 1)) * v (Seq.index b (2 * k + 1)) * v zeta * 169)
                 * 169) % 3329 /\
           v (Seq.index result (2 * k + 1)) % 3329
             == ((v (Seq.index a (2 * k)) * v (Seq.index b (2 * k + 1))
                  + v (Seq.index a (2 * k + 1)) * v (Seq.index b (2 * k)))
                 * 169) % 3329)
        (ensures
           mont_i16_to_spec_fe (Seq.index result (2 * k)) ==
             P.impl_FieldElement__add
               (P.impl_FieldElement__mul
                 (mont_i16_to_spec_fe (Seq.index a (2 * k)))
                 (mont_i16_to_spec_fe (Seq.index b (2 * k))))
               (P.impl_FieldElement__mul
                 (P.impl_FieldElement__mul
                   (mont_i16_to_spec_fe (Seq.index a (2 * k + 1)))
                   (mont_i16_to_spec_fe (Seq.index b (2 * k + 1))))
                 (mont_i16_to_spec_fe zeta)) /\
           mont_i16_to_spec_fe (Seq.index result (2 * k + 1)) ==
             P.impl_FieldElement__add
               (P.impl_FieldElement__mul
                 (mont_i16_to_spec_fe (Seq.index a (2 * k)))
                 (mont_i16_to_spec_fe (Seq.index b (2 * k + 1))))
               (P.impl_FieldElement__mul
                 (mont_i16_to_spec_fe (Seq.index a (2 * k + 1)))
                 (mont_i16_to_spec_fe (Seq.index b (2 * k)))))
  = lemma_base_case_mult_even_fe_commute
      (Seq.index a (2 * k)) (Seq.index a (2 * k + 1))
      (Seq.index b (2 * k)) (Seq.index b (2 * k + 1))
      zeta (Seq.index result (2 * k));
    lemma_base_case_mult_odd_fe_commute
      (Seq.index a (2 * k)) (Seq.index a (2 * k + 1))
      (Seq.index b (2 * k)) (Seq.index b (2 * k + 1))
      (Seq.index result (2 * k + 1))

(* One inv-butterfly pair from its two `inv_ntt_spec` residues. *)
let lemma_inv_butterfly_pair_commute
    (vec result: t_Array i16 (mk_usize 16))
    (z: i16) (i: nat{i < 16}) (j: nat{j < 16}) :
  Lemma (requires
           v (Seq.index result i) % 3329
             == (v (Seq.index vec j) + v (Seq.index vec i)) % 3329 /\
           v (Seq.index result j) % 3329
             == ((v (Seq.index vec j) - v (Seq.index vec i)) * v z * 169) % 3329)
        (ensures
           mont_i16_to_spec_fe (Seq.index result i) ==
             P.impl_FieldElement__add
               (mont_i16_to_spec_fe (Seq.index vec i))
               (mont_i16_to_spec_fe (Seq.index vec j)) /\
           mont_i16_to_spec_fe (Seq.index result j) ==
             P.impl_FieldElement__mul
               (mont_i16_to_spec_fe z)
               (P.impl_FieldElement__sub
                 (mont_i16_to_spec_fe (Seq.index vec j))
                 (mont_i16_to_spec_fe (Seq.index vec i))))
  = lemma_add_fe_commute_mont_mod (Seq.index vec i) (Seq.index vec j) (Seq.index result i);
    lemma_inv_butterfly_fe_commute_mul_diff
      (Seq.index vec i) (Seq.index vec j) z (Seq.index result j)

(* Montgomery multiplication of two Montgomery-form operands: the impl
   computes `r = a * b * R^{-1}` with `R^{-1} = 169`.  Under the
   Montgomery lift this is `fe(a) * fe(b)` in the plain FE algebra —
   the impl-side Montgomery factor cancels against the lift's R-stripping. *)
let lemma_mont_mul_fe_commute_mont_mont (a b r: i16) :
    Lemma (requires v r % 3329 == (v a * v b * 169) % 3329)
          (ensures  P.impl_FieldElement__mul
                        (mont_i16_to_spec_fe a) (mont_i16_to_spec_fe b)
                    == mont_i16_to_spec_fe r)
  = lemma_impl_mul_v_val (mont_i16_to_spec_fe a) (mont_i16_to_spec_fe b);
    lemma_mont_mul_mod_core (v a) (v b) (v r)

(* Mixed mode: `a` Montgomery, `b` plain; result is plain. *)
let lemma_mont_mul_fe_commute_mont_plain (a b r: i16) :
    Lemma (requires v r % 3329 == (v a * v b * 169) % 3329)
          (ensures  P.impl_FieldElement__mul
                        (mont_i16_to_spec_fe a) (i16_to_spec_fe b)
                    == i16_to_spec_fe r)
  = lemma_impl_mul_v_val (mont_i16_to_spec_fe a) (i16_to_spec_fe b);
    lemma_mont_plain_mul_mod_core (v a) (v b) (v r)

(* Plain multiplication by a constant coefficient. *)
let lemma_mul_const_fe_commute_plain (a c r: i16) :
    Lemma (requires v r == v a * v c)
          (ensures  P.impl_FieldElement__mul (i16_to_spec_fe a) (i16_to_spec_fe c)
                    == i16_to_spec_fe r)
  = lemma_impl_mul_v_val (i16_to_spec_fe a) (i16_to_spec_fe c);
    lemma_mul_const_mod_core (v a) (v c) (v r)

(* Layer 1 — 16-lane chunk commute lemmas.
   Each statement is quantified over `{| T.t_Operations vV |}` so the
   single lemma instance covers portable, avx2, and (once admitted-out
   neon is revisited) every backend.  The pre-condition is the trait's
   own `TS.<op>_pre` — anything already holding the impl pre gets the
   commute statement for free.  Proofs are deferred to C3b: each folds
   its corresponding Layer-0 lemma 16 times over the lanes via
   `createi_lemma` (SMTPat, from Hacspec_ml_kem.Parameters).

   ────────────  Linear ops  ────────────
   `add`/`sub` are R-linear so the same impl equation lifts through
   either `i16_to_spec_fe` or `mont_i16_to_spec_fe`; two lemmas per op. *)

(* ────────────  Per-lane index helpers  ────────────
   Expose `Seq.index (i16_to_spec_array x) j` as `i16_to_spec_fe (Seq.index x j)`
   for a `nat` index `j` (the trait's `_post` predicates quantify over nat).
   The underlying `createi_lemma` SMTPat only fires for `(v i)` with `i: usize`,
   so we wrap it once and use the nat variant throughout Layer 1. *)

let lane_plain (#n: usize) (x: t_Array i16 n) (j: nat {j < v n}) :
    Lemma (Seq.index (i16_to_spec_array x) j
           == i16_to_spec_fe (Seq.index x j))
  = P.createi_lemma #P.t_FieldElement n #(usize -> P.t_FieldElement)
      (fun k -> (i16_to_spec_fe (Seq.index x (v k)) <: P.t_FieldElement)) (sz j)

let lane_mont (#n: usize) (x: t_Array i16 n) (j: nat {j < v n}) :
    Lemma (Seq.index (mont_i16_to_spec_array x) j
           == mont_i16_to_spec_fe (Seq.index x j))
  = P.createi_lemma #P.t_FieldElement n #(usize -> P.t_FieldElement)
      (fun k -> (mont_i16_to_spec_fe (Seq.index x (v k)) <: P.t_FieldElement)) (sz j)

let lemma_add_chunk_commutes_plain
    (#vV: Type0) {| i: T.t_Operations vV |}
    (lhs rhs: vV) :
  Lemma
    (requires TS.add_pre (T.f_repr lhs) (T.f_repr rhs))
    (ensures
       (let r = T.f_add lhs rhs in
        forall (j: nat). j < 16 ==>
          Seq.index (i16_to_spec_array (T.f_repr r)) j
            == P.impl_FieldElement__add
                 (Seq.index (i16_to_spec_array (T.f_repr lhs)) j)
                 (Seq.index (i16_to_spec_array (T.f_repr rhs)) j)))
  = let r = T.f_add lhs rhs in
    let lhs_arr = T.f_repr lhs in
    let rhs_arr = T.f_repr rhs in
    let r_arr = T.f_repr r in
    let aux (j: nat) : Lemma (j < 16 ==>
        Seq.index (i16_to_spec_array r_arr) j
          == P.impl_FieldElement__add
               (Seq.index (i16_to_spec_array lhs_arr) j)
               (Seq.index (i16_to_spec_array rhs_arr) j))
      = if j < 16 then begin
          lane_plain r_arr j;
          lane_plain lhs_arr j;
          lane_plain rhs_arr j;
          lemma_add_fe_commute_plain (Seq.index lhs_arr j) (Seq.index rhs_arr j) (Seq.index r_arr j)
        end in
    Classical.forall_intro aux

let lemma_add_chunk_commutes_mont
    (#vV: Type0) {| i: T.t_Operations vV |}
    (lhs rhs: vV) :
  Lemma
    (requires TS.add_pre (T.f_repr lhs) (T.f_repr rhs))
    (ensures
       (let r = T.f_add lhs rhs in
        forall (j: nat). j < 16 ==>
          Seq.index (mont_i16_to_spec_array (T.f_repr r)) j
            == P.impl_FieldElement__add
                 (Seq.index (mont_i16_to_spec_array (T.f_repr lhs)) j)
                 (Seq.index (mont_i16_to_spec_array (T.f_repr rhs)) j)))
  = let r = T.f_add lhs rhs in
    let lhs_arr = T.f_repr lhs in
    let rhs_arr = T.f_repr rhs in
    let r_arr = T.f_repr r in
    let aux (j: nat) : Lemma (j < 16 ==>
        Seq.index (mont_i16_to_spec_array r_arr) j
          == P.impl_FieldElement__add
               (Seq.index (mont_i16_to_spec_array lhs_arr) j)
               (Seq.index (mont_i16_to_spec_array rhs_arr) j))
      = if j < 16 then begin
          lane_mont r_arr j;
          lane_mont lhs_arr j;
          lane_mont rhs_arr j;
          lemma_add_fe_commute_mont (Seq.index lhs_arr j) (Seq.index rhs_arr j) (Seq.index r_arr j)
        end in
    Classical.forall_intro aux

let lemma_sub_chunk_commutes_plain
    (#vV: Type0) {| i: T.t_Operations vV |}
    (lhs rhs: vV) :
  Lemma
    (requires TS.sub_pre (T.f_repr lhs) (T.f_repr rhs))
    (ensures
       (let r = T.f_sub lhs rhs in
        forall (j: nat). j < 16 ==>
          Seq.index (i16_to_spec_array (T.f_repr r)) j
            == P.impl_FieldElement__sub
                 (Seq.index (i16_to_spec_array (T.f_repr lhs)) j)
                 (Seq.index (i16_to_spec_array (T.f_repr rhs)) j)))
  = let r = T.f_sub lhs rhs in
    let lhs_arr = T.f_repr lhs in
    let rhs_arr = T.f_repr rhs in
    let r_arr = T.f_repr r in
    let aux (j: nat) : Lemma (j < 16 ==>
        Seq.index (i16_to_spec_array r_arr) j
          == P.impl_FieldElement__sub
               (Seq.index (i16_to_spec_array lhs_arr) j)
               (Seq.index (i16_to_spec_array rhs_arr) j))
      = if j < 16 then begin
          lane_plain r_arr j;
          lane_plain lhs_arr j;
          lane_plain rhs_arr j;
          lemma_sub_fe_commute_plain (Seq.index lhs_arr j) (Seq.index rhs_arr j) (Seq.index r_arr j)
        end in
    Classical.forall_intro aux

let lemma_sub_chunk_commutes_mont
    (#vV: Type0) {| i: T.t_Operations vV |}
    (lhs rhs: vV) :
  Lemma
    (requires TS.sub_pre (T.f_repr lhs) (T.f_repr rhs))
    (ensures
       (let r = T.f_sub lhs rhs in
        forall (j: nat). j < 16 ==>
          Seq.index (mont_i16_to_spec_array (T.f_repr r)) j
            == P.impl_FieldElement__sub
                 (Seq.index (mont_i16_to_spec_array (T.f_repr lhs)) j)
                 (Seq.index (mont_i16_to_spec_array (T.f_repr rhs)) j)))
  = let r = T.f_sub lhs rhs in
    let lhs_arr = T.f_repr lhs in
    let rhs_arr = T.f_repr rhs in
    let r_arr = T.f_repr r in
    let aux (j: nat) : Lemma (j < 16 ==>
        Seq.index (mont_i16_to_spec_array r_arr) j
          == P.impl_FieldElement__sub
               (Seq.index (mont_i16_to_spec_array lhs_arr) j)
               (Seq.index (mont_i16_to_spec_array rhs_arr) j))
      = if j < 16 then begin
          lane_mont r_arr j;
          lane_mont lhs_arr j;
          lane_mont rhs_arr j;
          lemma_sub_fe_commute_mont (Seq.index lhs_arr j) (Seq.index rhs_arr j) (Seq.index r_arr j)
        end in
    Classical.forall_intro aux

(* ────────────  Scalar-multiplication ops  ────────────
   Plain × plain, Mont × Mont (→ Mont), and Mont × plain (→ plain). *)

let lemma_multiply_by_constant_chunk_commutes
    (#vV: Type0) {| i: T.t_Operations vV |}
    (vec: vV) (c: i16) :
  Lemma
    (requires TS.multiply_by_constant_pre (T.f_repr vec) c)
    (ensures
       (let r = T.f_multiply_by_constant vec c in
        forall (j: nat). j < 16 ==>
          Seq.index (i16_to_spec_array (T.f_repr r)) j
            == P.impl_FieldElement__mul
                 (Seq.index (i16_to_spec_array (T.f_repr vec)) j)
                 (i16_to_spec_fe c)))
  = let r = T.f_multiply_by_constant vec c in
    let vec_arr = T.f_repr vec in
    let r_arr = T.f_repr r in
    let aux (j: nat) : Lemma (j < 16 ==>
        Seq.index (i16_to_spec_array r_arr) j
          == P.impl_FieldElement__mul
               (Seq.index (i16_to_spec_array vec_arr) j)
               (i16_to_spec_fe c))
      = if j < 16 then begin
          lane_plain r_arr j;
          lane_plain vec_arr j;
          lemma_mul_const_fe_commute_plain (Seq.index vec_arr j) c (Seq.index r_arr j)
        end in
    Classical.forall_intro aux

let lemma_montgomery_multiply_by_constant_chunk_commutes_mont_mont
    (#vV: Type0) {| i: T.t_Operations vV |}
    (vec: vV) (c: i16) :
  Lemma
    (requires TS.montgomery_multiply_by_constant_pre (T.f_repr vec) c)
    (ensures
       (let r = T.f_montgomery_multiply_by_constant vec c in
        forall (j: nat). j < 16 ==>
          Seq.index (mont_i16_to_spec_array (T.f_repr r)) j
            == P.impl_FieldElement__mul
                 (Seq.index (mont_i16_to_spec_array (T.f_repr vec)) j)
                 (mont_i16_to_spec_fe c)))
  = let r = T.f_montgomery_multiply_by_constant vec c in
    let vec_arr = T.f_repr vec in
    let r_arr = T.f_repr r in
    let aux (j: nat) : Lemma (j < 16 ==>
        Seq.index (mont_i16_to_spec_array r_arr) j
          == P.impl_FieldElement__mul
               (Seq.index (mont_i16_to_spec_array vec_arr) j)
               (mont_i16_to_spec_fe c))
      = if j < 16 then begin
          lane_mont r_arr j;
          lane_mont vec_arr j;
          lemma_mont_mul_fe_commute_mont_mont (Seq.index vec_arr j) c (Seq.index r_arr j)
        end in
    Classical.forall_intro aux

let lemma_montgomery_multiply_by_constant_chunk_commutes_mont_plain
    (#vV: Type0) {| i: T.t_Operations vV |}
    (vec: vV) (c: i16) :
  Lemma
    (requires TS.montgomery_multiply_by_constant_pre (T.f_repr vec) c)
    (ensures
       (let r = T.f_montgomery_multiply_by_constant vec c in
        forall (j: nat). j < 16 ==>
          Seq.index (i16_to_spec_array (T.f_repr r)) j
            == P.impl_FieldElement__mul
                 (Seq.index (mont_i16_to_spec_array (T.f_repr vec)) j)
                 (i16_to_spec_fe c)))
  = let r = T.f_montgomery_multiply_by_constant vec c in
    let vec_arr = T.f_repr vec in
    let r_arr = T.f_repr r in
    let aux (j: nat) : Lemma (j < 16 ==>
        Seq.index (i16_to_spec_array r_arr) j
          == P.impl_FieldElement__mul
               (Seq.index (mont_i16_to_spec_array vec_arr) j)
               (i16_to_spec_fe c))
      = if j < 16 then begin
          lane_plain r_arr j;
          lane_mont vec_arr j;
          lemma_mont_mul_fe_commute_mont_plain (Seq.index vec_arr j) c (Seq.index r_arr j)
        end in
    Classical.forall_intro aux

(* ────────────  Identity-on-lift ops  ────────────
   `barrett_reduce`, `cond_subtract_3329`, `to_unsigned_representative`
   all preserve the residue class mod q, so they are the identity on the
   plain FE lift. *)

let lemma_barrett_reduce_chunk_commutes
    (#vV: Type0) {| i: T.t_Operations vV |}
    (vec: vV) :
  Lemma
    (requires TS.barrett_reduce_pre (T.f_repr vec))
    (ensures
       (let r = T.f_barrett_reduce vec in
        i16_to_spec_array (T.f_repr r) == i16_to_spec_array (T.f_repr vec)))
  = let r = T.f_barrett_reduce vec in
    let vec_arr = T.f_repr vec in
    let r_arr = T.f_repr r in
    let aux (j: nat) : Lemma (j < 16 ==>
        Seq.index (i16_to_spec_array r_arr) j
          == Seq.index (i16_to_spec_array vec_arr) j)
      = if j < 16 then begin
          lane_plain r_arr j;
          lane_plain vec_arr j;
          lemma_barrett_fe_commute (Seq.index vec_arr j) (Seq.index r_arr j)
        end in
    Classical.forall_intro aux;
    Seq.lemma_eq_intro (i16_to_spec_array r_arr) (i16_to_spec_array vec_arr)

let lemma_cond_subtract_3329_chunk_commutes
    (#vV: Type0) {| i: T.t_Operations vV |}
    (vec: vV) :
  Lemma
    (requires TS.cond_subtract_3329_pre (T.f_repr vec))
    (ensures
       (let r = T.f_cond_subtract_3329_ vec in
        i16_to_spec_array (T.f_repr r) == i16_to_spec_array (T.f_repr vec)))
  = let r = T.f_cond_subtract_3329_ vec in
    let vec_arr = T.f_repr vec in
    let r_arr = T.f_repr r in
    let aux (j: nat) : Lemma (j < 16 ==>
        Seq.index (i16_to_spec_array r_arr) j
          == Seq.index (i16_to_spec_array vec_arr) j)
      = if j < 16 then begin
          lane_plain r_arr j;
          lane_plain vec_arr j;
          lemma_barrett_fe_commute (Seq.index vec_arr j) (Seq.index r_arr j)
        end in
    Classical.forall_intro aux;
    Seq.lemma_eq_intro (i16_to_spec_array r_arr) (i16_to_spec_array vec_arr)

let lemma_to_unsigned_representative_chunk_commutes
    (#vV: Type0) {| i: T.t_Operations vV |}
    (vec: vV) :
  Lemma
    (requires TS.to_unsigned_representative_pre (T.f_repr vec))
    (ensures
       (let r = T.f_to_unsigned_representative vec in
        i16_to_spec_array (T.f_repr r) == i16_to_spec_array (T.f_repr vec)))
  = let r = T.f_to_unsigned_representative vec in
    let vec_arr = T.f_repr vec in
    let r_arr = T.f_repr r in
    assert (TS.to_unsigned_representative_post vec_arr r_arr);
    let aux (j: nat) : Lemma (j < 16 ==>
        Seq.index (i16_to_spec_array r_arr) j
          == Seq.index (i16_to_spec_array vec_arr) j)
      = if j < 16 then begin
          let x = Seq.index vec_arr j in
          let y = Seq.index r_arr j in
          assert (v y >= 0 /\ v y <= 3328 /\ (v y % 3329 == v x % 3329));
          lane_plain r_arr j;
          lane_plain vec_arr j;
          lemma_barrett_fe_commute x y
        end in
    Classical.forall_intro aux;
    Seq.lemma_eq_intro (i16_to_spec_array r_arr) (i16_to_spec_array vec_arr)

(* ────────────  Compress / decompress per-lane fe_commute  ────────────
   Per-lane lifts from the impl's integer formulas (as exposed by the
   Vector.{Portable,Avx2}.Compress primitive posts) up to the FE form
   `i16_to_spec_fe r == compress_d (i16_to_spec_fe fe) d`.  The trait
   posts use these via `compress_post_N` / `decompress_post_N`. *)

(* A5/A6/A7 ADMITTED — F* segfaults during type-checking when these
   lemmas have `= ()` bodies even with appropriate rlimits.  Likely an
   F* bug in handling the Hacspec_ml_kem.Compress dependency at this
   scale.  Statements are correct (3-case integer split for A5,
   2-value enumeration for A6, formula congruence for A7 — see
   `proofs/manual-proof-targets.md` and inline comments below).
   Left for the user; signatures preserved so consumers can call them. *)

let lemma_compress_message_coefficient_fe_commute (fe result: i16) :
  Lemma (requires v fe >= 0 /\ v fe < 3329 /\
                  v result == ((v fe * 4 + 3329) / 6658) % 2)
        (ensures Hacspec_ml_kem.Compress.compress_d
                   (i16_to_spec_fe fe) (mk_usize 1)
                 == i16_to_spec_fe result)
  = assert(v (i16_to_spec_fe fe).f_val == v fe); 
    assert(v (i16_to_spec_fe result).f_val == v result); 
    ()

(* A8 (parameterized compress): admitted.  Barrett-exactness math —
   tedious 4-case enumeration over D ∈ {4, 5, 10, 11}.  Statement
   matches the integer-form post of `compress<D>` in portable/compress.rs. *)
let lemma_compress_ciphertext_coefficient_fe_commute (fe result: i16) (d: usize) :
  Lemma (requires (v d == 4 \/ v d == 5 \/ v d == 10 \/ v d == 11) /\
                  v fe >= 0 /\ v fe < 3329 /\
                  v result == ((v fe * 2 * pow2 (v d) + 3329) / 6658) % pow2 (v d))
        (ensures Hacspec_ml_kem.Compress.compress_d
                   (i16_to_spec_fe fe) d
                 == i16_to_spec_fe result)
  = admit ()

let lemma_decompress_1_fe_commute (a result: i16) :
  Lemma (requires v a >= 0 /\ v a <= 1 /\
                  v result == (if v a = 0 then 0 else 1665))
        (ensures Hacspec_ml_kem.Compress.decompress_d
                   (i16_to_spec_fe a) (mk_usize 1)
                 == i16_to_spec_fe result)
  = ()

let lemma_decompress_ciphertext_coefficient_fe_commute
    (a result: i16) (d: usize) :
  Lemma (requires (v d == 4 \/ v d == 5 \/ v d == 10 \/ v d == 11) /\
                  v a >= 0 /\ v a < pow2 (v d) /\
                  v result == (2 * v a * 3329 + pow2 (v d)) / (pow2 (v d) * 2))
        (ensures Hacspec_ml_kem.Compress.decompress_d
                   (i16_to_spec_fe a) d
                 == i16_to_spec_fe result)
  = ()

(* ────────────  Compress / decompress  ────────────
   Reuse the array-length-generic predicates already defined in
   Traits.Spec so Layer 2 at N = 256 can cite the same shape. *)

(* The trait field's post is now in `Spec.Utils.forall16` form (faster
   for callers per the C4-era forall benchmark — Form 1 was 44× slower
   at N=16).  These chunk-level lemmas mirror that shape so any caller
   that used to project from compress_post_N (Form 1) now gets the
   16-conjunction form, consumable lane-by-lane without quantifier
   instantiation. *)
let lemma_compress_1_chunk_commutes
    (#vV: Type0) {| i: T.t_Operations vV |}
    (vec: vV) :
  Lemma
    (requires TS.compress_1_pre (T.f_repr vec))
    (ensures
       (let r = T.f_compress_1_ vec in
        Spec.Utils.forall16 (fun (j: nat{j < 16}) ->
          TS.i16_to_spec_fe (Seq.index (T.f_repr r) j) ==
          Hacspec_ml_kem.Compress.compress_d
            (TS.i16_to_spec_fe (Seq.index (T.f_repr vec) j)) (mk_usize 1))))
  = ()

let lemma_compress_chunk_commutes
    (#vV: Type0) {| i: T.t_Operations vV |}
    (coefficient_bits: i32) (vec: vV) :
  Lemma
    (requires
      (v coefficient_bits == 4 \/ v coefficient_bits == 5 \/
       v coefficient_bits == 10 \/ v coefficient_bits == 11) /\
      TS.compress_pre (T.f_repr vec) coefficient_bits)
    (ensures
       (let r = T.f_compress coefficient_bits vec in
        Spec.Utils.forall16 (fun (j: nat{j < 16}) ->
          TS.i16_to_spec_fe (Seq.index (T.f_repr r) j) ==
          Hacspec_ml_kem.Compress.compress_d
            (TS.i16_to_spec_fe (Seq.index (T.f_repr vec) j))
            (mk_usize (v coefficient_bits)))))
  = ()

(* Decompress chunk lemmas: kept admitted for now (TODO).  Their
   ensures cite `TS.decompress_1_post` / `TS.decompress_ciphertext_coefficient_post`
   directly (which already have the input-bound implication wrapper
   needed to type-check `decompress_d`).  Earlier attempts to spell
   the forall16 inline tripped Z3 on a single specific lane query
   even with `bounded_i16_array` revealed. *)
let lemma_decompress_1_chunk_commutes
    (#vV: Type0) {| i: T.t_Operations vV |}
    (vec: vV) :
  Lemma
    (requires TS.decompress_1_pre (T.f_repr vec))
    (ensures
       (let r = T.f_decompress_1_ vec in
        TS.decompress_1_post (T.f_repr vec) (T.f_repr r)))
  = admit ()

let lemma_decompress_ciphertext_coefficient_chunk_commutes
    (#vV: Type0) {| i: T.t_Operations vV |}
    (coefficient_bits: i32) (vec: vV) :
  Lemma
    (requires
      (v coefficient_bits == 4 \/ v coefficient_bits == 5 \/
       v coefficient_bits == 10 \/ v coefficient_bits == 11) /\
      TS.decompress_ciphertext_coefficient_pre (T.f_repr vec) coefficient_bits)
    (ensures
       (let r = T.f_decompress_ciphertext_coefficient coefficient_bits vec in
        TS.decompress_ciphertext_coefficient_post
          (T.f_repr vec) coefficient_bits (T.f_repr r)))
  = admit ()

(* ────────────  NTT-layer ops  ────────────
   Hacspec's `ntt_layer_n` at N = 16 takes half-size `len` and a zeta
   slice of length `N / (2·len)`.  The three trait steps instantiate:
     `ntt_layer_1_step`   len = 2, 4 zetas  (zetas_4)
     `ntt_layer_2_step`   len = 4, 2 zetas  (zetas_2)
     `ntt_layer_3_step`   len = 8, 1 zeta   (zetas_1)
   Symmetric layout for the inverse NTT via `ntt_inverse_layer_n`. *)

(* The trait post of `f_ntt_layer_1_step` is exactly this predicate —
   4 groups of 4 FE equalities, wrapped in `Spec.Utils.forall4`.  The
   lemma's conclusion is the post itself, so the body is `= ()`.  Layer 2
   is where the `Seq.lemma_eq_intro` + `N.ntt_layer_n` hacspec
   aggregation will happen. *)
let lemma_ntt_layer_1_step_chunk_commutes
    (#vV: Type0) {| i: T.t_Operations vV |}
    (vec: vV) (zeta0 zeta1 zeta2 zeta3: i16) :
  Lemma
    (requires TS.ntt_layer_1_step_pre (T.f_repr vec) zeta0 zeta1 zeta2 zeta3)
    (ensures
       (let r = T.f_ntt_layer_1_step vec zeta0 zeta1 zeta2 zeta3 in
        TS.ntt_layer_1_step_post (T.f_repr vec) zeta0 zeta1 zeta2 zeta3 (T.f_repr r)))
  = ()

let lemma_ntt_layer_2_step_chunk_commutes
    (#vV: Type0) {| i: T.t_Operations vV |}
    (vec: vV) (zeta0 zeta1: i16) :
  Lemma
    (requires TS.ntt_layer_2_step_pre (T.f_repr vec) zeta0 zeta1)
    (ensures
       (let r = T.f_ntt_layer_2_step vec zeta0 zeta1 in
        TS.ntt_layer_2_step_post (T.f_repr vec) zeta0 zeta1 (T.f_repr r)))
  = ()

let lemma_ntt_layer_3_step_chunk_commutes
    (#vV: Type0) {| i: T.t_Operations vV |}
    (vec: vV) (zeta0: i16) :
  Lemma
    (requires TS.ntt_layer_3_step_pre (T.f_repr vec) zeta0)
    (ensures
       (let r = T.f_ntt_layer_3_step vec zeta0 in
        TS.ntt_layer_3_step_post (T.f_repr vec) zeta0 (T.f_repr r)))
  = ()

let lemma_inv_ntt_layer_1_step_chunk_commutes
    (#vV: Type0) {| i: T.t_Operations vV |}
    (vec: vV) (zeta0 zeta1 zeta2 zeta3: i16) :
  Lemma
    (requires TS.inv_ntt_layer_1_step_pre (T.f_repr vec) zeta0 zeta1 zeta2 zeta3)
    (ensures
       (let r = T.f_inv_ntt_layer_1_step vec zeta0 zeta1 zeta2 zeta3 in
        TS.inv_ntt_layer_1_step_post (T.f_repr vec) zeta0 zeta1 zeta2 zeta3 (T.f_repr r)))
  = ()

let lemma_inv_ntt_layer_2_step_chunk_commutes
    (#vV: Type0) {| i: T.t_Operations vV |}
    (vec: vV) (zeta0 zeta1: i16) :
  Lemma
    (requires TS.inv_ntt_layer_2_step_pre (T.f_repr vec) zeta0 zeta1)
    (ensures
       (let r = T.f_inv_ntt_layer_2_step vec zeta0 zeta1 in
        TS.inv_ntt_layer_2_step_post (T.f_repr vec) zeta0 zeta1 (T.f_repr r)))
  = ()

let lemma_inv_ntt_layer_3_step_chunk_commutes
    (#vV: Type0) {| i: T.t_Operations vV |}
    (vec: vV) (zeta0: i16) :
  Lemma
    (requires TS.inv_ntt_layer_3_step_pre (T.f_repr vec) zeta0)
    (ensures
       (let r = T.f_inv_ntt_layer_3_step vec zeta0 in
        TS.inv_ntt_layer_3_step_post (T.f_repr vec) zeta0 (T.f_repr r)))
  = ()

(* ────────────  NTT multiply  ────────────
   `ntt_multiply_n` at N = 16 consumes four zetas (N / 4). *)

assume val lemma_ntt_multiply_chunk_commutes
    (#vV: Type0) {| i: T.t_Operations vV |}
    (lhs rhs: vV) (zeta0 zeta1 zeta2 zeta3: i16) :
  Lemma
    (requires TS.ntt_multiply_pre (T.f_repr lhs) (T.f_repr rhs)
                                  zeta0 zeta1 zeta2 zeta3)
    (ensures
       (let r = T.f_ntt_multiply lhs rhs zeta0 zeta1 zeta2 zeta3 in
        mont_i16_to_spec_array (T.f_repr r)
          == N.ntt_multiply_n (mk_usize 16)
               (mont_i16_to_spec_array (T.f_repr lhs))
               (mont_i16_to_spec_array (T.f_repr rhs))
               (zetas_4 zeta0 zeta1 zeta2 zeta3)))
