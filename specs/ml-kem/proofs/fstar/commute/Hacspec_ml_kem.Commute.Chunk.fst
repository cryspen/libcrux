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

module P = Hacspec_ml_kem.Parameters
module L = FStar.Math.Lemmas

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
   These state the trait-level commutativity in terms of hacspec
   operations over the lifted arrays.  Each lemma is quantified over
   `{| t_Operations vV |}` so portable, avx2 share a single statement.

   Deferred to C3: populate with signatures below. *)

(* TODO(C3): add the ~13 chunk-level lemmas matching the mode table:
     lemma_add_chunk_commutes               (either lift)
     lemma_sub_chunk_commutes               (either)
     lemma_mul_const_chunk_commutes         (plain)
     lemma_mont_mul_const_chunk_mont_mont
     lemma_mont_mul_const_chunk_mont_plain
     lemma_barrett_chunk_commutes           (plain)
     lemma_cond_subtract_chunk_commutes
     lemma_to_unsigned_representative_commutes
     lemma_compress_chunk_commutes
     lemma_decompress_chunk_commutes
     lemma_ntt_layer_{1,2,3}_chunk_commutes
     lemma_inv_ntt_layer_{1,2,3}_chunk_commutes
     lemma_ntt_multiply_chunk_commutes *)
