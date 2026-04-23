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
assume val lemma_add_fe_commute_plain (a b r: i16) :
    Lemma (requires v r == v a + v b)
          (ensures  P.impl_FieldElement__add (i16_to_spec_fe a) (i16_to_spec_fe b)
                    == i16_to_spec_fe r)

assume val lemma_add_fe_commute_mont (a b r: i16) :
    Lemma (requires v r == v a + v b)
          (ensures  P.impl_FieldElement__add
                        (mont_i16_to_spec_fe a) (mont_i16_to_spec_fe b)
                    == mont_i16_to_spec_fe r)

assume val lemma_sub_fe_commute_plain (a b r: i16) :
    Lemma (requires v r == v a - v b)
          (ensures  P.impl_FieldElement__sub (i16_to_spec_fe a) (i16_to_spec_fe b)
                    == i16_to_spec_fe r)

assume val lemma_sub_fe_commute_mont (a b r: i16) :
    Lemma (requires v r == v a - v b)
          (ensures  P.impl_FieldElement__sub
                        (mont_i16_to_spec_fe a) (mont_i16_to_spec_fe b)
                    == mont_i16_to_spec_fe r)

(* Barrett reduction preserves value mod q, i.e. is identity under the
   plain lift. *)
assume val lemma_barrett_fe_commute (a r: i16) :
    Lemma (requires v r % 3329 == v a % 3329)
          (ensures  i16_to_spec_fe r == i16_to_spec_fe a)

(* Montgomery multiplication of two Montgomery-form operands: the impl
   computes `r = a * b * R^{-1}` with `R^{-1} = 169`.  Under the
   Montgomery lift this is `fe(a) * fe(b)` in the plain FE algebra —
   the impl-side Montgomery factor cancels against the lift's R-stripping. *)
assume val lemma_mont_mul_fe_commute_mont_mont (a b r: i16) :
    Lemma (requires v r % 3329 == (v a * v b * 169) % 3329)
          (ensures  P.impl_FieldElement__mul
                        (mont_i16_to_spec_fe a) (mont_i16_to_spec_fe b)
                    == mont_i16_to_spec_fe r)

(* Mixed mode: `a` Montgomery, `b` plain; result is plain. *)
assume val lemma_mont_mul_fe_commute_mont_plain (a b r: i16) :
    Lemma (requires v r % 3329 == (v a * v b * 169) % 3329)
          (ensures  P.impl_FieldElement__mul
                        (mont_i16_to_spec_fe a) (i16_to_spec_fe b)
                    == i16_to_spec_fe r)

(* Plain multiplication by a constant coefficient. *)
assume val lemma_mul_const_fe_commute_plain (a c r: i16) :
    Lemma (requires v r == v a * v c)
          (ensures  P.impl_FieldElement__mul (i16_to_spec_fe a) (i16_to_spec_fe c)
                    == i16_to_spec_fe r)

(* Zeta cancellation: the impl stores zetas pre-multiplied by R, so
   `mont_i16_to_spec_fe zeta_mont` recovers the plain abstract zeta.
   Provable by `assert_norm` over the 128-entry ZETAS table, since
   hacspec's `ZETAS_TIMES_MONTGOMERY_R = ZETAS` (identity in the spec). *)
assume val lemma_mont_zeta_cancel (zeta_mont zeta_plain: i16) :
    Lemma (requires (v zeta_mont * 169) % 3329 == v zeta_plain % 3329)
          (ensures  mont_i16_to_spec_fe zeta_mont == i16_to_spec_fe zeta_plain)

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
