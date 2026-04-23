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

assume val lemma_add_chunk_commutes_plain
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

assume val lemma_add_chunk_commutes_mont
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

assume val lemma_sub_chunk_commutes_plain
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

assume val lemma_sub_chunk_commutes_mont
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

(* ────────────  Scalar-multiplication ops  ────────────
   Plain × plain, Mont × Mont (→ Mont), and Mont × plain (→ plain). *)

assume val lemma_multiply_by_constant_chunk_commutes
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

assume val lemma_montgomery_multiply_by_constant_chunk_commutes_mont_mont
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

assume val lemma_montgomery_multiply_by_constant_chunk_commutes_mont_plain
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

(* ────────────  Identity-on-lift ops  ────────────
   `barrett_reduce`, `cond_subtract_3329`, `to_unsigned_representative`
   all preserve the residue class mod q, so they are the identity on the
   plain FE lift. *)

assume val lemma_barrett_reduce_chunk_commutes
    (#vV: Type0) {| i: T.t_Operations vV |}
    (vec: vV) :
  Lemma
    (requires TS.barrett_reduce_pre (T.f_repr vec))
    (ensures
       (let r = T.f_barrett_reduce vec in
        i16_to_spec_array (T.f_repr r) == i16_to_spec_array (T.f_repr vec)))

assume val lemma_cond_subtract_3329_chunk_commutes
    (#vV: Type0) {| i: T.t_Operations vV |}
    (vec: vV) :
  Lemma
    (requires TS.cond_subtract_3329_pre (T.f_repr vec))
    (ensures
       (let r = T.f_cond_subtract_3329_ vec in
        i16_to_spec_array (T.f_repr r) == i16_to_spec_array (T.f_repr vec)))

assume val lemma_to_unsigned_representative_chunk_commutes
    (#vV: Type0) {| i: T.t_Operations vV |}
    (vec: vV) :
  Lemma
    (requires TS.to_unsigned_representative_pre (T.f_repr vec))
    (ensures
       (let r = T.f_to_unsigned_representative vec in
        i16_to_spec_array (T.f_repr r) == i16_to_spec_array (T.f_repr vec)))

(* ────────────  Compress / decompress  ────────────
   Reuse the array-length-generic predicates already defined in
   Traits.Spec so Layer 2 at N = 256 can cite the same shape. *)

assume val lemma_compress_1_chunk_commutes
    (#vV: Type0) {| i: T.t_Operations vV |}
    (vec: vV) :
  Lemma
    (requires TS.compress_1_pre (T.f_repr vec))
    (ensures
       (let r = T.f_compress_1_ vec in
        TS.compress_post_N #(mk_usize 16) (mk_usize 1) (T.f_repr vec) (T.f_repr r)))

assume val lemma_compress_chunk_commutes
    (#vV: Type0) {| i: T.t_Operations vV |}
    (coefficient_bits: i32) (vec: vV) :
  Lemma
    (requires
      (v coefficient_bits == 4 \/ v coefficient_bits == 5 \/
       v coefficient_bits == 10 \/ v coefficient_bits == 11) /\
      TS.compress_pre (T.f_repr vec) coefficient_bits)
    (ensures
       (let r = T.f_compress coefficient_bits vec in
        TS.compress_post_N #(mk_usize 16) (mk_usize (v coefficient_bits))
          (T.f_repr vec) (T.f_repr r)))

assume val lemma_decompress_1_chunk_commutes
    (#vV: Type0) {| i: T.t_Operations vV |}
    (vec: vV) :
  Lemma
    (requires TS.decompress_1_pre (T.f_repr vec))
    (ensures
       (let r = T.f_decompress_1_ vec in
        TS.decompress_post_N #(mk_usize 16) (mk_usize 1) (T.f_repr vec) (T.f_repr r)))

assume val lemma_decompress_ciphertext_coefficient_chunk_commutes
    (#vV: Type0) {| i: T.t_Operations vV |}
    (coefficient_bits: i32) (vec: vV) :
  Lemma
    (requires
      (v coefficient_bits == 4 \/ v coefficient_bits == 5 \/
       v coefficient_bits == 10 \/ v coefficient_bits == 11) /\
      TS.decompress_ciphertext_coefficient_pre (T.f_repr vec) coefficient_bits)
    (ensures
       (let r = T.f_decompress_ciphertext_coefficient coefficient_bits vec in
        TS.decompress_post_N #(mk_usize 16) (mk_usize (v coefficient_bits))
          (T.f_repr vec) (T.f_repr r)))

(* ────────────  NTT-layer ops  ────────────
   Hacspec's `ntt_layer_n` at N = 16 takes half-size `len` and a zeta
   slice of length `N / (2·len)`.  The three trait steps instantiate:
     `ntt_layer_1_step`   len = 2, 4 zetas  (zetas_4)
     `ntt_layer_2_step`   len = 4, 2 zetas  (zetas_2)
     `ntt_layer_3_step`   len = 8, 1 zeta   (zetas_1)
   Symmetric layout for the inverse NTT via `ntt_inverse_layer_n`. *)

assume val lemma_ntt_layer_1_step_chunk_commutes
    (#vV: Type0) {| i: T.t_Operations vV |}
    (vec: vV) (zeta0 zeta1 zeta2 zeta3: i16) :
  Lemma
    (requires TS.ntt_layer_1_step_pre (T.f_repr vec) zeta0 zeta1 zeta2 zeta3)
    (ensures
       (let r = T.f_ntt_layer_1_step vec zeta0 zeta1 zeta2 zeta3 in
        mont_i16_to_spec_array (T.f_repr r)
          == N.ntt_layer_n (mk_usize 16)
               (mont_i16_to_spec_array (T.f_repr vec))
               (mk_usize 2)
               (zetas_4 zeta0 zeta1 zeta2 zeta3)))

assume val lemma_ntt_layer_2_step_chunk_commutes
    (#vV: Type0) {| i: T.t_Operations vV |}
    (vec: vV) (zeta0 zeta1: i16) :
  Lemma
    (requires TS.ntt_layer_2_step_pre (T.f_repr vec) zeta0 zeta1)
    (ensures
       (let r = T.f_ntt_layer_2_step vec zeta0 zeta1 in
        mont_i16_to_spec_array (T.f_repr r)
          == N.ntt_layer_n (mk_usize 16)
               (mont_i16_to_spec_array (T.f_repr vec))
               (mk_usize 4)
               (zetas_2 zeta0 zeta1)))

assume val lemma_ntt_layer_3_step_chunk_commutes
    (#vV: Type0) {| i: T.t_Operations vV |}
    (vec: vV) (zeta0: i16) :
  Lemma
    (requires TS.ntt_layer_3_step_pre (T.f_repr vec) zeta0)
    (ensures
       (let r = T.f_ntt_layer_3_step vec zeta0 in
        mont_i16_to_spec_array (T.f_repr r)
          == N.ntt_layer_n (mk_usize 16)
               (mont_i16_to_spec_array (T.f_repr vec))
               (mk_usize 8)
               (zetas_1 zeta0)))

assume val lemma_inv_ntt_layer_1_step_chunk_commutes
    (#vV: Type0) {| i: T.t_Operations vV |}
    (vec: vV) (zeta0 zeta1 zeta2 zeta3: i16) :
  Lemma
    (requires TS.inv_ntt_layer_1_step_pre (T.f_repr vec) zeta0 zeta1 zeta2 zeta3)
    (ensures
       (let r = T.f_inv_ntt_layer_1_step vec zeta0 zeta1 zeta2 zeta3 in
        mont_i16_to_spec_array (T.f_repr r)
          == IN.ntt_inverse_layer_n (mk_usize 16)
               (mont_i16_to_spec_array (T.f_repr vec))
               (mk_usize 2)
               (zetas_4 zeta0 zeta1 zeta2 zeta3)))

assume val lemma_inv_ntt_layer_2_step_chunk_commutes
    (#vV: Type0) {| i: T.t_Operations vV |}
    (vec: vV) (zeta0 zeta1: i16) :
  Lemma
    (requires TS.inv_ntt_layer_2_step_pre (T.f_repr vec) zeta0 zeta1)
    (ensures
       (let r = T.f_inv_ntt_layer_2_step vec zeta0 zeta1 in
        mont_i16_to_spec_array (T.f_repr r)
          == IN.ntt_inverse_layer_n (mk_usize 16)
               (mont_i16_to_spec_array (T.f_repr vec))
               (mk_usize 4)
               (zetas_2 zeta0 zeta1)))

assume val lemma_inv_ntt_layer_3_step_chunk_commutes
    (#vV: Type0) {| i: T.t_Operations vV |}
    (vec: vV) (zeta0: i16) :
  Lemma
    (requires TS.inv_ntt_layer_3_step_pre (T.f_repr vec) zeta0)
    (ensures
       (let r = T.f_inv_ntt_layer_3_step vec zeta0 in
        mont_i16_to_spec_array (T.f_repr r)
          == IN.ntt_inverse_layer_n (mk_usize 16)
               (mont_i16_to_spec_array (T.f_repr vec))
               (mk_usize 8)
               (zetas_1 zeta0)))

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
