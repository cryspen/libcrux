module Hacspec_ml_kem.Commute.Bridges
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open FStar.Mul
open Core_models
open Libcrux_ml_kem.Vector.Traits.Spec
open Hacspec_ml_kem.Commute.Chunk

(* Function-form per-vector hacspec bridges (the slow ones — Z3 queries
   take multi-minutes on first verification without hint replay) for
   the trait's NTT/INTT step methods.  These lift the trait branch
   posts (per-lane FE equations under `mont_i16_to_spec_fe`) to a
   single per-vector function-form equation
       `mont_i16_to_spec_array(out) ==
         <hacspec_layer_fn> (mont_i16_to_spec_array(in)) ...`.

   Split out from `Hacspec_ml_kem.Commute.Chunk` to isolate the slow
   queries: editing this file does not invalidate Chunk.fst.checked.
   Helpers (`mont_array_lane`, `zetas_4_lane`,
   `lemma_ntt_layer_n_16_2_lane`, `lemma_ntt_inverse_layer_n_16_2_lane`)
   live in Chunk because Polynomial.fst/Invert_ntt.fst's proofs depend
   on those axioms transitively.

   Future layer 2/3 and layer-4_plus per-vector function-form bridges
   go in this file, NOT in Chunk.fst. *)

module P  = Hacspec_ml_kem.Parameters
module T  = Libcrux_ml_kem.Vector.Traits
module TS = Libcrux_ml_kem.Vector.Traits.Spec
module N  = Hacspec_ml_kem.Ntt
module IN = Hacspec_ml_kem.Invert_ntt

(*** Phase 7a (track A) — Inverse spec function unfold helper ***)

(* Per-lane unfold for `IN.ntt_inverse_layer_n (mk_usize 16) p (mk_usize 2) zs`
   at concrete lane `i ∈ [0, 16)`.  Mirror of `lemma_ntt_layer_n_16_2_lane`
   (in Chunk.fst) for the inverse direction.  Defined here in Bridges.fst
   (NOT in Chunk.fst) so that introducing it to the codebase doesn't
   change Polynomial.fst's transitive SMT context (which would regress
   `add_to_ring_element` Q60 with "incomplete quantifiers"). *)
#push-options "--z3rlimit 200 --fuel 0 --ifuel 1"
let lemma_ntt_inverse_layer_n_16_2_lane
    (p: t_Array P.t_FieldElement (mk_usize 16))
    (zs: t_Array P.t_FieldElement (mk_usize 4))
    (i: nat {i < 16}) :
    Lemma
      (let result = IN.ntt_inverse_layer_n (mk_usize 16) p (mk_usize 2)
                                            (Rust_primitives.unsize zs) in
       let group : nat = i / 4 in
       let idx   : nat = i % 4 in
       (idx < 2 ==>
         i + 2 < 16 /\
         Seq.index result i ==
           (IN.inv_butterfly (Seq.index zs group)
                              (Seq.index p i)
                              (Seq.index p (i + 2)))._1) /\
       (idx >= 2 ==>
         i >= 2 /\
         Seq.index result i ==
           (IN.inv_butterfly (Seq.index zs group)
                              (Seq.index p (i - 2))
                              (Seq.index p i))._2))
  = let result = IN.ntt_inverse_layer_n (mk_usize 16) p (mk_usize 2)
                                         (Rust_primitives.unsize zs) in
    P.createi_lemma #P.t_FieldElement (mk_usize 16)
      #(usize -> P.t_FieldElement)
      (fun (j: usize { j <. mk_usize 16 }) ->
        let group:usize = j /! (mk_usize 2 *! mk_usize 2 <: usize) in
        let idx:usize = j %! (mk_usize 2 *! mk_usize 2 <: usize) in
        (if idx <. mk_usize 2 then
          (IN.inv_butterfly (Seq.index zs (v group))
                             (Seq.index p (v j))
                             (Seq.index p (v j + 2)))._1
        else
          (IN.inv_butterfly (Seq.index zs (v group))
                             (Seq.index p (v j - 2))
                             (Seq.index p (v j)))._2)
        <: P.t_FieldElement)
      (sz i)
#pop-options

(*** Phase 7b — Forward NTT layer 1 hacspec bridge ***)

#push-options "--z3rlimit 400 --fuel 0 --ifuel 1"

(* Per-lane bridge for `f_ntt_layer_1_step`: produces the per-lane FE
   equation `out_fe.[i] == rhs.[i]` from the trait branch post and the
   `lemma_ntt_layer_n_16_2_lane` unfold helper.

   Key idea: lane `i ∈ [0, 16)` belongs to branch `b = i / 4`, position
   `idx = i % 4` within the branch.  The trait branch post exposes 4
   FE equalities at lanes `(4b, 4b+1, 4b+2, 4b+3)`.  The hacspec lane
   `i` matches:
     - if idx < 2 (lanes 4b or 4b+1): `result[i] = vec[i] + z*vec[i+2]`
       (first FE eq for `i = 4b`, third for `i = 4b+1`)
     - if idx >= 2 (lanes 4b+2 or 4b+3): `result[i] = vec[i-2] - z*vec[i]`
       (second FE eq for `i = 4b+2`, fourth for `i = 4b+3`)
   The N.butterfly._{1,2} structurally matches the branch post's
   add/sub by virtue of `mont_i16_to_spec_fe`'s linearity. *)
private
let lemma_ntt_layer_1_step_lane_bridge
    (in_arr out_arr: t_Array i16 (mk_usize 16))
    (zeta0 zeta1 zeta2 zeta3: i16)
    (i: nat {i < 16}) :
  Lemma
    (requires
      TS.ntt_layer_1_step_post in_arr zeta0 zeta1 zeta2 zeta3 out_arr)
    (ensures
      (let zs = zetas_4 zeta0 zeta1 zeta2 zeta3 in
       let p_fe = mont_i16_to_spec_array in_arr in
       let r_fe = mont_i16_to_spec_array out_arr in
       let rhs = N.ntt_layer_n (mk_usize 16) p_fe (mk_usize 2)
                               (Rust_primitives.unsize zs) in
       Seq.index r_fe i == Seq.index rhs i))
  = let zs = zetas_4 zeta0 zeta1 zeta2 zeta3 in
    let p_fe = mont_i16_to_spec_array in_arr in
    let r_fe = mont_i16_to_spec_array out_arr in
    (* Branch b = i / 4 ∈ {0,1,2,3}; reveal post for that branch. *)
    let b : nat = i / 4 in
    assert (b < 4);
    assert (Spec.Utils.forall4 (fun (bb: nat{bb < 4}) ->
              TS.ntt_layer_1_step_branch_post bb in_arr zeta0 zeta1 zeta2 zeta3 out_arr));
    assert (TS.ntt_layer_1_step_branch_post b in_arr zeta0 zeta1 zeta2 zeta3 out_arr);
    reveal_opaque (`%TS.ntt_layer_1_step_branch_post)
                  (TS.ntt_layer_1_step_branch_post b in_arr zeta0 zeta1 zeta2 zeta3 out_arr);
    (* Now we have, for the right z (zeta0..3 picked by b), 4 FE equalities
       at lanes (4b, 4b+2, 4b+1, 4b+3). *)
    lemma_ntt_layer_n_16_2_lane p_fe zs i;
    zetas_4_lane zeta0 zeta1 zeta2 zeta3 (sz b);
    (* Unfold per-array index helpers — these provide
       `(mont_i16_to_spec_array x).[i] == mont_i16_to_spec_fe x.[i]`. *)
    mont_array_lane out_arr (sz i);
    mont_array_lane in_arr (sz i);
    let idx : nat = i % 4 in
    if idx < 2 then begin
      assert (i + 2 < 16);
      mont_array_lane in_arr (sz (i + 2))
    end else begin
      assert (i >= 2);
      mont_array_lane in_arr (sz (i - 2))
    end

#pop-options

#push-options "--z3rlimit 400 --fuel 0 --ifuel 1"

(* Per-vector hacspec bridge for `f_ntt_layer_1_step`.

   Composes the 16 per-lane bridges via `Classical.forall_intro` +
   `Seq.lemma_eq_intro`. *)
let lemma_ntt_layer_1_step_to_hacspec
    (#vV: Type0) {| i: T.t_Operations vV |}
    (vec: vV) (zeta0 zeta1 zeta2 zeta3: i16) :
  Lemma
    (requires TS.ntt_layer_1_step_pre (T.f_repr vec) zeta0 zeta1 zeta2 zeta3)
    (ensures
       (let r = T.f_ntt_layer_1_step vec zeta0 zeta1 zeta2 zeta3 in
        mont_i16_to_spec_array (T.f_repr r) ==
          N.ntt_layer_n (mk_usize 16)
            (mont_i16_to_spec_array (T.f_repr vec))
            (mk_usize 2)
            (Rust_primitives.unsize (zetas_4 zeta0 zeta1 zeta2 zeta3))))
  = let r = T.f_ntt_layer_1_step vec zeta0 zeta1 zeta2 zeta3 in
    let in_arr = T.f_repr vec in
    let out_arr = T.f_repr r in
    let zs = zetas_4 zeta0 zeta1 zeta2 zeta3 in
    let p_fe = mont_i16_to_spec_array in_arr in
    let r_fe = mont_i16_to_spec_array out_arr in
    let rhs = N.ntt_layer_n (mk_usize 16) p_fe (mk_usize 2)
                            (Rust_primitives.unsize zs) in
    assert (TS.ntt_layer_1_step_post in_arr zeta0 zeta1 zeta2 zeta3 out_arr);
    let aux (j: nat) : Lemma (j < 16 ==> Seq.index r_fe j == Seq.index rhs j)
      = if j < 16 then
          lemma_ntt_layer_1_step_lane_bridge in_arr out_arr
            zeta0 zeta1 zeta2 zeta3 j
    in
    Classical.forall_intro aux;
    Seq.lemma_eq_intro r_fe rhs

#pop-options

(*** Phase 7a (track A) — Inverse NTT layer 1 hacspec bridge ***)

#push-options "--z3rlimit 400 --fuel 0 --ifuel 1"

(* Per-lane bridge for `f_inv_ntt_layer_1_step`: produces the per-lane FE
   equation `out_fe.[i] == rhs.[i]` from the trait branch post and the
   `lemma_ntt_inverse_layer_n_16_2_lane` unfold helper.

   Mirror of `lemma_ntt_layer_1_step_lane_bridge` for the inverse
   direction.  Lane `i ∈ [0, 16)` belongs to branch `b = i / 4`,
   position `idx = i % 4`.  Trait branch post exposes 4 FE equalities
   at lanes `(4b, 4b+1, 4b+2, 4b+3)`.  The hacspec lane `i` matches:
     - if idx < 2 (lanes 4b or 4b+1): `result[i] = vec[i] + vec[i+2]`
       (SUM — matches `inv_butterfly._1` at `(i, i+2)`)
     - if idx ≥ 2 (lanes 4b+2 or 4b+3): `result[i] = z·(vec[i] − vec[i−2])`
       (MUL — matches `inv_butterfly._2` at `(i−2, i)`).
   `IN.inv_butterfly._{1,2}` structurally matches the branch post's
   `add`/`mul-of-sub` by virtue of `mont_i16_to_spec_fe`'s linearity. *)
private
let lemma_inv_ntt_layer_1_step_lane_bridge
    (in_arr out_arr: t_Array i16 (mk_usize 16))
    (zeta0 zeta1 zeta2 zeta3: i16)
    (i: nat {i < 16}) :
  Lemma
    (requires
      TS.inv_ntt_layer_1_step_post in_arr zeta0 zeta1 zeta2 zeta3 out_arr)
    (ensures
      (let zs = zetas_4 zeta0 zeta1 zeta2 zeta3 in
       let p_fe = mont_i16_to_spec_array in_arr in
       let r_fe = mont_i16_to_spec_array out_arr in
       let rhs = IN.ntt_inverse_layer_n (mk_usize 16) p_fe (mk_usize 2)
                                         (Rust_primitives.unsize zs) in
       Seq.index r_fe i == Seq.index rhs i))
  = let zs = zetas_4 zeta0 zeta1 zeta2 zeta3 in
    let p_fe = mont_i16_to_spec_array in_arr in
    let r_fe = mont_i16_to_spec_array out_arr in
    let b : nat = i / 4 in
    assert (b < 4);
    assert (Spec.Utils.forall4 (fun (bb: nat{bb < 4}) ->
              TS.inv_ntt_layer_1_step_branch_post bb in_arr zeta0 zeta1 zeta2 zeta3 out_arr));
    assert (TS.inv_ntt_layer_1_step_branch_post b in_arr zeta0 zeta1 zeta2 zeta3 out_arr);
    reveal_opaque (`%TS.inv_ntt_layer_1_step_branch_post)
                  (TS.inv_ntt_layer_1_step_branch_post b in_arr zeta0 zeta1 zeta2 zeta3 out_arr);
    lemma_ntt_inverse_layer_n_16_2_lane p_fe zs i;
    zetas_4_lane zeta0 zeta1 zeta2 zeta3 (sz b);
    mont_array_lane out_arr (sz i);
    mont_array_lane in_arr (sz i);
    let idx : nat = i % 4 in
    if idx < 2 then begin
      assert (i + 2 < 16);
      mont_array_lane in_arr (sz (i + 2))
    end else begin
      assert (i >= 2);
      mont_array_lane in_arr (sz (i - 2))
    end

#pop-options

#push-options "--z3rlimit 400 --fuel 0 --ifuel 1"

(* Per-vector hacspec bridge for `f_inv_ntt_layer_1_step`.

   Mirror of `lemma_ntt_layer_1_step_to_hacspec`.  Composes the 16
   per-lane bridges via `Classical.forall_intro` + `Seq.lemma_eq_intro`.

   This is the function-form layer commute: the Mont-lifted output of
   one in-vector layer-1 inverse-NTT step equals
   `IN.ntt_inverse_layer_n` applied to the Mont-lifted input.  Caller
   chains 16 of these (one per chunk) to lift to a poly-level equation
   for `invert_ntt_at_layer_1`'s post (Step 4 of the Phase 7a plan). *)
let lemma_inv_ntt_layer_1_step_to_hacspec
    (#vV: Type0) {| i: T.t_Operations vV |}
    (vec: vV) (zeta0 zeta1 zeta2 zeta3: i16) :
  Lemma
    (requires TS.inv_ntt_layer_1_step_pre (T.f_repr vec) zeta0 zeta1 zeta2 zeta3)
    (ensures
       (let r = T.f_inv_ntt_layer_1_step vec zeta0 zeta1 zeta2 zeta3 in
        mont_i16_to_spec_array (T.f_repr r) ==
          IN.ntt_inverse_layer_n (mk_usize 16)
            (mont_i16_to_spec_array (T.f_repr vec))
            (mk_usize 2)
            (Rust_primitives.unsize (zetas_4 zeta0 zeta1 zeta2 zeta3))))
  = let r = T.f_inv_ntt_layer_1_step vec zeta0 zeta1 zeta2 zeta3 in
    let in_arr = T.f_repr vec in
    let out_arr = T.f_repr r in
    let zs = zetas_4 zeta0 zeta1 zeta2 zeta3 in
    let p_fe = mont_i16_to_spec_array in_arr in
    let r_fe = mont_i16_to_spec_array out_arr in
    let rhs = IN.ntt_inverse_layer_n (mk_usize 16) p_fe (mk_usize 2)
                                       (Rust_primitives.unsize zs) in
    assert (TS.inv_ntt_layer_1_step_post in_arr zeta0 zeta1 zeta2 zeta3 out_arr);
    let aux (j: nat) : Lemma (j < 16 ==> Seq.index r_fe j == Seq.index rhs j)
      = if j < 16 then
          lemma_inv_ntt_layer_1_step_lane_bridge in_arr out_arr
            zeta0 zeta1 zeta2 zeta3 j
    in
    Classical.forall_intro aux;
    Seq.lemma_eq_intro r_fe rhs

#pop-options

(* ───── Layer 2 / 3 forward NTT bridges and (layers 2/3) inverse NTT bridges ─────
   STATUS: layer 1 inverse-NTT bridge is done above (track A, Phase 7a).
   Layer 2/3 forward and inverse remain.  Same pattern as
   `lemma_ntt_layer_1_step_to_hacspec`: each layer needs a per-lane
   bridge revealing the right branch post for `b = lane → branch` and
   matching against the trait branch post's per-lane FE equations,
   plus a `Classical.forall_intro` + `Seq.lemma_eq_intro` per-vector
   composition.

   First-cut implementation of layer 2 forward (lanes-to-branches
   mapping `b = (i / 8) * 2 + ((i % 4) / 2)`) ran Z3 past 2.7 minutes
   on a single sub-query — case-splits on the layer-2 branch post's
   nested `if`-ladder for `base`/`off`/`z`.  Mitigation: explicitly
   enumerate `i ∈ {0..15}` to remove the symbolic `b = ...`. *)
