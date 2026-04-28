module Hacspec_ml_kem.Commute.Bridges
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open FStar.Mul
open Core_models
open Libcrux_ml_kem.Vector.Traits.Spec

(* Function-form per-vector hacspec bridges for the trait's NTT/INTT
   step methods.  These lift the trait branch posts (per-lane FE
   equations under `mont_i16_to_spec_fe`) to a single per-vector
   function-form equation `mont_i16_to_spec_array(out) ==
   <hacspec_layer_fn> (mont_i16_to_spec_array(in)) ...`.

   Split out from `Hacspec_ml_kem.Commute.Chunk` to isolate the slow
   Z3 queries (no hint replay yet for the lane bridges → multi-minute
   Z3 search per query on first verification).  Future layer 2/3 and
   layer-4_plus bridges go in this file, NOT in Chunk.fst, to keep
   Chunk.fst's verification fast on each iteration. *)

module P  = Hacspec_ml_kem.Parameters
module T  = Libcrux_ml_kem.Vector.Traits
module TS = Libcrux_ml_kem.Vector.Traits.Spec
module N  = Hacspec_ml_kem.Ntt
module IN = Hacspec_ml_kem.Invert_ntt

(*** Phase 7b — Forward NTT layer commute (target #1: ntt_at_layer_1) ***)

(* Per-lane unfold helper for `mont_i16_to_spec_array`.  Wraps
   `createi_lemma` to surface the per-lane FE for an i16 array. *)
let mont_array_lane (#n: usize)
    (x: t_Array i16 n) (i: usize { v i < v n }) :
    Lemma (Seq.index (mont_i16_to_spec_array x) (v i)
           == mont_i16_to_spec_fe (Seq.index x (v i)))
  = P.createi_lemma #P.t_FieldElement n
      #(usize -> P.t_FieldElement)
      (fun (j: usize { j <. n }) ->
        (mont_i16_to_spec_fe (Seq.index x (v j)) <: P.t_FieldElement))
      i

(* Per-lane unfold helper for `zetas_4`. *)
let zetas_4_lane (z0 z1 z2 z3: i16) (i: usize { v i < 4 }) :
    Lemma (Seq.index (zetas_4 z0 z1 z2 z3) (v i)
           == (if v i = 0 then mont_i16_to_spec_fe z0
               else if v i = 1 then mont_i16_to_spec_fe z1
               else if v i = 2 then mont_i16_to_spec_fe z2
               else mont_i16_to_spec_fe z3))
  = P.createi_lemma #P.t_FieldElement (mk_usize 4)
      #(usize -> P.t_FieldElement)
      (fun (j: usize { j <. mk_usize 4 }) ->
        (if v j = 0 then mont_i16_to_spec_fe z0
         else if v j = 1 then mont_i16_to_spec_fe z1
         else if v j = 2 then mont_i16_to_spec_fe z2
         else mont_i16_to_spec_fe z3) <: P.t_FieldElement)
      i

#push-options "--z3rlimit 200 --fuel 0 --ifuel 1"

(* Per-lane unfold for `N.ntt_layer_n (mk_usize 16) p (mk_usize 2) zs`
   at concrete lane `i ∈ [0, 16)`.  Computes the body of the createi at
   index `i`: `group = i / 4`, `idx = i % 4`, then either
   `butterfly._1` (if idx < 2: lanes i, i+2) or `_2` (else: lanes i-2, i).

   Surfaces the result at lane `i` as a concrete `butterfly` expression
   so per-lane matching against the trait branch post is reducible. *)
let lemma_ntt_layer_n_16_2_lane
    (p: t_Array P.t_FieldElement (mk_usize 16))
    (zs: t_Array P.t_FieldElement (mk_usize 4))
    (i: nat {i < 16}) :
    Lemma
      (let result = N.ntt_layer_n (mk_usize 16) p (mk_usize 2)
                                  (Rust_primitives.unsize zs) in
       let group : nat = i / 4 in
       let idx   : nat = i % 4 in
       (idx < 2 ==>
         i + 2 < 16 /\
         Seq.index result i ==
           (N.butterfly (Seq.index zs group)
                        (Seq.index p i)
                        (Seq.index p (i + 2)))._1) /\
       (idx >= 2 ==>
         i >= 2 /\
         Seq.index result i ==
           (N.butterfly (Seq.index zs group)
                        (Seq.index p (i - 2))
                        (Seq.index p i))._2))
  = let result = N.ntt_layer_n (mk_usize 16) p (mk_usize 2)
                                (Rust_primitives.unsize zs) in
    P.createi_lemma #P.t_FieldElement (mk_usize 16)
      #(usize -> P.t_FieldElement)
      (fun (j: usize { j <. mk_usize 16 }) ->
        let group:usize = j /! (mk_usize 2 *! mk_usize 2 <: usize) in
        let idx:usize = j %! (mk_usize 2 *! mk_usize 2 <: usize) in
        (if idx <. mk_usize 2 then
          (N.butterfly (Seq.index zs (v group))
                       (Seq.index p (v j))
                       (Seq.index p (v j + 2)))._1
        else
          (N.butterfly (Seq.index zs (v group))
                       (Seq.index p (v j - 2))
                       (Seq.index p (v j)))._2)
        <: P.t_FieldElement)
      (sz i)

#pop-options

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

#push-options "--z3rlimit 200 --fuel 0 --ifuel 1"

(* Per-lane unfold for `IN.ntt_inverse_layer_n (mk_usize 16) p (mk_usize 2) zs`
   at concrete lane `i ∈ [0, 16)`.  Mirror of `lemma_ntt_layer_n_16_2_lane`
   for the inverse direction.  Computes the body of the createi at index
   `i`: `group = i / 4`, `idx = i % 4`, then either
     - `inv_butterfly._1` (if idx < 2: SUM lanes i, i+2 ↦ `p[i] + p[i+2]`)
     - `inv_butterfly._2` (else:   MUL lanes i-2, i ↦ `z·(p[i] − p[i−2])`).

   Surfaces the result at lane `i` as a concrete `inv_butterfly`
   expression so per-lane matching against the trait branch post is
   reducible. *)
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
   Layer 2/3 forward and inverse remain.

   Same pattern as `lemma_ntt_layer_1_step_to_hacspec` above; each layer
   needs a `lemma_ntt_layer_n_16_<2*len>_lane` createi unfold, a
   `zetas_<groups>_lane` zetas unfold, a per-lane bridge that reveals
   the right branch post for `b = lane → branch` and matches against
   the trait branch post's per-lane FE equations, and a top-level
   `Classical.forall_intro` + `Seq.lemma_eq_intro` composition.

   First-cut implementation of layer 2 forward (lanes-to-branches
   mapping `b = (i / 8) * 2 + ((i % 4) / 2)`) verified the per-lane
   unfold and zetas helpers, but the lane bridge itself ran Z3 past
   2.7 minutes on a single sub-query without reaching any failure or
   success — likely because Z3 was case-splitting heavily on the
   layer-2 branch post's nested `if`-ladder for `base`/`off`/`z`.

   Recommended approach for follow-up:
     (a) Profile via `--query_stats --split_queries always` to identify
         which sub-query stalls;
     (b) Either explicitly enumerate `i ∈ {0..15}` to remove the
         nested arithmetic in `b = ...`, OR
     (c) Restructure the trait branch post so `b` is consumed by a
         flat case-split (no nested ifs).

   Inverse NTT layers (`f_inv_ntt_layer_{2,3}_step`) follow the same
   pattern with `IN.inv_butterfly` and `IN.ntt_inverse_layer_n` in
   place of the forward equivalents. *)
