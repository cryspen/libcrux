module Libcrux_ml_dsa.Arithmetic_theory
#set-options "--fuel 0 --ifuel 1 --z3rlimit 80"
open FStar.Mul
open Core_models

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_ml_dsa.Polynomial in
  let open Libcrux_ml_dsa.Simd.Traits in
  ()

(* ---------------------------------------------------------------------------
   Relocated from `src/arithmetic.rs` `fstar::before` blocks (annotation
   compaction).  BLOCK 1: `is_lane_range_poly_range` opaque predicate family
   (used by `decompose_vector`).  BLOCK 2: `make_hint` functional-correctness
   theory stack.  Consumers (`Arithmetic.fst`) `open` this module.
   --------------------------------------------------------------------------- *)

[@@ "opaque_to_smt"]
let is_lane_range_poly_range
      (#v_SIMDUnit: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (lo hi start fin: usize)
      (arr: t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
    : prop =
  forall (k: nat). v start <= k /\ k < v fin /\ k < Seq.length arr ==>
    Libcrux_ml_dsa.Polynomial.Spec.is_lane_range_poly lo hi (Seq.index arr k)

let lemma_is_lane_range_poly_range_lookup
      (#v_SIMDUnit: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (lo hi start fin: usize)
      (arr: t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
      (k: nat)
    : Lemma
      (requires is_lane_range_poly_range lo hi start fin arr /\
                v start <= k /\ k < v fin /\ k < Seq.length arr)
      (ensures Libcrux_ml_dsa.Polynomial.Spec.is_lane_range_poly lo hi (Seq.index arr k))
      [SMTPat (is_lane_range_poly_range lo hi start fin arr); SMTPat (Seq.index arr k)]
  = reveal_opaque (`%is_lane_range_poly_range) (is_lane_range_poly_range lo hi start fin arr)

let lemma_is_lane_range_poly_range_intro
      (#v_SIMDUnit: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (lo hi start fin: usize)
      (arr: t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
    : Lemma
      (requires forall (k: nat). v start <= k /\ k < v fin /\ k < Seq.length arr ==>
        Libcrux_ml_dsa.Polynomial.Spec.is_lane_range_poly lo hi (Seq.index arr k))
      (ensures is_lane_range_poly_range lo hi start fin arr)
  = reveal_opaque (`%is_lane_range_poly_range) (is_lane_range_poly_range lo hi start fin arr)

let lemma_is_lane_range_poly_range_extend_after_update
      (#v_SIMDUnit: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (lo hi: usize) (i: usize)
      (arr_old arr_new: t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
    : Lemma
      (requires
        Seq.length arr_new == Seq.length arr_old /\ v i < Seq.length arr_new /\
        is_lane_range_poly_range lo hi (mk_usize 0) i arr_old /\
        (forall (k:nat). k < Seq.length arr_new /\ k <> v i ==>
          Seq.index arr_new k == Seq.index arr_old k) /\
        Libcrux_ml_dsa.Polynomial.Spec.is_lane_range_poly lo hi (Seq.index arr_new (v i)))
      (ensures is_lane_range_poly_range lo hi (mk_usize 0) (i +! mk_usize 1) arr_new)
  = let aux (k: nat{k < v i + 1 /\ k < Seq.length arr_new}) :
      Lemma (Libcrux_ml_dsa.Polynomial.Spec.is_lane_range_poly lo hi (Seq.index arr_new k)) =
      if k < v i then begin
        lemma_is_lane_range_poly_range_lookup lo hi (mk_usize 0) i arr_old k;
        assert (Seq.index arr_new k == Seq.index arr_old k)
      end else assert (k == v i)
    in
    Classical.forall_intro aux;
    lemma_is_lane_range_poly_range_intro lo hi (mk_usize 0) (i +! mk_usize 1) arr_new

(* ============================================================================
   make_hint functional correctness (step 4): specification + lemma stack.

   GOAL: v true_hints == count_total_ones hint, GUARDED by `high_all_nonneg`
   (every lane of every SIMD unit of every row of `high` lies in [0, q)). The
   guard is the decompose>=0 last-mile, discharged later in sign_internal.
   ============================================================================ *)

(* Guard predicate: every lane of every unit of every row of `high` is in
   [0, q).  Matches the per-call antecedent of the trait's guarded count post
   (`f_compute_hint_post`, Traits.fst:263-266).  Opaque so it stays an atom in
   make_hint's body; the maintenance lemmas reveal it. *)
[@@ "opaque_to_smt"]
let high_all_nonneg
      (#v_SIMDUnit: Type0)
      (i0: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (high: t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
    : prop =
  forall (r: nat) (u: nat) (lane: nat).
    (r < Seq.length high /\
      u < Seq.length (Seq.index high r).Libcrux_ml_dsa.Polynomial.f_simd_units /\ lane < 8) ==>
    (let a =
        i0._super_i2.f_repr
          (Seq.index (Seq.index high r).Libcrux_ml_dsa.Polynomial.f_simd_units u)
      in
      v (Seq.index a lane) >= 0 /\ v (Seq.index a lane) < 8380417)

(* Bridge: decompose_vector's `is_lane_range_poly_slice 0 8380416` post
   (asymmetric [0, q) lane range on the HighBits output) implies make_hint's
   `high_all_nonneg` guard.  Consumed at the make_hint call site in
   sign_internal to discharge the count-correctness post. *)
let lemma_lane_range_slice_high_all_nonneg
      (#v_SIMDUnit: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (high: t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
    : Lemma
      (requires Libcrux_ml_dsa.Polynomial.Spec.is_lane_range_poly_slice
                  (mk_usize 0) (mk_usize 8380416) high)
      (ensures high_all_nonneg i0 high)
  = reveal_opaque (`%high_all_nonneg) (high_all_nonneg i0 high);
    introduce forall (r: nat) (u: nat) (lane: nat).
      (r < Seq.length high /\
       u < Seq.length (Seq.index high r).Libcrux_ml_dsa.Polynomial.f_simd_units /\ lane < 8) ==>
      (let a =
          i0._super_i2.f_repr
            (Seq.index (Seq.index high r).Libcrux_ml_dsa.Polynomial.f_simd_units u)
        in
        v (Seq.index a lane) >= 0 /\ v (Seq.index a lane) < 8380417)
    with introduce _ ==> _
    with _pf.
      (Libcrux_ml_dsa.Polynomial.Spec.lemma_is_lane_range_poly_slice_lookup
         (mk_usize 0) (mk_usize 8380416) high r;
       Libcrux_ml_dsa.Polynomial.Spec.lemma_is_lane_range_poly_lookup
         (mk_usize 0) (mk_usize 8380416) (Seq.index high r) u lane)

#push-options "--fuel 1 --ifuel 1 --z3rlimit 100"

(* compute_hint as an explicit 8-lane sum (generic restatement of
   Simd.Avx2.Arithmetic.lemma_compute_hint_8). *)
let lemma_compute_hint_8 (arr: t_Array i32 (mk_usize 8))
    : Lemma
      (ensures
        Spec.MLDSA.Math.compute_hint arr ==
        v (cast (arr.[ mk_usize 0 ] <: i32) <: usize) +
        v (cast (arr.[ mk_usize 1 ] <: i32) <: usize) +
        v (cast (arr.[ mk_usize 2 ] <: i32) <: usize) +
        v (cast (arr.[ mk_usize 3 ] <: i32) <: usize) +
        v (cast (arr.[ mk_usize 4 ] <: i32) <: usize) +
        v (cast (arr.[ mk_usize 5 ] <: i32) <: usize) +
        v (cast (arr.[ mk_usize 6 ] <: i32) <: usize) +
        v (cast (arr.[ mk_usize 7 ] <: i32) <: usize)) =
  Spec.Utils.eq_repeati0 (mk_usize 8) (Spec.MLDSA.Math.hint_counter arr) 0;
  Spec.Utils.unfold_repeati (mk_usize 8) (Spec.MLDSA.Math.hint_counter arr) 0 (mk_usize 0);
  Spec.Utils.unfold_repeati (mk_usize 8) (Spec.MLDSA.Math.hint_counter arr) 0 (mk_usize 1);
  Spec.Utils.unfold_repeati (mk_usize 8) (Spec.MLDSA.Math.hint_counter arr) 0 (mk_usize 2);
  Spec.Utils.unfold_repeati (mk_usize 8) (Spec.MLDSA.Math.hint_counter arr) 0 (mk_usize 3);
  Spec.Utils.unfold_repeati (mk_usize 8) (Spec.MLDSA.Math.hint_counter arr) 0 (mk_usize 4);
  Spec.Utils.unfold_repeati (mk_usize 8) (Spec.MLDSA.Math.hint_counter arr) 0 (mk_usize 5);
  Spec.Utils.unfold_repeati (mk_usize 8) (Spec.MLDSA.Math.hint_counter arr) 0 (mk_usize 6);
  Spec.Utils.unfold_repeati (mk_usize 8) (Spec.MLDSA.Math.hint_counter arr) 0 (mk_usize 7)

(* Sum of per-unit hint counts over the first `j` SIMD units of `units`.
   Total over unrestricted `nat` (clamped) so the fold invariants carry no
   well-formedness side-condition; only called with `j <= Seq.length units`. *)
let rec sum_unit_hints
      (#v_SIMDUnit: Type0)
      (i0: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (units: t_Slice v_SIMDUnit)
      (j: nat)
    : Tot nat (decreases j) =
  if j = 0 || j > Seq.length units then 0
  else
    sum_unit_hints i0 units (j - 1) +
    Spec.MLDSA.Math.compute_hint
      (i0._super_i2.f_repr (Seq.index units (j - 1)))

(* Sum of per-row one-counts over the first `i` rows of `hint`.  Total over
   unrestricted `nat` (clamped); only called with `i <= Seq.length hint`. *)
let rec sum_rows (hint: t_Slice (t_Array i32 (mk_usize 256))) (i: nat)
    : Tot nat (decreases i) =
  if i = 0 || i > Seq.length hint then 0
  else
    sum_rows hint (i - 1) +
    Libcrux_ml_dsa.Encoding.Signature.count_row_ones (Seq.index hint (i - 1)) 256

(* Base cases, exposed via SMTPat so the fold init invariants (i=0, j=0)
   discharge at fuel 0 without unfolding the recursive sums elsewhere. *)
let lemma_sum_rows_zero (hint: t_Slice (t_Array i32 (mk_usize 256)))
    : Lemma (ensures sum_rows hint 0 == 0) [SMTPat (sum_rows hint 0)] = ()

let lemma_sum_unit_hints_zero
      (#v_SIMDUnit: Type0)
      (i0: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (units: t_Slice v_SIMDUnit)
    : Lemma (ensures sum_unit_hints i0 units 0 == 0) [SMTPat (sum_unit_hints i0 units 0)] = ()

(* ---- L2 machinery: hax `fold_range` -> nat-fold bridge (inlined from
   `Proof_Utils.NatFold` in the sha3 equivalence tree, which is NOT on ml-dsa's
   include path — each body is a trivial fuel-1 recursion).  The bridge passes
   the loop-body equality as a Lemma VALUE (`pointwise`), sidestepping the hax
   closure inequality that blocks a named-step re-induction of
   impl_2__to_i32_array's INLINE fold. ---- *)

(* Nat-indexed fold mirroring `Rust_primitives.Hax.Folds.fold_range` over
   [start,end_), with explicit iteration counter `i`. *)
let rec fold_range_nat
      (#acc_t: Type0)
      (start end_: nat)
      (i: nat{start <= i /\ i <= end_})
      (acc: acc_t)
      (f: acc_t -> (j: nat{start <= j /\ j < end_}) -> acc_t)
    : Tot acc_t (decreases end_ - i) =
  if i < end_ then fold_range_nat start end_ (i + 1) (f acc i) f else acc

(* Bridge: refined `fold_range i end_ inv acc f` equals
   `fold_range_nat (v start) (v end_) (v i) acc g` whenever `f` and `g` agree
   pointwise.  The `pointwise` argument is a Lemma supplied at the call site —
   not a forall-hypothesis — so no closure equality is ever asked of Z3. *)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 200"
let rec lemma_fold_range_is_range_nat
      (#acc_t: Type0) (#u: Rust_primitives.Integers.uinttype)
      (start end_: Rust_primitives.Integers.int_t u)
      (i: Rust_primitives.Integers.int_t u {v start <= v i /\ v i <= v end_})
      (inv:
          acc_t ->
          (j: Rust_primitives.Integers.int_t u
              {Rust_primitives.Hax.Folds.fold_range_wf_index i end_ false (v j)}) ->
          Type0)
      (acc: acc_t {~(Rust_primitives.Hax.Folds.range_empty i end_) ==> inv acc i})
      (f:
          (a: acc_t ->
           j:
             Rust_primitives.Integers.int_t u
               { v j <= v end_ /\ Rust_primitives.Hax.Folds.fold_range_wf_index i end_ true (v j) /\
                 inv a j } ->
           a': acc_t {inv a' (Rust_primitives.Integers.mk_int (v j + 1))}))
      (g: acc_t -> (j: nat{v start <= j /\ j < v end_}) -> acc_t)
      (pointwise:
          (a: acc_t) ->
          (j:
              Rust_primitives.Integers.int_t u
                { v j <= v end_ /\ Rust_primitives.Hax.Folds.fold_range_wf_index i end_ true (v j) /\
                  inv a j }) ->
          Lemma (f a j == g a (v j)))
    : Lemma
      (ensures
        Rust_primitives.Hax.Folds.fold_range i end_ inv acc f ==
        fold_range_nat (v start) (v end_) (v i) acc g)
      (decreases v end_ - v i) =
  if v i < v end_
  then
    (pointwise acc i;
      lemma_fold_range_is_range_nat start end_ (i +! Rust_primitives.Integers.mk_int 1) inv (f acc i) f
        g (fun a j -> pointwise a j))
  else ()
#pop-options

(* Nat-indexed loop body mirroring impl_2__to_i32_array's INLINE fold body:
   write block `j` (8 coefficients) via `update_at_range`. *)
let to_i32_nat_body
      (#v_SIMDUnit: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (units: t_Slice v_SIMDUnit {Seq.length units == 32})
      (result: t_Array i32 (mk_usize 256))
      (j: nat{0 <= j /\ j < 32})
    : t_Array i32 (mk_usize 256) =
  Rust_primitives.Hax.Monomorphized_update_at.update_at_range result
    ({
        Core_models.Ops.Range.f_start
        =
        mk_usize j *! Libcrux_ml_dsa.Simd.Traits.v_COEFFICIENTS_IN_SIMD_UNIT <: usize;
        Core_models.Ops.Range.f_end
        =
        (mk_usize j +! mk_usize 1 <: usize) *! Libcrux_ml_dsa.Simd.Traits.v_COEFFICIENTS_IN_SIMD_UNIT
        <:
        usize
      }
      <:
      Core_models.Ops.Range.t_Range usize)
    (Libcrux_ml_dsa.Simd.Traits.f_to_coefficient_array #v_SIMDUnit
        #FStar.Tactics.Typeclasses.solve
        (units.[ mk_usize j ] <: v_SIMDUnit)
        (result.[ ({
              Core_models.Ops.Range.f_start
              =
              mk_usize j *! Libcrux_ml_dsa.Simd.Traits.v_COEFFICIENTS_IN_SIMD_UNIT <: usize;
              Core_models.Ops.Range.f_end
              =
              (mk_usize j +! mk_usize 1 <: usize) *!
              Libcrux_ml_dsa.Simd.Traits.v_COEFFICIENTS_IN_SIMD_UNIT
              <:
              usize
            }
            <:
            Core_models.Ops.Range.t_Range usize) ]
          <:
          t_Slice i32)
      <:
      t_Slice i32)

(* Closure-FREE recursion equivalent to `fold_range_nat 0 32 start acc
   (to_i32_nat_body i0 units)`.  The `fold_range_nat ... (to_i32_nat_body i0
   units)` form carries the partial application `to_i32_nat_body i0 units` as a
   closure argument; Z3 cannot type that closure well enough to run the
   `Seq.index` congruence in the consumer (qi.profile: `typing_Tm_abs_*` stall,
   "incomplete quantifiers").  Phrasing the lemma posts over `to_i32_rec` (a
   plain recursive application, no closure) keeps the consumer's facts clean. *)
let rec to_i32_rec
      (#v_SIMDUnit: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (units: t_Slice v_SIMDUnit {Seq.length units == 32})
      (start: nat{start <= 32})
      (acc: t_Array i32 (mk_usize 256))
    : Tot (t_Array i32 (mk_usize 256)) (decreases 32 - start) =
  if start < 32
  then to_i32_rec #v_SIMDUnit #i0 units (start + 1) (to_i32_nat_body #v_SIMDUnit #i0 units acc start)
  else acc

(* `fold_range_nat 0 32 start acc (to_i32_nat_body i0 units)` == the closure-free
   `to_i32_rec i0 units start acc` (both recurse identically). *)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 100"
let rec lemma_foldnat_eq_rec
      (#v_SIMDUnit: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (units: t_Slice v_SIMDUnit {Seq.length units == 32})
      (start: nat{start <= 32})
      (acc: t_Array i32 (mk_usize 256))
    : Lemma
      (ensures
        fold_range_nat 0 32 start acc (to_i32_nat_body #v_SIMDUnit #i0 units) ==
        to_i32_rec #v_SIMDUnit #i0 units start acc)
      (decreases 32 - start) =
  if start < 32
  then lemma_foldnat_eq_rec #v_SIMDUnit #i0 units (start + 1) (to_i32_nat_body #v_SIMDUnit #i0 units acc start)
  else ()
#pop-options

(* (A) The extracted impl_2__to_i32_array's refined fold_range equals the
   closure-free `to_i32_rec` recursion (via the nat-fold bridge + eq_rec).
   Bridge applied with the SAME inline lambdas the extractor produces — F*
   matches them syntactically, so the only proof obligation is the pointwise
   `()`. *)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 200"
let lemma_to_i32_array_is_fold_nat
      (#v_SIMDUnit: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (p: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
    : Lemma
      (requires Seq.length p.Libcrux_ml_dsa.Polynomial.f_simd_units == 32)
      (ensures
        Libcrux_ml_dsa.Polynomial.impl_2__to_i32_array #v_SIMDUnit p ==
        to_i32_rec #v_SIMDUnit #i0 p.Libcrux_ml_dsa.Polynomial.f_simd_units 0
          (Rust_primitives.Hax.repeat (mk_i32 0) (mk_usize 256))) =
  assert (Core_models.Slice.impl__len #v_SIMDUnit
            (p.Libcrux_ml_dsa.Polynomial.f_simd_units <: t_Slice v_SIMDUnit) ==
          mk_usize 32);
  lemma_fold_range_is_range_nat #(t_Array i32 (mk_usize 256)) #Rust_primitives.Integers.USIZE
    (mk_usize 0)
    (Core_models.Slice.impl__len #v_SIMDUnit
        (p.Libcrux_ml_dsa.Polynomial.f_simd_units <: t_Slice v_SIMDUnit)
      <:
      usize)
    (mk_usize 0)
    (fun result temp_1_ ->
        let result:t_Array i32 (mk_usize 256) = result in
        let _:usize = temp_1_ in
        true)
    (Rust_primitives.Hax.repeat (mk_i32 0) (mk_usize 256))
    (fun result i ->
        let result:t_Array i32 (mk_usize 256) = result in
        let i:usize = i in
        Rust_primitives.Hax.Monomorphized_update_at.update_at_range result
          ({
              Core_models.Ops.Range.f_start
              =
              i *! Libcrux_ml_dsa.Simd.Traits.v_COEFFICIENTS_IN_SIMD_UNIT <: usize;
              Core_models.Ops.Range.f_end
              =
              (i +! mk_usize 1 <: usize) *! Libcrux_ml_dsa.Simd.Traits.v_COEFFICIENTS_IN_SIMD_UNIT
              <:
              usize
            }
            <:
            Core_models.Ops.Range.t_Range usize)
          (Libcrux_ml_dsa.Simd.Traits.f_to_coefficient_array #v_SIMDUnit
              #FStar.Tactics.Typeclasses.solve
              (p.Libcrux_ml_dsa.Polynomial.f_simd_units.[ i ] <: v_SIMDUnit)
              (result.[ ({
                    Core_models.Ops.Range.f_start
                    =
                    i *! Libcrux_ml_dsa.Simd.Traits.v_COEFFICIENTS_IN_SIMD_UNIT <: usize;
                    Core_models.Ops.Range.f_end
                    =
                    (i +! mk_usize 1 <: usize) *!
                    Libcrux_ml_dsa.Simd.Traits.v_COEFFICIENTS_IN_SIMD_UNIT
                    <:
                    usize
                  }
                  <:
                  Core_models.Ops.Range.t_Range usize) ]
                <:
                t_Slice i32)
            <:
            t_Slice i32))
    (to_i32_nat_body #v_SIMDUnit #i0 p.Libcrux_ml_dsa.Polynomial.f_simd_units)
    (fun acc i -> ());
  lemma_foldnat_eq_rec #v_SIMDUnit #i0 p.Libcrux_ml_dsa.Polynomial.f_simd_units 0
    (Rust_primitives.Hax.repeat (mk_i32 0) (mk_usize 256))
#pop-options

(* (B) Nat-fold characterization: every (8u+lane)-th coefficient of the
   completed fold equals `f_repr units[u] lane`.  Induction on the iteration
   counter `start`, carrying the invariant "blocks [0,start) already correct".
   Maintenance is one `lemma_index_update_at_range` per step + the trait post
   `block == f_repr units[start]`. *)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 300"
let rec lemma_to_i32_fold_nat_index
      (#v_SIMDUnit: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (units: t_Slice v_SIMDUnit {Seq.length units == 32})
      (u: nat{u < 32})
      (lane: nat{lane < 8})
      (start: nat{start <= 32})
      (acc: t_Array i32 (mk_usize 256))
      (inv:
          (uu: nat{uu < start}) ->
          (ll: nat{ll < 8}) ->
          Lemma
            (Seq.index acc (8 * uu + ll) ==
             Seq.index (i0._super_i2.f_repr (Seq.index units uu)) ll))
    : Lemma
      (ensures
        Seq.index
          (to_i32_rec #v_SIMDUnit #i0 units start acc)
          (8 * u + lane) ==
        Seq.index (i0._super_i2.f_repr (Seq.index units u)) lane)
      (decreases 32 - start) =
  if start = 32 then inv u lane   (* to_i32_rec _ 32 acc == acc; inv u lane closes it *)
  else begin
    let range:Core_models.Ops.Range.t_Range usize =
      {
        Core_models.Ops.Range.f_start
        =
        mk_usize start *! Libcrux_ml_dsa.Simd.Traits.v_COEFFICIENTS_IN_SIMD_UNIT <: usize;
        Core_models.Ops.Range.f_end
        =
        (mk_usize start +! mk_usize 1 <: usize) *! Libcrux_ml_dsa.Simd.Traits.v_COEFFICIENTS_IN_SIMD_UNIT
        <:
        usize
      }
    in
    let slice:t_Slice i32 = acc.[ range ] in
    let block:t_Slice i32 =
      Libcrux_ml_dsa.Simd.Traits.f_to_coefficient_array #v_SIMDUnit
        #FStar.Tactics.Typeclasses.solve (units.[ mk_usize start ] <: v_SIMDUnit) slice
    in
    let acc':t_Array i32 (mk_usize 256) = to_i32_nat_body #v_SIMDUnit #i0 units acc start in
    assert (acc' == Rust_primitives.Hax.Monomorphized_update_at.update_at_range acc range block);
    Rust_primitives.Hax.Monomorphized_update_at_Lemmas.lemma_index_update_at_range acc range block;
    assert (v range.Core_models.Ops.Range.f_start == 8 * start);
    assert (v range.Core_models.Ops.Range.f_end == 8 * start + 8);
    assert (block == i0._super_i2.f_repr (Seq.index units start));
    (* Extend the block invariant from `start` to `start+1` for acc'.  Passed
       as a Lemma value (no forall triggers). *)
    let inv' (uu: nat{uu < start + 1}) (ll: nat{ll < 8})
      : Lemma
        (Seq.index acc' (8 * uu + ll) ==
         Seq.index (i0._super_i2.f_repr (Seq.index units uu)) ll) =
      if uu < start
      then
        (inv uu ll;
          assert (8 * uu + ll < 8 * start))
      else
        (assert (uu == start);
          assert (8 * start <= 8 * uu + ll /\ 8 * uu + ll < 8 * start + 8);
          assert (8 * uu + ll - 8 * start == ll))
    in
    lemma_to_i32_fold_nat_index #v_SIMDUnit #i0 units u lane (start + 1) acc' inv'
  end
#pop-options

(* L2 (to_i32_array fold characterization): the (8u+lane)-th coefficient of
   `to_i32_array p` is the lane-th coefficient of `f_repr p.units[u]`.
   impl_2__to_i32_array is a `fold_range 0 32 (fun _ _ -> true) result0
   <inline step>` writing per-block via `update_at_range` (Polynomial cannot be
   touched — whole-tree cascade).  Proof: (A) `lemma_to_i32_array_is_fold_nat`
   bridges the inline fold to the closure-free `to_i32_rec` recursion (via the
   pointwise-Lemma nat-fold bridge, sidestepping the hax closure inequality);
   (B) `lemma_to_i32_fold_nat_index` characterizes `to_i32_rec`'s (8u+lane)-th
   coefficient by induction (base invariant vacuous at start=0).  Both posts are
   phrased over the closure-FREE `to_i32_rec`, so Z3's `Seq.index` congruence
   here is clean (a closure-bearing fold term stalls with "incomplete
   quantifiers"). *)
#push-options "--fuel 0 --ifuel 1 --z3rlimit 100"
let lemma_to_i32_array_index
      (#v_SIMDUnit: Type0)
      (i0: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (p: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
      (u: nat{u < 32})
      (lane: nat{lane < 8})
    : Lemma
      (requires Seq.length p.Libcrux_ml_dsa.Polynomial.f_simd_units == 32)
      (ensures
        Seq.index (Libcrux_ml_dsa.Polynomial.impl_2__to_i32_array #v_SIMDUnit p) (8 * u + lane) ==
        Seq.index
          (i0._super_i2.f_repr
            (Seq.index p.Libcrux_ml_dsa.Polynomial.f_simd_units u))
          lane) =
  (* (A) impl_2 p == to_i32_rec i0 units 0 result0 *)
  lemma_to_i32_array_is_fold_nat #v_SIMDUnit #i0 p;
  (* (B) Seq.index (to_i32_rec i0 units 0 result0) (8u+lane) == f_repr units[u] lane *)
  lemma_to_i32_fold_nat_index #v_SIMDUnit #i0 p.Libcrux_ml_dsa.Polynomial.f_simd_units u lane 0
    (Rust_primitives.Hax.repeat (mk_i32 0) (mk_usize 256))
    (fun uu ll -> ())
#pop-options

(* count_row_ones peels the last index, so an 8-wide block [8u, 8u+8) unfolds
   into the running count plus 8 indicator terms. *)
#push-options "--fuel 9 --ifuel 1 --z3rlimit 100"
let lemma_count_row_ones_block (row: t_Array i32 (mk_usize 256)) (u: nat{u < 32})
    : Lemma
      (ensures
        Libcrux_ml_dsa.Encoding.Signature.count_row_ones row (8 * (u + 1)) ==
        Libcrux_ml_dsa.Encoding.Signature.count_row_ones row (8 * u) +
        (if Seq.index row (8 * u + 0) = mk_i32 1 then 1 else 0) +
        (if Seq.index row (8 * u + 1) = mk_i32 1 then 1 else 0) +
        (if Seq.index row (8 * u + 2) = mk_i32 1 then 1 else 0) +
        (if Seq.index row (8 * u + 3) = mk_i32 1 then 1 else 0) +
        (if Seq.index row (8 * u + 4) = mk_i32 1 then 1 else 0) +
        (if Seq.index row (8 * u + 5) = mk_i32 1 then 1 else 0) +
        (if Seq.index row (8 * u + 6) = mk_i32 1 then 1 else 0) +
        (if Seq.index row (8 * u + 7) = mk_i32 1 then 1 else 0)) = ()
#pop-options

(* L4 core: count_row_ones over the first `8k` coeffs equals the first-`k`-units
   hint sum.  Induction on k: block-decompose count_row_ones, bridge each lane via
   L2 (to_i32_array index) + binary (x∈{0,1} ⟹ v(cast x)==[x==1]) + compute_hint_8. *)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 300"
let rec lemma_row_bridge_upto
      (#v_SIMDUnit: Type0)
      (i0: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (hint_simd: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
      (k: nat{k <= 32})
    : Lemma
      (requires
        Seq.length hint_simd.Libcrux_ml_dsa.Polynomial.f_simd_units == 32 /\
        (forall (u: nat). u < 32 ==>
          Libcrux_ml_dsa.Simd.Traits.Specs.is_binary_array_8_opaque
            (i0._super_i2.f_repr
              (Seq.index hint_simd.Libcrux_ml_dsa.Polynomial.f_simd_units u))))
      (ensures
        Libcrux_ml_dsa.Encoding.Signature.count_row_ones
          (Libcrux_ml_dsa.Polynomial.impl_2__to_i32_array #v_SIMDUnit hint_simd) (8 * k) ==
        sum_unit_hints i0 hint_simd.Libcrux_ml_dsa.Polynomial.f_simd_units k)
      (decreases k) =
  if k = 0 then ()
  else begin
    let units = hint_simd.Libcrux_ml_dsa.Polynomial.f_simd_units in
    let arr = Libcrux_ml_dsa.Polynomial.impl_2__to_i32_array #v_SIMDUnit hint_simd in
    lemma_row_bridge_upto i0 hint_simd (k - 1);
    lemma_count_row_ones_block arr (k - 1);
    assert (Libcrux_ml_dsa.Simd.Traits.Specs.is_binary_array_8_opaque
              (i0._super_i2.f_repr (Seq.index units (k - 1))));
    lemma_compute_hint_8 (i0._super_i2.f_repr (Seq.index units (k - 1)));
    lemma_to_i32_array_index i0 hint_simd (k - 1) 0;
    lemma_to_i32_array_index i0 hint_simd (k - 1) 1;
    lemma_to_i32_array_index i0 hint_simd (k - 1) 2;
    lemma_to_i32_array_index i0 hint_simd (k - 1) 3;
    lemma_to_i32_array_index i0 hint_simd (k - 1) 4;
    lemma_to_i32_array_index i0 hint_simd (k - 1) 5;
    lemma_to_i32_array_index i0 hint_simd (k - 1) 6;
    lemma_to_i32_array_index i0 hint_simd (k - 1) 7
  end
#pop-options

(* L4 (row bridge): given all 32 units binary, the one-count of `to_i32_array
   hint_simd` over 256 coeffs equals the sum of per-unit compute_hint counts. *)
let lemma_row_bridge
      (#v_SIMDUnit: Type0)
      (i0: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (hint_simd: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
    : Lemma
      (requires
        Seq.length hint_simd.Libcrux_ml_dsa.Polynomial.f_simd_units == 32 /\
        (forall (u: nat). u < 32 ==>
          Libcrux_ml_dsa.Simd.Traits.Specs.is_binary_array_8_opaque
            (i0._super_i2.f_repr
              (Seq.index hint_simd.Libcrux_ml_dsa.Polynomial.f_simd_units u))))
      (ensures
        Libcrux_ml_dsa.Encoding.Signature.count_row_ones
          (Libcrux_ml_dsa.Polynomial.impl_2__to_i32_array #v_SIMDUnit hint_simd) 256 ==
        sum_unit_hints i0 hint_simd.Libcrux_ml_dsa.Polynomial.f_simd_units 32) =
  lemma_row_bridge_upto i0 hint_simd 32

(* L6: updating row `k >= i` leaves the first-`i`-rows sum unchanged. *)
let rec lemma_sum_rows_upd
      (hint: t_Slice (t_Array i32 (mk_usize 256)))
      (i: nat{i <= Seq.length hint})
      (k: nat{k < Seq.length hint})
      (x: t_Array i32 (mk_usize 256))
    : Lemma (requires i <= k)
            (ensures sum_rows (Seq.upd hint k x) i == sum_rows hint i)
            (decreases i) =
  if i = 0 then ()
  else lemma_sum_rows_upd hint (i - 1) k x

(* L7: updating unit `k >= j` leaves the first-`j`-units sum unchanged. *)
let rec lemma_sum_unit_hints_upd
      (#v_SIMDUnit: Type0)
      (i0: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (units: t_Slice v_SIMDUnit)
      (j: nat{j <= Seq.length units})
      (k: nat{k < Seq.length units})
      (x: v_SIMDUnit)
    : Lemma (requires j <= k)
            (ensures sum_unit_hints i0 (Seq.upd units k x) j == sum_unit_hints i0 units j)
            (decreases j) =
  if j = 0 then ()
  else lemma_sum_unit_hints_upd i0 units (j - 1) k x

(* L5 core: the total sum equals the first-`i` sum plus count_total_ones of the
   suffix `[i, n)`.  Induction on the suffix length, matching count_total_ones's
   front-peel; uses only slice lemmas (slice_slice / lemma_index_slice). *)
let rec lemma_sum_rows_suffix (hint: t_Slice (t_Array i32 (mk_usize 256))) (i: nat{i <= Seq.length hint})
    : Lemma
      (ensures
        sum_rows hint (Seq.length hint) ==
        sum_rows hint i +
        Libcrux_ml_dsa.Encoding.Signature.count_total_ones (Seq.slice hint i (Seq.length hint)))
      (decreases (Seq.length hint - i)) =
  let n = Seq.length hint in
  if i = n then
    Seq.lemma_eq_intro (Seq.slice hint i n) (Seq.empty #(t_Array i32 (mk_usize 256)))
  else begin
    lemma_sum_rows_suffix hint (i + 1);
    Seq.lemma_index_slice hint i n 0;
    Seq.slice_slice hint i n 1 (n - i)
  end

let lemma_sum_rows_eq_count_total (hint: t_Slice (t_Array i32 (mk_usize 256)))
    : Lemma
      (ensures
        sum_rows hint (Seq.length hint) ==
        Libcrux_ml_dsa.Encoding.Signature.count_total_ones hint) =
  lemma_sum_rows_suffix hint 0;
  Seq.lemma_eq_intro (Seq.slice hint 0 (Seq.length hint)) hint

(* Inner-fold step maintenance: the inner invariant survives one unit step.
   The trait guarded-count post is passed verbatim (as `high_local_guard ==>
   v out == compute_hint (f_repr tmp0)`); this lemma discharges the
   `high_all_nonneg` instance internally. *)
let lemma_make_hint_inner_step
      (#v_SIMDUnit: Type0)
      (i0: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (high: t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
      (hint: t_Slice (t_Array i32 (mk_usize 256)))
      (i: usize)
      (hint_simd: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
      (true_hints out: usize)
      (j: usize)
      (tmp0: v_SIMDUnit)
    : Lemma
      (requires
        v i < Seq.length high /\ v j < 32 /\
        (forall (u: nat). u < v j ==>
          Libcrux_ml_dsa.Simd.Traits.Specs.is_binary_array_8_opaque
            (i0._super_i2.f_repr
              (Seq.index hint_simd.Libcrux_ml_dsa.Polynomial.f_simd_units u))) /\
        (high_all_nonneg #v_SIMDUnit i0 high ==>
          v true_hints ==
          sum_rows hint (v i) +
          sum_unit_hints i0 hint_simd.Libcrux_ml_dsa.Polynomial.f_simd_units (v j)) /\
        Libcrux_ml_dsa.Simd.Traits.Specs.is_binary_array_8_opaque
          (i0._super_i2.f_repr tmp0) /\
        ((forall (lane: nat). lane < 8 ==>
            v (Seq.index
                  (i0._super_i2.f_repr
                    (Seq.index (Seq.index high (v i)).Libcrux_ml_dsa.Polynomial.f_simd_units (v j)))
                  lane) >= 0 /\
            v (Seq.index
                  (i0._super_i2.f_repr
                    (Seq.index (Seq.index high (v i)).Libcrux_ml_dsa.Polynomial.f_simd_units (v j)))
                  lane) < 8380417) ==>
          v out == Spec.MLDSA.Math.compute_hint (i0._super_i2.f_repr tmp0)))
      (ensures
        (let nu = Seq.upd hint_simd.Libcrux_ml_dsa.Polynomial.f_simd_units (v j) tmp0 in
          (forall (u: nat). u < v j + 1 ==>
            Libcrux_ml_dsa.Simd.Traits.Specs.is_binary_array_8_opaque
              (i0._super_i2.f_repr (Seq.index nu u))) /\
          (high_all_nonneg #v_SIMDUnit i0 high ==>
            v true_hints + v out == sum_rows hint (v i) + sum_unit_hints i0 nu (v j + 1)))) =
  lemma_sum_unit_hints_upd i0 hint_simd.Libcrux_ml_dsa.Polynomial.f_simd_units (v j) (v j) tmp0;
  reveal_opaque (`%high_all_nonneg) (high_all_nonneg #v_SIMDUnit i0 high)

(* Outer-fold step maintenance: writing row `i` = to_i32_array hint_simd
   extends the row sum by count_row_ones of that row (= the accumulated
   per-unit hint counts, via the row bridge). *)
let lemma_make_hint_outer_step
      (#v_SIMDUnit: Type0)
      (i0: Libcrux_ml_dsa.Simd.Traits.t_Operations v_SIMDUnit)
      (high: t_Slice (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit))
      (hint: t_Slice (t_Array i32 (mk_usize 256)))
      (i: usize)
      (hint_simd: Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement v_SIMDUnit)
      (true_hints: usize)
    : Lemma
      (requires
        v i < Seq.length hint /\
        (forall (u: nat). u < 32 ==>
          Libcrux_ml_dsa.Simd.Traits.Specs.is_binary_array_8_opaque
            (i0._super_i2.f_repr
              (Seq.index hint_simd.Libcrux_ml_dsa.Polynomial.f_simd_units u))) /\
        (high_all_nonneg #v_SIMDUnit i0 high ==>
          v true_hints ==
          sum_rows hint (v i) + sum_unit_hints i0 hint_simd.Libcrux_ml_dsa.Polynomial.f_simd_units 32))
      (ensures
        (let nh =
            Seq.upd hint (v i) (Libcrux_ml_dsa.Polynomial.impl_2__to_i32_array #v_SIMDUnit hint_simd)
          in
          Seq.length nh == Seq.length hint /\
          (high_all_nonneg #v_SIMDUnit i0 high ==> v true_hints == sum_rows nh (v i + 1)))) =
  lemma_sum_rows_upd hint (v i) (v i)
    (Libcrux_ml_dsa.Polynomial.impl_2__to_i32_array #v_SIMDUnit hint_simd);
  lemma_row_bridge i0 hint_simd

#pop-options
