# Outstanding Admits

This file tracks every `admit()`, `admit_smt_queries`, or
`#[hax_lib::fstar::verification_status::panic_free]` annotation in the
ML-DSA proof effort. Each entry should answer: where, why, and what
mitigation a USER (human prover) might attempt.

## Template entry

```
### <Module>.<function>
- **File / lines**: `path/to/file.rs:LINE_START-LINE_END`
- **Annotation**: `panic_free` | `fstar!("admit()")` | `--admit_smt_queries true`
- **Phase added**: 0 | 1 | 2x | 3x | 4x
- **Diagnosis**: <one paragraph: Z3 timeout? Quantifier blowup? Missing
  lemma? FE-algebra divergence? What was tried in the 20-minute budget?>
- **Suggested mitigation**: <agent-lane vs USER-lane; specific approach
  (split into N sub-lemmas; factor branch-post; explicit zeta-table
  induction; etc.)>
- **Template value**: <does landing this proof unblock similar admits?>
```

---

## Pre-budgeted admits (planned from day 1)

Items we expect to mark admitted on first attempt; including them here
so subsequent sessions don't burn budget retrying:

### Libcrux_ml_dsa.Simd.Avx2.Ntt.{layer_1, layer_2}
- **Phase**: 3D
- **Diagnosis**: 4-zeta-parallel SIMD layer where Z3 can't handle the
  wide context (ML-KEM USER-4 analog, see
  `libcrux-ml-kem/proofs/manual-proof-targets.md`).
- **Suggested mitigation**: USER lane. Refactor each AVX2 layer body
  into 4 per-zeta sub-functions to split the proof obligations; or
  await SIMD model unification (`libcrux-ml-kem/proofs/simd-model-unification-plan.md`).

### Libcrux_ml_dsa.Simd.Avx2.Invntt.{layer_3, layer_4}
- **File / lines**: `libcrux-ml-dsa/src/simd/avx2/invntt.rs:524` (layer_3), `:552` (layer_4)
- **Annotation**: `#[hax_lib::fstar::verification_status(panic_free)]`
- **Phase**: 3E
- **Diagnosis**: Both layers expand into 16 / 8 calls of `outer_3_plus`
  carrying the wide `invert_ntt_outer_3_plus_spec` post. Z3 times out at
  the function-level VC (12s with rlimit 80) on the conjunction across
  iterations even at moderate normalization. Analogous to NTT layers 1–2.
- **Suggested mitigation**: USER lane. Refactor each AVX2 layer body
  into per-zeta sub-functions to split the proof obligations; or await
  SIMD model unification.
- **Note**: layer_3 admit unblocked layer_4's Z3 timeout (which was
  hidden behind layer_3's earlier failure) — both admits land together
  in the 2026-04-28 session.

### Hacspec_ml_dsa.Commute.Chunk.lemma_ntt_full_commute
- **Phase**: 2F
- **Diagnosis**: Tier-3 composition of 8 layer-step lemmas with BitRev₈
  zeta-table indexing — same shape as ML-KEM USER-2 but one more layer
  (8 vs 7).
- **Suggested mitigation**: USER lane. Template after ML-KEM's
  `lemma_ntt_full_commute` once it lands.
- **Template value**: closes NTT layer of the proof; once forward
  composition is proven, INVNTT and ntt_multiply compositions are
  direct adaptations.

---

## Resolved (2026-04-27/28 Funarr-unblock session)

Items repaired across commits `04fd066f0`, `42d4a3347`, and `1c827fab7`.

### Specs.fst lemma fixes (commit `04fd066f0`)
- **`lemma_decompose_lane_lookup` Error 19** — fixed by hoisting
  `((v gamma2 == 95232) \/ (v gamma2 == 261888))` into the lemma's
  `requires`. Same hoist applied to `lemma_compute_hint_lane_lookup` and
  `lemma_use_hint_lane_lookup` which had the identical opaque-shielded
  function-call-precondition issue (revealed once the decompose error
  was cleared).

### Phase-1 over-strong post relaxations (commit `04fd066f0`)
- **`infinity_norm_exceeds_post` over-strong vs pre** — relaxed: now
  cites raw signed absolute value (`if x >= 0 then x else -x`) instead
  of `Hacspec_ml_dsa.Arithmetic.coeff_norm`. Compatible with the loose
  `is_i32b_array_opaque FIELD_MAX simd_unit` pre.
- **`reduce_lane_post` over-strong vs impl** — relaxed from `0 <= v r < q`
  to centered Barrett range `(-q < v r < q) /\ (v r) % q == (v input) % q`.
- **`montgomery_multiply_lane_post` triple-product i64 overflow** —
  rewrote post in mathematical `int` arithmetic
  (`(v future_lhs) % q == (v lhs * v rhs * 8265825) % q`) instead of the
  i64 expression `(cast lhs *! cast rhs *! mk_i64 8265825)` which
  overflows i64.

### AVX2 reduce impl bug (commit `04fd066f0`)
- **`Operations::reduce` 4-of-32** — replaced four hard-coded
  `shift_left_then_reduce::<0>(&mut simd_units[{0,8,16,24}].value)`
  calls with `for i in 0..simd_units.len() { ... }`.

### Funarr/Bitvec source-level unblock (commit `42d4a3347`)
- **`crates/utils/core-models/src/abstractions/{funarr,bitvec}.rs`** —
  the hax-generated F\* `replace` overrides for `FunArray::from_fn` and
  `BitVec::from_fn` declared a single implicit type slot (`#v_T`) but
  hax extracts call sites with two implicits (impl-block's `T` plus the
  closure's auto-inferred `F: Fn(u64) -> T`). Added an `#_v_F: Type0`
  absorbing slot to both override signatures plus passed it explicitly
  at the in-replace call sites inside `FunArray::fold` and the inner
  call from `BitVec::from_fn` to `FunArray::from_fn`. Persistent
  source-level fix; survives `./hax.sh extract`. **Unblocked all
  `Simd.*` impl proofs from empirical validation** — this was the
  single largest gating finding of the session.

### Trait-side fixes surfaced by the unblock (commit `1c827fab7`)
- **`error_deserialize` post Eta enum projection (Error 189)** — used
  `v $eta == 2 / 4` against the `Eta` enum (not an int_t). Replaced
  with direct variant equality (`$eta == Libcrux_ml_dsa.Constants.Eta_Two`).
- **Three `rejection_sample_*` posts Seq.index well-formedness (Error 19)** —
  `forall (i:nat). i < v $result ==> v (Seq.index ${out}_future i) ...`
  doesn't typecheck without `i < Seq.length out_future`. Bound `i`
  in-forall to `i:nat{i < Seq.length ${out}_future}`.

## Active admits — above-trait branch (`ml-dsa-above-trait` lane)

### Libcrux_ml_dsa.Arithmetic.power2round_vector
- **File**: `src/arithmetic.rs:65-81` (post `8d532957e`)
- **Annotation**: `verification_status(panic_free)` + `hax_lib::fstar!("admit ()")`
- **Diagnosis**: hax extraction quirk — `&mut t0[i]` resolves Index
  typeclass cleanly but `&mut t1[i]` (the second `&mut` arg passed to
  `power2round_one_ring_element`) fails with Error 228:
  `Could not solve typeclass constraint Core_models.Ops.Index.t_Index
  (FStar.Seq.Base.seq (Libcrux_ml_dsa.Polynomial.t_PolynomialRingElement ...))`.
  Both args have the same type — asymmetric.
- **Closure attempt (2026-04-29, ~22 min)**: tried three restructurings —
  (1) loop_invariant + helper kept; (2) local-clone of `t0[i]`/`t1[i]` to
  mutable locals + `power2round_one_ring_element(&mut local_t0, &mut local_t1)`
  + write-back; (3) inline helper body so the call site passes
  `&mut t0[i].simd_units[j]` and `&mut t1[i].simd_units[j]` to
  `SIMDUnit::power2round` (a trait method, not a local fn).
  All three hit Error 228 on the SECOND slice access (`t1.[i]` or
  `t1[i].simd_units.[j]`) regardless of restructure.
  Notably `decompose_vector` extracts cleanly with the parallel
  `(low.[i], high.[i])` shape — difference unclear; possibly fold
  accumulator naming (`(high, low)` alphabetical vs `(t0, t1)`),
  loop_invariant content, or context-pruning of the typeclass
  instance set.  This appears to be a hax-extraction asymmetry rather
  than something fixable from arithmetic.rs alone.
- **Suggested mitigation**: rename the slice arguments so the fold
  accumulator is alphabetized, e.g. `(t0, t1)` → `(low, high)` or
  `(a, b)`, and re-test.  Or factor into a single fold with a
  combined `(t0_slice, t1_slice)` tuple-typed parameter passed to
  helper that accepts both as values and returns a tuple.  Or report
  as hax bug.

### Libcrux_ml_dsa.Arithmetic.use_hint
- **File**: `src/arithmetic.rs:155-185` (post `b097daf01`)
- **Annotation**: `verification_status(panic_free)` + `hax_lib::fstar!("admit ()")`
- **Diagnosis**: body needs `from_i32_array(&hint[i], &mut tmp)` post
  (`tmp.repr() == hint[i]`) bridged to per-simd-unit
  `is_binary_array_8_opaque (f_repr tmp.simd_units[j])` so the inner
  `Operations::use_hint` call's pre is satisfied.  The intro lemma
  `lemma_is_binary_array_8_intro` exists; needs to be applied per-j
  with hypotheses from the slice-level binary property.
- **Closure attempt (2026-04-29)**: investigation showed
  `from_i32_array` in `src/polynomial.rs:128-136` has NO ensures
  (extracted post is `Prims.l_True`).  The intro lemma cannot fire
  because the per-simd-unit `repr()` equality is not visible at the
  call site without inlining.  The recipe ("Classical.forall_intro
  applying lemma_is_binary_array_8_intro after from_i32_array") relied
  on `from_i32_array` having a strong post — which it does not.
- **Suggested mitigation (Option A, in arithmetic.rs only)**: replace
  the `from_i32_array(&hint[i], &mut tmp)` call with an inline
  per-simd-unit fold calling `SIMDUnit::from_coefficient_array`
  directly.  `from_coefficient_array` has the trait post
  `future(out).repr() == array`, so a loop_invariant of shape
  `forall kk < k. is_binary_array_8_opaque (f_repr tmp.simd_units[kk])`
  carries the binary property forward (via `lemma_is_binary_array_8_intro`
  applied per-iteration after the `from_coefficient_array` call).
  Estimated effort: 30-45 min (uncertain — first iteration would still
  need the loop-invariant for the outer i-loop to thread the hint binary
  property + the inner loop's accumulated post + the j-loop after; non-trivial).
- **Suggested mitigation (Option B)**: add an `ensures` to
  `Polynomial::from_i32_array` exposing
  `forall kk < 32. (future(result).simd_units[kk]).repr() == array[kk*8..(kk+1)*8]`.
  Then the original recipe works directly.  Out of scope for the
  arithmetic.rs lane but is the cleaner fix and unblocks any other
  call site needing a per-simd-unit post.

### Libcrux_ml_dsa.Arithmetic.power2round_one_ring_element
- **Status**: closed at `8d532957e` — admit removed, strong post
  discharged via loop_invariant + Spec.Utils.forall8.

### 

Body admits added during Step C promotions (2026-04-28).  Each
keeps the trait pre/post strong (the contract callers see) but
admits the panic-free body.  Below-trait branch is unaffected;
these are local to the above-trait lane.

### Libcrux_ml_dsa.Encoding.{Error,T0}.deserialize_to_vector_then_ntt
- **Files**: `src/encoding/{error,t0}.rs`, in `deserialize_to_vector_then_ntt`
- **Annotation**: `verification_status(panic_free)` + `hax_lib::fstar!("admit ()")`
- **Phase added**: above-trait C.2/C.3 (`2eefebe43`, `9848dde7c`)
- **Status update (2026-04-29)**:
  - **T0**: CLOSED at `577a112cf` — body admit replaced with real proof.
    Loop invariant `forall k<i. forall j<32. is_i32b_array_opaque FIELD_MAX
    (ring_elements[k].simd_units[j].repr)`; `pow2 12 → NTT_BASE_BOUND` lift via
    per-j `Spec.Utils.is_i32b_array_larger` invoked by `Classical.forall_intro`
    after the local `deserialize` (which propagates the trait's
    `is_i32b_strict_lower_array_opaque (pow2 12)` post via the existing SMTPat
    `lemma_is_i32b_strict_lower_implies_array_opaque`).  Verified 2.5s @ rlimit 21.
  - **Error**: BODY ADMIT RETAINED, length-preservation ensures added at
    `(this commit)`.  Strong-bound shape is harder than T0's because the
    `Operations::error_deserialize` trait post is in eta-conditional `forall8`
    form (raw bound, not `is_i32b_strict_lower_array_opaque` with SMTPat
    support), so the lift to `is_i32b_array_opaque eta_value` is manual
    (would need `reveal_opaque (`%is_i32b_array_opaque)` plus a case-split
    on `eta` between `Eta_Two` and `Eta_Four`).  A prior agent attempt
    (`8601b2420` on `agent-error-rs-deserialize-ntt`) reported all individual
    sub-goals (deserialize ensures, ntt pre, index pre) verifying under
    `assert`, but the composite loop-invariant *preservation* step (extending
    `forall k<i ...` to `forall k<i+1 ...` through `update_at_usize` + `ntt`'s
    post) timed out at `--z3rlimit 14-15s` with `reason-unknown=canceled`.
    Likely fix path: pivot to polynomial-level
    `Libcrux_ml_dsa.Polynomial.Spec.is_bounded_poly` (already defined; SMTPat
    + intro lemmas in place) instead of the nested-forall shape, to avoid
    quantifier-trigger explosion.
- **Suggested mitigation (closing the body)**: as above — try is_bounded_poly
  factoring to avoid nested-forall blowup; or write a manual bridge lemma in
  `Spec.Utils` converting eta-conditional `forall8` to `is_i32b_array_opaque`,
  then mirror T0's pattern.  ~30-45 min once the bridge is in place.

### Libcrux_ml_dsa.Encoding.Verification_key.{generate_serialized,deserialize}
- **File**: `src/encoding/verification_key.rs`
- **Annotation**: `verification_status(panic_free)` + `hax_lib::fstar!("admit ()")`
- **Phase added**: above-trait C.5 (`0d11b64a9`)
- **Status update (2026-04-29)**:
  - **deserialize**: CLOSED at `743956689` — inline `320` literal in slice
    index + minimal `loop_invariant` (`i <= rows_in_a /\ rows_in_a <= 8 /\
    rows_in_a == Seq.length t1 /\ Seq.length serialized == rows_in_a * 320`)
    + `--z3rlimit 200`.  Verifies in ~2s.
  - **generate_serialized**: CLOSED Session B.1 (2026-04-30).  Mirrored
    `Signing_key.generate_serialized` pattern: hoist `t1.len()` into a
    nameable `t1_len` binding, attach a `loop_invariant!` carrying the
    triple-forall on t1 + length identity on `verification_key_serialized`,
    plus offset-arithmetic asserts.  Two notable choices:
    (i) `--z3rlimit 400 --split_queries always --fuel 0 --ifuel 1` (the
    earlier estimate of explosion at rlimit 800 was correct for the previous
    proof attempt that did not split; with split_queries and the right
    invariant shape the obligations split into ~80 small queries that all
    discharge); (ii) `assert_norm (v $RING_ELEMENT_OF_T1S_SIZE == 320)`
    instead of plain `assert` — needed because `BITS_IN_UPPER_PART_OF_T =
    FIELD_MODULUS_MINUS_ONE_BIT_LENGTH - BITS_IN_LOWER_PART_OF_T` adds an
    extra unfold step that Z3 cannot fold under `fuel 0`.

### Libcrux_ml_dsa.Encoding.Signing_key.generate_serialized
- **File**: `src/encoding/signing_key.rs`
- **Annotation**: `verification_status(panic_free)` + `hax_lib::fstar!("admit ()")`
- **Phase added**: above-trait C.5 (`0d11b64a9`)
- **Diagnosis**: hardest of the C.5 batch.  Body has 5 sequential
  slice writes with running `offset` variable: seed_matrix (32),
  seed_signing (32), shake256-output verification_key_hash (64),
  per-poly s1_2 errors (eta-conditional size), per-poly t0
  serializations (416 each).  The Shake256 trait method's post
  needs length-preservation ensures (added in `b68738411` for
  shake128 and shake256 Xof; verify it covers `DsaXof::shake256`
  too).
- **Suggested mitigation**: add length-preservation ensures to
  `shake256::DsaXof::shake256<OUT_LEN>` if missing.  Then split
  the body into 3 sub-functions (seed-write block, error-loop, t0-loop)
  with intermediate length post-conditions.  ~45 min.

### Libcrux_ml_dsa.Encoding.Signature.serialize
- **File**: `src/encoding/signature.rs`
- **Annotation**: `verification_status(panic_free)` + `hax_lib::fstar!("admit ()")`
- **Phase added**: above-trait C.5 (`0d11b64a9`)
- **Diagnosis**: `serialize` packs commitment_hash + per-poly
  gamma1_serialize + hint-bit-pack with running `true_hints_seen`
  counter and per-row written count.  Bounding the counter
  requires a count-of-ones precondition that the caller
  (`sign_internal`) ensures via `if ones_in_hint > MAX_ONES_IN_HINT
  { skip }`, but expressing it in F* needs either a recursive
  spec helper or a function-signature change.
- **Suggested mitigation**: helper-split mirroring PR 1348's
  `deserialize` closure — extract the hint-pack inner loop into
  `write_signature_hints` and carry the count bound through it.
  See post-merge-handoff Session B option list.

`Encoding.Signature.deserialize` was closed in PR 1348 (`9c83b0279`).

`set_hint` helper got a real `requires(i < out_hint.len() && j < 256)`
in `0d11b64a9` (no admit needed there).

### Polynomial::add_bounded / subtract_bounded helpers (no admit)
- **File**: `src/polynomial.rs:93-160`
- **Status**: both prove clean (`bounded_add_post` / `bounded_sub_post`
  SMTPats fire per simd-unit; pre `is_i32b_array_opaque b1 self ∧
  is_i32b_array_opaque b2 rhs ∧ b1+b2 ≤ i32::MAX` gives polynomial-level
  post `is_i32b_array_opaque (b1+b2) self_future`).
- **Mirrors**: ML-KEM's `add_to_ring_element(myself, rhs, _bound)` recipe
  — ghost bound parameters thread the bound chain through composition
  without forcing per-lane forall expansion at every call site.
- **Used by**: `add_vectors`, `subtract_vectors` (admit removed; see below).

### Slice snapshot trick: `lhs.to_vec().as_slice()`
The frame-property invariant ML-KEM uses (`#[cfg(hax)] let _result = result`)
relies on `result` being an owned fixed-size array (Copy).  ML-DSA matrix
wrappers take `&mut [T]` slices, which can't be snapshot-cloned that way
(hax HAX0003 error).  Workaround:
```rust
#[cfg(hax)]
let e_lhs_orig: &[PolynomialRingElement<SIMDUnit>] = lhs.to_vec().as_slice();
```
The chain `to_vec` (allocates a Vec) `.as_slice()` (returns `&[T]`)
extracts to F* as
`Alloc.Vec.impl_1__as_slice (Alloc.Slice.impl__to_vec lhs)`.  Both
functions are local-let-defined and F* unfolds them well enough at
sufficient rlimit (400-800 with `--split_queries always`) to prove
`Seq.length lhs == Seq.length e_lhs_orig` and
`forall k. Seq.index lhs k == Seq.index e_lhs_orig k` initially.
The `extern crate alloc;` under cfg(hax) makes `Vec` reachable in
this no_std crate.

In Rust, `let _orig = lhs.to_vec().as_slice()` would dangle (the
temporary Vec is dropped at the end of the statement), but the
binding only exists under `#[cfg(hax)]` and never compiles in
non-hax builds.

### Libcrux_ml_dsa.Matrix.{compute_as1_plus_s2,compute_matrix_x_mask,compute_w_approx} (3 of 6 still admit)
**Status update**: `add_vectors`, `subtract_vectors`, and
`vector_times_ring_element` no longer admit their bodies — the proof
closure is via `Polynomial::add_bounded`/`subtract_bounded` + the
`lhs.to_vec().as_slice()` snapshot trick + `--z3rlimit 400-800
--split_queries always`.

**Opaque predicate infrastructure (this commit)**: introduced
`Libcrux_ml_dsa.Polynomial.Spec.is_bounded_poly` as `opaque_to_smt`
with three companion lemmas:
- `lemma_is_bounded_poly_lookup` (SMTPat-driven — fires per simd-unit
  when `is_i32b_array_opaque b (f_repr ...simd_units[j])` is needed).
- `lemma_is_bounded_poly_intro` (manual call — re-establishes the
  opaque atom from a per-simd-unit forall, e.g. after `add_bounded`
  returns its post).
- `lemma_is_bounded_poly_higher` (manual call — monotonicity, weakens
  bound from `b1` to `b2 >= b1`, e.g. lifting the inner-loop `j *
  FIELD_MAX` to reduce's `2143289343`-bound pre).

Applying this to `compute_matrix_x_mask` made significant progress:
queries dropped from 121 → ~115 and average per-query time fell from
60-130s to under 10s.  Three failure points remain — at the inner
ntt_multiply call (matrix bound lookup at index `i*c+j`), the reduce
call (higher-lemma must be visible), and the outer-loop continuation
(frame property + intro for next-iteration invariant).  Each is a
trigger-instantiation issue rather than a complexity blowup.  Closing
all three needs ~1-2 more iterations of bridging assertions or a
slight restructuring to make instantiations more obvious.

Reverted matrix.rs to admits for now; the opaque infra is the
contributed deliverable and will accelerate the next attempt
significantly.

**Spec gap resolved (2026-04-28)**: cherry-picked Option C from
`ml-dsa-proofs` 686543e33 (above-trait commit `8ea464a2d`).
`NTT_BASE_BOUND` widened from `FIELD_MID` to `FIELD_MAX`, so the
`shift_left_then_reduce → ntt` chain in `compute_w_approx` composes
directly; the A.6 `reduce` insertion is no longer needed (removed in
`0a1f1880f`).  `reduce_lane_post` unchanged (Option B was rejected by
below-trait per F-5 finding).  The 3 remaining body admits are now
purely SMT-trigger work, not spec gaps.

**Closure attempt (2026-04-29)**: deeper investigation of the
remaining 3 wrappers surfaced two infrastructure shortfalls and one
hax extraction quirk:

1. *`shift_left_then_reduce` had no `ensures`.*  The wrapper's
   per-simd-unit post (`shift_left_then_reduce_lane_post`) lifts to
   `is_i32b_array_opaque FIELD_MAX re_future`, but the polynomial
   wrapper exposed nothing — the chain `shift_left_then_reduce →
   ntt` couldn't compose at the wrapper level.  Added an `ensures`
   producing the polynomial-level FIELD_MAX bound + per-simd-unit
   `Classical.forall_intro` lifting (commit infra in this session).
2. *`Polynomial::zero()` had no `ensures`.*  `compute_w_approx` does
   `let mut inner_result = PolynomialRingElement::zero();` then adds
   into it; without a post on `zero()` the inner accumulator started
   with `Prims.l_True` instead of `is_i32b_array_opaque 0`.  Added
   an `ensures` producing the per-simd-unit zero bound (commit infra
   in this session).
3. *Hax typeclass-resolution quirk on tuple-folded slice access.*
   When the outer fold accumulator is a tuple of slices (`(a_as_ntt,
   result)`), nested-fold body `result.[i]` access fails with
   `Error 228: Could not solve typeclass constraint
   Core_models.Ops.Index.t_Index (FStar.Seq.Base.seq ...) usize`
   even though the same shape works for single-slice accumulators
   (e.g. `add_vectors`).  Worked around by changing
   `compute_as1_plus_s2`'s `a_as_ntt: &mut [T]` parameter to
   `&[T]` (so the outer fold is single-slice), with the body cloning
   matrix entries into a `let mut product = ...` local.  The
   workaround DID extract cleanly but the SMT proof did not close in
   the 20-min budget — query 92 of `compute_w_approx` (the simplest
   of the three, post = length only) timed out at rlimit 800 with
   `--retry 3`.  Most queries (~85 of ~92) discharged in <100ms;
   one inner-loop preservation query at line 728-913 took 72s rlimit
   396.  The dominant cost is the outer-loop frame-property
   reasoning interacting with the per-simd-unit unfolds inside
   each wrapper's `--split_queries always` discharge.

The infrastructure (`shift_left_then_reduce` ensures + `zero()`
ensures) is committed in this session; future closure attempts will
benefit from these.  The three wrappers remain admitted.

**Sprint scope (recorded 2026-04-29)**:

*Core (must achieve)*:
1. Close the 3 remaining Matrix.fst body admits (compute_as1_plus_s2,
   compute_matrix_x_mask, compute_w_approx) using slice API +
   Polynomial.Spec opaque infra.
2. Strengthen Sample.fst posts beyond the current body-admit state.
3. Add length-preservation ensures to Hash_functions Xof methods
   (Shake128, Shake256, Portable, Simd256, Neon) so Sample's posts
   can chain.
4. Show `Libcrux_ml_dsa.Ml_dsa_generic.fst` is **panic-free**.
   Remove the `admit ()` body markers on the 10 functions in
   `src/ml_dsa_generic.rs` and add the pres / loop_invariants /
   bridging assertions for F* to discharge panic-freedom.
   Functional posts can stay weak — goal is panic-free, not
   functional correctness.

*Rejected (do not pursue)*:
- Refactoring matrix wrappers to fixed-size arrays.  Closure work
  must stay within the slice API.


- **File**: `src/matrix.rs`
- **Annotation**: `hax_lib::fstar!("admit ()")` mid-body (prefix)
- **Phase added**: above-trait C.6 (Matrix.fst promotion)
- **Diagnosis**: each of the six wrappers chains trait calls
  (`ntt_multiply_montgomery → add → reduce → invert_ntt_montgomery`
  with possible variations).  Wrapper pre/post is strong (FIELD_MAX-bounded
  inputs, FIELD_MAX-bounded or 2*FIELD_MAX-bounded outputs).  The body
  needs nested loop-invariants that simultaneously track partial
  bound-progress across `result[0..i]` for the outer loop AND across
  the inner-j accumulating sum.  Each wrapper individually was tried
  but the loop-invariant shape (forall over slice elements + per-poly
  bounds) timed out at rlimit 80 across 6+ subqueries even with body-only
  proof attempts.  The hax-extraction shape with `verification_status(panic_free)`
  also generated a non-linear `(result, result: Prims.unit)` pattern
  due to the parameter name clash (worked around by reverting to plain
  body admit).
- **Suggested mitigation**: per-wrapper, ~30-45 min each.  Pattern:
  add `lhs_bound: usize{lhs_bound + (cols+1)*FIELD_MAX <= i32::MAX}`
  ghost parameter to the inner loop_invariant; track per-iteration
  bound growth.  OR weaken the post to bounds-only without an
  equation chain so the SMT search space shrinks.  Caller-side fix
  A.6 (insert reduce before ntt at compute_w_approx) is applied;
  the residual gap is `reduce` post (FIELD_MAX) vs `ntt` pre
  (NTT_BASE_BOUND = FIELD_MID = FIELD_MAX/2) — the actual implementation
  produces FIELD_MID-bounded values but the spec post is loose at FIELD_MAX,
  so even with reduce inserted the chain doesn't close at the spec level
  without strengthening reduce's post (which is not in this branch's
  scope per the lane-split protocol).
- **Polynomial::add / subtract strengthening (this commit)**: both
  wrappers in `src/polynomial.rs:65-101` now carry a per-simd-unit
  ensures `forall (j:nat). j < 32 ==> add_post|sub_post old[j] rhs[j] future[j]`,
  which is what callers (Matrix and downstream) need to chain bounds.
  The body proof works via the existing loop_invariant extended with
  the partial post-progress conjunct.  No body admit on Polynomial::add
  or subtract.

### Libcrux_ml_dsa.Ml_dsa_generic (all 10 functions)
- **File**: `src/ml_dsa_generic.rs`
- **Annotation**: `hax_lib::fstar!("admit ()")` mid-body (prefix) on
  `generate_key_pair`, `sign_internal`, `verify_internal`,
  `sign_pre_hashed_mut`, `sign_pre_hashed`, `sign_mut`, `sign`,
  `verify`, `verify_pre_hashed`, and the free fn
  `derive_message_representative`.
- **Length-preservation ensures (2026-04-29)**: `generate_key_pair`
  carries `Seq.length ${signing_key}_future == Seq.length ${signing_key}
  /\ Seq.length ${verification_key}_future == Seq.length ${verification_key}`,
  established via the body admit.  This unblocks the
  `Instantiations.{Portable,Avx2,Neon}.Ml_dsa_{44,65,87}_` subtype
  coercion (slice-typed inner return → array-typed outer signature)
  for all 9 platform-instantiation modules and all 3 multiplexing
  modules.
- **Phase added**: above-trait C.9 (Ml_dsa_generic.fst promotion;
  16 modules total — 1 generic + 3 per-param + 9 platform-instantiations
  + 3 multiplexing).
- **Diagnosis**: top-level orchestrator chains every below-and-above-trait
  primitive (sample → matrix-multiply → reduce/invert → encode → hash).
  Discharging panic-freedom requires posts on all transitively-called
  modules — most below-trait Xof methods are still ADMIT, the encoding
  serialize/deserialize methods carry length-only posts, and the
  rejection-sample partial-acceptance count is not in the trait post.
  Body admit makes the function callable from the public API while
  the wrapper signatures sit ready for downstream typing.
- **Suggested mitigation**: Phase 4 work, ~6-10 hours.  Touchpoints:
  (1) Length-preservation ensures on Xof methods (mirrors `b68738411`).
  (2) Trait-level rejection-sample partial-acceptance count post.
  (3) Per-function precondition (signing key length, message length,
      randomness length, signature buffer length) sized by the
      param-set constants.
  (4) Per-function post: sign returns Ok with valid-length output,
      verify returns Ok on a self-consistent signature.

### Libcrux_ml_dsa.Sample (5 of 10 functions still admit)
- **File**: `src/sample.rs`
- **Status update (2026-04-29)**: 5 of 10 functions closed.
  - **Closed (no admit)**: `rejection_sample_less_than_field_modulus`,
    `rejection_sample_less_than_eta_equals_2`,
    `rejection_sample_less_than_eta_equals_4`,
    `rejection_sample_less_than_eta`, `inside_out_shuffle`.
    Closure recipe:
    (a) Refactor `cloop! { for ... in ....chunks_exact(N) }` to plain
        `for i in 0..randomness.len()/N { let chunk = &randomness[i*N..(i+1)*N]; ... }`.
    (b) Pre `*sampled_coefficients < 256` (or `*out_index < 256`
        for `inside_out_shuffle`).
    (c) Loop invariant
        `v sampled_coefficients <= 263 /\ (done \/ v sampled_coefficients < 256)`
        — this carries the trait pre `8 <= 263 - sampled_coefficients`
        through each iteration and propagates the post `v sampled_future <= 263`.
    (d) Bounds-only post: `v sampled_future <= 263` (matching the
        trait-side bounds-only convention).
    (e) For `inside_out_shuffle`, replaced
        `result[sample_at] = 1 - 2 * ((*signs & 1) as i32)` with
        `if (*signs & 1) == 0 { 1 } else { -1 }` — equivalent value,
        but avoids the u64→i32 cast that loses the [0,1] bound and
        triggers a spurious overflow check on the `2 * b` step.
    (f) Required `Seq.length out_future == Seq.length out`
        length-preservation conjunct on the three trait
        `rejection_sample_*` posts (see lane-split-protocol F-6 for
        below-trait cherry-pick action).
- **Remaining body admits (5)**: `sample_up_to_four_ring_elements_flat`,
  `sample_four_error_ring_elements`, `sample_mask_ring_element`,
  `sample_mask_vector`, `sample_challenge_ring_element` — all use
  `Shake128`/`Shake256` Xof methods.  The Xof method posts now carry
  length-preservation (commit before this), so these bodies should
  close once the per-function pre is sized appropriately
  (`re.len() >= dimension` / matching wrapper-buffer lengths) and
  the trait-helper-call shape is propagated through the loop. Phase
  2 work, ~2-3 hours.

## Active admits — below-trait branch (`ml-dsa-proofs` lane)

### Libcrux_ml_dsa.Simd.Traits.Specs.bounded_{add,sub}_{pre,post}
**Status**: closed (no admits) as of the 2026-04-28 final pass.
- All four SMTPat-bridge lemmas in `src/simd/traits/specs.rs:292-380` now
  carry real proofs:
  - `_pre` lemmas: two `reveal_opaque` calls (one for
    `Spec.Utils.is_i32b_array_opaque`, one for the relevant
    `add_pre`/`sub_pre`).
  - `_post` lemmas: same two reveals plus a per-lane lemma threaded via
    `Classical.forall_intro` to bridge the `forall (i: usize)` (from
    the unfolded `add_post`/`sub_post`) to the `forall (i: nat{i < 8})`
    quantifier needed by `is_i32b_array_opaque`. Wrapped in
    `#push-options "--z3rlimit 200 --fuel 1 --ifuel 1"`.
- The original soundness gap (constraint `b1+b2 ≤ u32::MAX` was looser
  than the conclusion's `i32::MAX`) is fully closed: bound is now
  `2147483647` (i32::MAX) and the proof actually goes through.

### Libcrux_ml_dsa.Simd.Avx2.Encoding.{Gamma1,T0,T1,Error} body admits
- **File / lines**:
  - `src/simd/avx2/encoding/gamma1.rs:50` (`serialize_when_gamma1_is_2_pow_17`)
  - `src/simd/avx2/encoding/gamma1.rs:118` (`serialize_when_gamma1_is_2_pow_19`)
  - `src/simd/avx2/encoding/gamma1.rs:211` (`deserialize_when_gamma1_is_2_pow_17_unsigned`)
  - `src/simd/avx2/encoding/gamma1.rs:243` (`deserialize_when_gamma1_is_2_pow_19_unsigned`)
  - `src/simd/avx2/encoding/t0.rs:67` (`serialize`)
  - `src/simd/avx2/encoding/t1.rs:13` (`serialize`)
  - `src/simd/avx2/encoding/error.rs:56` (`serialize_when_eta_is_2`)
  - `src/simd/avx2/encoding/error.rs:111` (`serialize_when_eta_is_4`)
- **Annotation**: `verification_status(panic_free)` plus
  `hax_lib::fstar!("admit ()")` mid-body (prefix). The `admit ()` puts F\*
  in a `False` context so all subsequent body assertions / out-of-bounds
  checks / strong-post discharges trivially succeed.
- **Phase added**: 2026-04-28 (Step 3 admit-parity path A from
  `next-session-plan.md`).
- **Diagnosis**: All eight encoding free functions carry strong
  bit-vector posts (`u8_to_bv`/`i32_to_bv`-shaped) that timed out
  individually under `--z3rlimit 140-800`. The dispatcher functions
  (`Operations::error_serialize`, etc.) do not require a length on
  `out`, so propagating `out.len() == N` upstream would have changed
  trait pre — disallowed by the hard rules. Mid-body `admit ()` matches
  the trait-side admit posture (T=🟡) without a trait-pre change.
- **Suggested mitigation**: Phase 2D / 3A iv work — extend
  `fstar-helpers/fstar-bitvec/BitVecEq.fst` for offset-encoded pack
  shapes, then carry `BitVecEq.int_t_array_bitwise_eq` posts through
  per-method to discharge the bit-vector identities. ML-KEM has the
  template for non-offset variants; gamma1/t0 widths use offset packing.

### Libcrux_ml_dsa.Arithmetic.power2round_vector body admit
- **File / lines**: `libcrux-ml-dsa/src/arithmetic.rs:54-72`
- **Annotation**: `verification_status(panic_free)` on
  `power2round_vector` and inner helper `power2round_one_ring_element`,
  plus `hax_lib::fstar!("admit ()")` at the top of the helper body.
- **Phase added**: 2026-04-28.
- **Diagnosis**: hax extracts the nested `for i in 0..t.len()` /
  `for j in 0..t[i].simd_units.len()` loops as an outer fold whose
  accumulator type is `(t_Slice, t_Slice)` with no length-preservation
  invariant. After the outer fold rebinds `t` inside the closure, F\*
  loses the refinement `i < t.len()` needed for `t[i]` and the inner
  fold call to `SIMDUnit::power2round`. Function post is `Prims.l_True`
  so the body admit has no upstream strength impact.
- **Suggested mitigation**: add a hax loop_invariant that re-asserts
  `Seq.length t == old_t_len` and `Seq.length t1 == old_t1_len`, or
  refactor the helper to take a slice index pair instead of a `&mut
  PolynomialRingElement`. ~20 min.

### Libcrux_ml_dsa.Simd.Portable.infinity_norm_exceeds u32-mask refactor
- **File / lines**: `libcrux-ml-dsa/src/simd/portable/arithmetic.rs:380-426`
- **Annotation**: none — proof passes after refactor (no admit).
- **Phase added**: 2026-04-28.
- **Diagnosis**: previously used `result | (normalized >= bound)` on
  `bool`s for FIPS 204 §3.6 constant-time semantics, but hax has no
  `BitOr<bool, bool>` instance (hacspec/hax#1204). Refactored the
  accumulator to `u32` (`violations | (normalized >= bound) as u32`)
  with `logor_lemma` to discharge `violations == 0 ==> ...` invariant
  preservation. Constant-time guarantee preserved.

### Libcrux_ml_dsa.Sample.inside_out_shuffle cloop refactor
- **File / lines**: `libcrux-ml-dsa/src/sample.rs:438-464`
- **Annotation**: none — proof passes after refactor.
- **Phase added**: 2026-04-28.
- **Diagnosis**: `cloop! { for byte in randomness.iter() { ... } }`
  extracted to `Iterator.f_fold` with a complex tuple-state closure,
  triggering a typeclass-resolution failure on `t_FnOnce`. Refactored
  to plain `for i in 0..randomness.len() { let byte = randomness[i]; ... }`.

### Libcrux_ml_dsa.Simd.{Portable,Avx2}.Arithmetic.reduce dedicated primitive
**Status**: refactored cleanly (no admits) at commit `3faaff641`.
The previous disjunctive pre on `shift_left_then_reduce` (accepting
either `SHIFT_BY == 13` with input ≤ 261631 or `SHIFT_BY == 0` with
input as Barrett-bound) was replaced by a dedicated `reduce` free
function in both Portable and AVX2 arithmetic modules, and
`Operations::reduce` now calls `arithmetic::reduce` per simd-unit.
`shift_left_then_reduce`'s pre is back to the simple `SHIFT_BY == 13`
form. The body admit added inside the SHIFT_BY=0 branch (1943e7f6e)
is gone. AVX2's `shift_left_then_reduce` is now a 2-line wrapper:
SIMD slli, then call `reduce`.

### Per-method Operations trait pre-condition tightening (2026-04-28)
**Status**: complete (no admits) — see `src/simd/traits.rs` for the
strengthened pres on use_hint, all rejection_sample_*, all gamma1_*,
commitment_serialize, error_serialize/deserialize, t0_serialize/deserialize,
t1_serialize/deserialize, and reduce. Each pre uses opaque packaging
(reuses `Spec.Utils.is_i32b_array_opaque`; new `is_binary_array_8_opaque`
for use_hint's hint binary check; defined in `src/simd/traits/specs.rs`
with intro/lookup SMTPat lemmas in the ML-KEM `bounded_pos_i16_array`
style). All Portable + AVX2 impls mirror the strengthened pres.

### Libcrux_ml_dsa.Simd.Portable + Simd.Avx2 impl-Operations method body admits
- **File / lines**: `libcrux-ml-dsa/src/simd/portable.rs:34-300` and
  `libcrux-ml-dsa/src/simd/avx2.rs:30-360` (Operations impl blocks).
- **Annotation**: `#[hax_lib::attributes]` on impl block;
  `#[requires]/[ensures]` on each method matching trait pre/post; body
  begins with `hax_lib::fstar!("admit ()")` for the methods listed below.
  Resolved (no admit) so far: Portable add/subtract (free fn post identical
  to trait), Portable reduce (Step 7 — `c91f0b413`), AVX2 reduce
  (Step 7 — `aa51e5ef9`), AVX2 add/subtract (Step 8 — this session).
- **Remaining methods with body admits** (AVX2 only — Portable mostly
  closed already): `zero`, `from_coefficient_array`, `to_coefficient_array`,
  `decompose`, `compute_hint`, `use_hint`,
  `montgomery_multiply`, all
  `rejection_sample_*`, all encoding methods, `ntt`, `invert_ntt_montgomery`.
  Cleared in Step 9: `infinity_norm_exceeds` (both), `power2round` (both),
  `montgomery_multiply` (Portable; AVX2 still admits — needs a bridging
  lemma `lemma_mont_mul_bound_and_mod_q` in `Commute.Chunk.fst`),
  `shift_left_then_reduce` (both — trait post relaxed to mod-q congruence).

### F-1 use_hint Portable impl close (resolved 2026-04-28, Step 11 Track 1)
**Status**: `admit ()` bodies in both paired commute lemmas
replaced with full proofs (commit `32ae8a9ce`):
- `lemma_use_one_hint_bound`: proved via new
  `lemma_spec_decompose_r1_bound` (Spec.MLDSA.Math.decompose's r1
  component lies in `[0, 4190208/g)` for any int input;
  case-splits on `r_g_raw > g` and on the special-case
  `r_q - r_g = q-1`, both excluded by upper-bound argument).  hint=1
  branch closes via `FStar.Math.Lemmas.lemma_mod_lt`.
- `lemma_use_hint_lane_commute_conditional`: proved via two
  sub-lemmas:
    1. `lemma_mod_pm_eq_mod_p` — `Hacspec.Arithmetic.mod_pm a m`
       v-image equals `Spec.Utils.mod_p (v a) (v m)` under non-negative
       `a` and positive even `m`; the i64 `((a%m)+m)%m` chain
       collapses since `%!` is Euclidean.
    2. `lemma_decompose_bridge` — `Hacspec.Arithmetic.decompose r g`
       v-image agrees with `Spec.MLDSA.Math.decompose (v g) (v r)`
       under `v r ∈ [0, q)` (output layouts differ; v-image agrees).
  Then case-splits on hint and `r0 > 0`; the `+m then %! m`
  re-correction in the Hacspec hint=1, r0≤0 branch collapses to
  `(r1-1) % m` since `%!` is already Euclidean.  Total ~85 lines.

### Step 11 Track 2: Portable decompose + compute_hint impl scaffolding (2026-04-28)
**Status**: both impl bodies upgraded from single top-level
`admit()` to paired-lemma scaffolding (commit `77a87ce4b`).
Verifies under impl_1 in 16s @ rlimit 80 (used 68/80).
- `lemma_decompose_bound`: real proof, reusing
  `lemma_spec_decompose_r1_bound` plus inline `mod_p` bound argument
  for r0 ∈ [-g, g].
- `lemma_decompose_lane_commute_conditional`: real proof, packaging
  Track-1's `lemma_decompose_bridge` in the `==>`-conditional shape.
- `lemma_compute_one_hint_bound`: trivial — Spec returns 0 or 1.
- `lemma_compute_hint_lane_commute_conditional`: **closed in Step 13
  Track A** (commit pending) — body collapses to a single
  `reveal_opaque (`%TS.compute_hint_lane_post)` after F-4 cherry-pick
  switched the post's RHS from `make_hint`-citing to
  `compute_one_hint`-citing.  The `introduce ... with hyp. admit ()`
  block is gone.
- `lemma_compute_hint_bound`: `repeati`-induction on the popcount
  (real proof) — proves Spec sum ≤ 8 under binary lane hypothesis.

### Step 14 Track D-2: encoding `*_deserialize` trait bodies (2026-04-29)
**Resolved (admit removed):**
- Portable `Operations::t1_deserialize` (commit `62a50deeb`) — free
  fn ensures + loop_invariant + `logand_mask_lemma` SMTPat after
  mask normalization tactic.
- AVX2 `Operations::t1_deserialize` (commit `62a50deeb`) — tightened
  free fn ensures from `j%32 > 10` to `j%32 >= 10`, then
  `i32_bit_zero_lemma_to_lt_pow2_n_weak 10` bridge in trait body.
- Portable `Operations::t0_deserialize` (commit `10b15d325`) — free
  fn + `change_t0_interval` ensures with conditional half-open bound;
  rlimit 300 + split_queries.
- AVX2 `Operations::t0_deserialize` (commit `10b15d325`) — added
  per-lane half-open bound conjunct to existing `deserialize_post`,
  discharged via existing body proof structure; trait body bridges
  via `f_repr ↔ to_i32x8` SMTPat assert + opaque reveal.
- Portable `Operations::gamma1_deserialize` (commit `4ec0e9f50`) —
  per-eta deserialize_when_* helpers + wrapper deserialize ensures;
  rlimit 600 + split_queries.  For γ1=2^19, added defensive
  `coefficient1 &= GAMMA1_TIMES_2_BITMASK` (mathematically a no-op
  since the OR of disjoint bit ranges already lies in [0, pow2 20))
  so the same SMTPat path discharges the bound; C output unchanged.
- AVX2 `Operations::gamma1_deserialize` (commit `4ec0e9f50`) — added
  per-lane closed bound conjunct to existing `deserialize_post`,
  same template as t0_deserialize AVX2.

**Resolved (admit removed) — additional after F-14 trait post relax:**
- Portable `Operations::error_deserialize`,
  AVX2 `Operations::error_deserialize` (commit `c1e8e2883`) —
  cherry-picked above-trait `e055bf9c0` (F-14 audit), which relaxes
  the trait post from canonical-symmetric `[-eta, eta]` to FIPS 204
  BitUnpack range `[-5, 2]` (eta=2) and `[-11, 4]` (eta=4).
  Per-eta free fn ensures added to
  `src/simd/portable/encoding/error.rs::deserialize_when_eta_is_*`
  + dispatcher; logand mask normalized via
  `assert (mk_i32 7 == mk_i32 (pow2 3) -! mk_i32 1) by ...` tactic
  to fire `logand_mask_lemma` SMTPat.  AVX2 deserialize ensures
  strengthened with per-lane `to_i32x8` value bound; per-eta
  `i32_bit_zero_lemma_to_lt_pow2_n_weak n` bridge invoked
  (n=3 for eta=2, n=4 already called for eta=4).

### Step 13 Track D-1: encoding `*_serialize` impl bodies (2026-04-29)
**Resolved (admit removed):**
- Portable `Operations::t1_serialize`, `Operations::error_serialize`
  trait bodies — discharged via length-pres ensures added to
  `t1::serialize` and `error::serialize`.
- AVX2 `Operations::t1_serialize`, `Operations::error_serialize`
  trait bodies — AVX2 free fns already advertise length-pres;
  `f_repr ↔ to_i32x8` bridge auto-discharged by SMTPat.

**Blocked (admit retained):**
- Portable `Operations::commitment_serialize`,
  `Operations::t0_serialize` trait bodies — F-7 boundary off-by-one
  in `is_pos_array_opaque l` (uses `<= l` where free fn `bounded x d`
  requires `< pow2 d`).  Z3 non-deterministically fails the call's
  requires discharge.  Awaiting above-trait fix (tighten predicate
  or change call sites to `pow2 d - 1`).
- AVX2 `Operations::t0_serialize` trait body — F-6: trait pre uses
  non-negative form `is_pos_array_opaque (pow2 13)` but AVX2 free
  fn requires *centered* form (the `4096 - x` shift).  Awaiting
  above-trait fix (revert F-3 for t0 only — use
  `is_i32b_array_opaque (pow2 12)` instead).

**Cross-method scope still open**: AVX2 use_hint, decompose,
compute_hint bodies remain top-level `admit()` — Track 3 (stretch,
deferred) needs strengthening of the AVX2 free-fn posts (which carry
`#push-options "--admit_smt_queries true"`) before the F-1 paired
template can be applied.

### Step 11 Track 4: AVX2 montgomery_multiply impl close (2026-04-28, RESOLVED)
**Status**: AVX2 `Operations::montgomery_multiply` impl body closes
without admits.  `Simd.Avx2.fst` verifies in 12.5s; impl_1 in 4.5s
@ rlimit 80 (used 8.4/80).
- `lemma_mont_mul_bound_and_mod_q` (new in `Commute.Chunk.fst`):
  centered-bound + mod-q congruence on `Spec.MLDSA.Math.mont_mul`.
  **Real proof** (no admit) — ~80-line i32/i64 Montgomery correctness
  argument, mirror of `Spec.Utils.lemma_mont_mul_red_i16_int`
  (`libcrux-ml-kem/proofs/fstar/spec/Spec.Utils.fst:505`) adapted to
  i32/i64 with shift 32, q=8380417, q'=58728449, R^-1=8265825.  Key
  fact `(58728449 * 8380417) % pow2 32 == 1` discharged via
  `assert_norm`; bound + mod-q split via `Spec.Utils.lemma_*_at_percent`
  helpers and `FStar.Math.Lemmas.lemma_div_exact / lemma_mod_*`.
  Cold first-verify takes ~330s without hints (heavy non-linear arith);
  hint-cached re-verify <1s.
- AVX2 `montgomery_multiply` impl: per-lane
  `lemma_mont_mul_bound_and_mod_q` on `to_i32x8` outputs, then
  `lemma_montgomery_multiply_lane_intro` to package into
  `montgomery_multiply_lane_post`.  Reveal `Spec.MLDSA.Math.mod_q`
  for the `mod_q` congruence conjunct, reveal
  `is_i32b_array_opaque` for the bound conjunct.

### Step 9.7 use_hint pre-audit finding (2026-04-28)

`Operations::use_hint` trait pre is `is_i32b_array_opaque (FIELD_MAX) (f_repr simd_unit)`,
which gives `-q+1 ≤ v input ≤ q-1` per lane.  But the trait post
`use_hint_lane_post` is conditional on `v input >= 0 /\ v input < q`,
and Hacspec/Spec.MLDSA.Math `use_one_hint` semantics agree only on
`[0, q)` representatives.  An unconditional commute lemma
(`lemma_use_hint_lane_commute`) was written and verified standalone in
`Commute.Chunk.fst`, but its `requires v input >= 0 /\ v input < q`
cannot be discharged from the trait pre alone — the impl side either
needs to (a) normalise input via `if r < 0 then r + q else r` before
delegating, or (b) the trait pre needs to tighten to require
`is_i32b_array_opaque (q-1)/2` (or equivalent) plus a positivity or
centred-rep tag.  Lemma reverted; impl admit retained.

This is also a Tier-1.5 (bounds-completeness) audit finding: the
use_hint pre is "FIELD_MAX-bounded" but use_hint actually needs
"valid representative", which is strictly stronger.  The same gap
likely affects `decompose` (whose post is also `[0, q)`-conditional).
- **Phase added**: 2026-04-28 (Step 5b extension).
- **Diagnosis**: After lifting Simd.Portable.fst + Simd.Avx2.fst from
  ADMIT to CHECK (Step 5), the impl methods extracted with `f_*_pre =
  true; f_*_post = true`. To carry strong trait posts to downstream
  callers (the thin-wrapper rule), the impl methods now declare exact
  trait-side `#[requires]/[ensures]`. The body admits are needed because:
  (1) some Portable underlying free fns prove a strictly weaker post than
  the trait (e.g. `infinity_norm_exceeds`); (2) all AVX2 free fns operate
  on Vec256 (the bitvec model) while the trait posts cite f_repr (i32x8
  view) — bridging the two needs per-method translation lemmas.
- **Template**: Step 7 + Step 8 established the AVX2 thin-wrapper template:
  (1) strengthen the underlying AVX2 free fn post to mention `to_i32x8`
  per lane (often free via existing `mm256_*_lemma` SMTPats);
  (2) add a per-lane bridge lemma in `Hacspec_ml_dsa.Commute.Chunk.fst`
  linking the intrinsic op shape to `Libcrux_ml_dsa.Simd.Traits.Specs.*_post`;
  (3) in the impl method, save `_orig`, call the free fn, reveal opacity
  of pre/post, and apply the bridge lemma per-lane via `Classical.forall_intro`.
- **Suggested mitigation**: continue applying the Step 7+8 template
  per-method. Estimate 15-25 min per method.

### Libcrux_ml_dsa.Simd.Avx2.f_reduce body admit (RESOLVED)
- **Resolution**: closed in this session via three pieces:
  1. `Spec.Intrinsics.fsti` — added `mm256_storeu_si256_i32_lemma` (and
     length lemma) as SMTPat axioms bridging `Seq.index ... i` to
     `to_i32x8 vec (mk_u64 i)`.  Self-contained in mldsa-only spec; no
     change to the shared `Libcrux_intrinsics.Avx2.fst`, so ml-kem is
     unaffected.
  2. `to_coefficient_array` ensures lifted (Rust source +
     `Libcrux_ml_dsa.Simd.Avx2.Vector_type.fst`) to carry per-lane
     content guarantee `Seq.index out_future i == to_i32x8 value.f_value (mk_u64 i)`.
  3. `Hacspec_ml_dsa.Commute.Chunk.fst` — proved
     `lemma_barrett_red_bound_and_mod_q` bridging the raw
     `Spec.MLDSA.Math.barrett_red` shape to (centered Barrett bound) +
     (raw `% q` congruence).  rlimit 200, opacity reveals +
     `FStar.Math.Lemmas.lemma_mod_sub`.
  4. `src/simd/avx2.rs:363-368` reduce body now uses the
     loop_invariant + after-loop `Classical.forall_intro` (over
     `j<32 / k<8`) pattern matching the Portable template
     (`c91f0b413`).  No admits.
- **Template value**: Pieces 1+2 unblock all 21 AVX2 trait methods
  whose posts cite `f_repr`.  Step 8/9 (`add` / `subtract` /
  `montgomery_multiply` / `shift_left_then_reduce` / `power2round` /
  `decompose` / `compute_hint` / `use_hint` / `infinity_norm_exceeds`)
  in subsequent sessions: the Vec256↔f_repr bridge from Piece 1 is
  now in place; only per-method commute lemmas remain.

### Libcrux_ml_dsa.Simd.Traits.ntt (per-poly post)
- **File / lines**: `libcrux-ml-dsa/src/simd/traits.rs:158-172` (Operations::ntt)
- **Annotation**: bounds-only post retained; no per-poly forall32-with-Hacspec_ml_dsa.Ntt.ntt conjunct added
- **Phase added**: 1
- **Diagnosis**: Tier-3 chain across 8 layers with BitRev₈ zeta indexing — the
  ML-KEM USER-2 analog with one extra layer. A per-poly post would require
  composing 8 layer-step lemmas with subtle indexing; this is Z3-incompatible
  in the trait-level 20-min budget. The bounds-only post is sufficient for
  upstream callers that only need the FIELD_MAX bound.
- **Suggested mitigation**: USER lane. Build per-layer commute lemmas in
  `specs/ml-dsa/proofs/fstar/commute/Hacspec_ml_dsa.Commute.Chunk.fst`
  (Phase 2F prerequisite), then chain into a `lemma_ntt_full_commute` after
  ML-KEM's analog lands as a template.
- **Template value**: closes the NTT layer of the proof; INVNTT and
  ntt_multiply compositions are direct adaptations.

### Libcrux_ml_dsa.Simd.Traits.invert_ntt_montgomery (per-poly post)
- **File / lines**: `libcrux-ml-dsa/src/simd/traits.rs:175-187`
- **Annotation**: bounds-only post retained
- **Phase added**: 1
- **Diagnosis**: Analogous to NTT — Tier-3 chain with the additional
  Montgomery-domain → standard-domain conversion at exit.
- **Suggested mitigation**: USER lane, after `lemma_ntt_full_commute` lands.
- **Template value**: matches NTT template once NTT is proven.

### Libcrux_ml_dsa.Simd.Traits.rejection_sample_* (per-byte step posts)
- **File / lines**: `libcrux-ml-dsa/src/simd/traits.rs:108-118`
- **Annotation**: bound + count-bound post; per-element citation of
  `Hacspec_ml_dsa.Encoding.coeff_from_three_bytes` /
  `coeff_from_half_byte` deferred (lane post predicates exist in
  `Libcrux_ml_dsa.Simd.Traits.Specs` but the trait post does not connect
  out[i] to the originating randomness chunk).
- **Phase added**: 1
- **Diagnosis**: The trait method consumes a length-24 (or length-4) byte
  buffer and outputs accepted coefficients into `out`. A per-byte step
  predicate would have to thread a loop index `j` through randomness
  chunks and witness the partial-acceptance count — non-trivial in a
  trait-level post and exceeds the 20-min budget.
- **Suggested mitigation**: agent-lane Phase 2 work. Add a
  loop-invariant-style relational predicate citing `coeff_from_*` once
  the impl proof is being driven in `simd/portable/sample.rs`.

### Libcrux_ml_dsa.Simd.Traits.{gamma1,commitment,error,t0,t1}_{serialize,deserialize}
- **File / lines**: `libcrux-ml-dsa/src/simd/traits.rs:120-156`
- **Annotation**: length-preservation + bound conjuncts only;
  `BitVecEq.int_t_array_bitwise_eq` round-trip equation against
  `Hacspec_ml_dsa.Encoding.{simple_bit_pack,bit_pack,simple_bit_unpack,bit_unpack}`
  deferred.
- **Phase added**: 1
- **Diagnosis**: Bit-vector equivalence via `BitVecEq.int_t_array_bitwise_eq`
  is the canonical ML-KEM template, but the encoding-side gamma1/t0 widths
  use offset-encoded bit_pack (each value `v` packed as `b - v` over a
  signed range), which the ML-KEM template does not cover. The full
  predicate can be added once the helpers in
  `fstar-helpers/fstar-bitvec/BitVecEq.fst` are extended for offset packing.
- **Suggested mitigation**: agent-lane Phase 2D. Mirror the ML-KEM
  `serialize_post_N` / `deserialize_post_N` shape, with offset-aware
  variants for gamma1/t0/error.

---

## Pre-existing failures (out of scope for the ML-DSA proof sprint)

(none currently — Funarr was the only one and is resolved at `42d4a3347`)
