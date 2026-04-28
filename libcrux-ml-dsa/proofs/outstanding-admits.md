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

## Active admits

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
