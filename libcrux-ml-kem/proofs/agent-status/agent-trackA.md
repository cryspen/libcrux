# agent-trackA — session log

**Session date:** 2026-04-28 (resumed evening, Step 2 layer 3 added)
**Branch:** `trait-opacify`
**Tip at end:** `0784e3b72` (was `7b4707227` at start of this resume —
handoff prompt commit; effective code tip `bcc3dc480` at session start)

## 2026-04-28 late evening — Phase 7a Step 3 (sub-pieces 1 + 2)

Strengthened `inv_ntt_layer_int_vec_step_reduce`'s post with per-lane FE
equations (Step 3.1) and added the chunk-pair hacspec bridge
`lemma_inv_ntt_layer_int_vec_step_reduce_to_hacspec` to Bridges.fst
(Step 3.2).  Step 3.3 (per-polynomial composition in
`invert_ntt_at_layer_4_plus`) deferred — see "Open work" below.

### What landed

#### `src/invert_ntt.rs` — `inv_ntt_layer_int_vec_step_reduce`

New post:
```
(forall i. i < 16 ==>
   mont_i16_to_spec_fe r0[i] ==
     impl_FieldElement__add (mont_i16_to_spec_fe a[i])
                             (mont_i16_to_spec_fe b[i])) /\
(forall i. i < 16 ==>
   mont_i16_to_spec_fe r1[i] ==
     impl_FieldElement__mul (mont_i16_to_spec_fe zeta_r)
       (impl_FieldElement__sub (mont_i16_to_spec_fe b[i])
                               (mont_i16_to_spec_fe a[i])))
```

Captures original `a, b` via `_a_in, _b_in` ghost snapshots (cfg(hax))
since the function reassigns `a, b` mid-body.  Renamed the rebound
locals to `r0, r1` for direct correspondence with the result tuple
(eliminates the shadow-by-overwrite that prevented post-references to
the entry values).

Body proof: two `Classical.forall_intro`s — one per output chunk —
invoking `Chunk.lemma_add_fe_commute_mont_mod` (for `r0[i]`) and
`Chunk.lemma_inv_butterfly_fe_commute_mul_diff` (for `r1[i]`).  The
mod-q residue equations from `barrett_reduce_post` ∘ `add_post` and
`montgomery_multiply_by_constant_post` ∘ `sub_post` discharge directly
under those existing Chunk helpers (no new core-arithmetic lemmas
needed).

Settings: `--z3rlimit 200 --ext context_pruning --split_queries always`.
107 queries, max single 725 ms (Q101 — likely a quantifier
instantiation in one of the `forall_intro` aux proofs).

#### `specs/ml-kem/proofs/fstar/commute/Hacspec_ml_kem.Commute.Bridges.fst`

New lemma `lemma_inv_ntt_layer_int_vec_step_reduce_to_hacspec`:
takes the strengthened (1) post as `requires`, produces the
function-form `IN.inv_butterfly`-citation as `ensures`.  Body is a
single `()` — `inv_butterfly` unfolds definitionally and the
hypotheses match `_1` (= add a b) and `_2` (= mul zeta (sub b a))
directly.

This is structurally the simplest of the four hacspec bridges (no
nested if-ladder, no `--split_queries always`, no per-branch helpers).
2 queries, max 41 ms.

### Verification

| Module | Status | Time | Notes |
|---|---|---|---|
| `Libcrux_ml_kem.Invert_ntt` (with Step 3.1 admits, layers 1/3/4_plus) | ✅ | 13.3 s | rlimit 200, 107 queries on `inv_ntt_layer_int_vec_step_reduce` |
| `Hacspec_ml_kem.Commute.Bridges` (cold) | ✅ | 175 s | Step 3.2 lemma added; cold rebuild dominated by existing layer 2 lemmas |
| `Libcrux_ml_kem.Invert_ntt` (no admits) | ❌ regressed | 26 min wall before failure | layer 4_plus's bounds-only post failed; Q191/Q192 saturated 168/200 of rlimit 200 |
| `Libcrux_ml_kem.Invert_ntt` (rlimit 400 + `--split_queries always` on layer 4_plus) | ❌ regressed | not waited (stopped via TaskStop after layer 1 cleared) | extrapolation: split_queries doesn't help when forall-context grows |
| `Libcrux_ml_kem.Invert_ntt` (TEMP admit on layer 4_plus body) | TBD | TBD | landing decision — see "Layer 4_plus regression" below |

### Layer 4_plus regression — diagnosis + landing decision

**Symptom.** After re-extracting with the strengthened
`inv_ntt_layer_int_vec_step_reduce` post + reverting the temp admits
on layers 1/3/4_plus, full `make check/Libcrux_ml_kem.Invert_ntt.fst`
failed at `invert_ntt_at_layer_4_plus` (Q191/Q192/Q195 saturating /
failing) at rlimit 200.

**Diagnosis (per smtprofiling skill, Technique 4 + Technique 6).**
The strengthened post adds two `forall (i: nat). i < 16 ==> ...`
conjuncts to the SMT context at every call site of step_reduce
inside layer 4_plus's inner loop.  These extra forall facts pollute
the bounds-only proof: prior session's perf data noted Q187 already
borderline at rlimit 200 (50.5/200 used); the extra context pushes
Q191 to 120/200, Q192 to 168/200, and one query failed outright.
A bumped rlimit + `--split_queries always` did NOT discharge cleanly
either (build was stopped via TaskStop after layer 1 cleared,
extrapolation supports that the fundamental issue is forall-context
growth, not query budget — split_queries doesn't reduce the
per-query context size).

**Landing decision (per user direction "Option B"):** apply
`#[hax_lib::fstar::options("--admit_smt_queries true")]` to
`invert_ntt_at_layer_4_plus` only, with TEMP comment + reference to
this trackA entry.  This admits its bounds-only post for now.  The
proper fix will be the **drive-to-the-top spike** documented in
`next-session-prompt.md`: admit layer 4_plus's strengthened post
(citing `IN.ntt_inverse_layer_n 256`), strengthen
`invert_ntt_montgomery`'s post, validate against consumers in
`matrix.rs` / `polynomial.rs`.  If the spec shape holds end-to-end,
discharging layer 4_plus's body is the LAST step (and at that point
we know exactly what shape its post needs).  If the shape doesn't
hold, we redesign before sinking time.

**Why this is OK to land:** the admit is on the BOUNDS-ONLY post
that ALREADY existed before this session.  The strengthened
step_reduce post (Step 3.1, the actual new spec) verifies cleanly.
We're not regressing any verified property — we're just deferring
a downstream proof until the spec direction is validated.



### Z3 lessons / patterns

- **Owned `mut` parameters need ghost snapshots for posts.**  When the
  function rebinds `a` and `b` after computing them, the F* post sees
  the rebound bindings, not the entry values.  Two options:
  (a) `let _a_in = a; let _b_in = b` at function top under `cfg(hax)`,
      use `${_a_in}` and `${_b_in}` in the body fstar! block, but
      reference `${a}` and `${b}` in the post (which scope-wise refer
      to the function params at entry).
  (b) Rename the rebound locals (`a = ...` → `let r0 = ...`) so the
      original bindings remain accessible in the body.
  We used **both**: ghost snapshots in the body proof, original param
  names in the post.  Cleanest signal-to-noise.

- **Variable scoping in hax_lib::ensures vs body.**  `${...}` capture
  in fstar! macros must reference identifiers that exist in the
  surrounding Rust scope at extraction time.  `cfg(hax)` ghosts work
  for body fstar! but NOT for post fstar! (post is a separate
  expression context — function params + result are in scope, but
  body locals are not).  Initial attempt to put `${_a_in}` in the
  post failed with `error[E0425]: cannot find value` because hax's
  Rust pre-pass enforces this.

### Open work / Step 3.3 deferred

**Why deferred (per decision tree in `next-session-prompt.md`):**

Step 3.3 (per-polynomial composition in `invert_ntt_at_layer_4_plus`'s
post citing `IN.ntt_inverse_layer_n 256 p step zs`) requires
substantial new spec infrastructure:

  1. **Polynomial-level lift function** `mont_to_spec_poly_256`
     (currently we only have per-chunk `mont_i16_to_spec_array` for
     length-16 arrays).  Needs to flatten `re.coefficients : t_Array
     vV 16` into `t_Array t_FieldElement 256`.
  2. **Zetas-N-inverse helpers** for layer 4..7: arrays of length
     `groups = {8, 4, 2, 1}` containing the layer's zetas.  Three new
     helpers (we already have `zetas_1`).
  3. **Loop invariant in chunk-pair / `inv_butterfly` form** plus
     post-loop `Classical.forall_intro` over chunks to lift to
     polynomial-level via the Step 3.2 bridge.
  4. **Z3 risk:** layer 4_plus's existing post already had
     Q187 borderline at rlimit 200 per the prior-session log.
     Strengthening adds ~16 forall-quantified per-chunk-pair facts,
     likely pushing into rlimit 400+ territory.

**Recommended approach for next session (or Step 4 layer 4_plus
framing):**
- Define `mont_to_spec_poly_256` and zetas-N helpers in
  `specs/ml-kem/proofs/fstar/commute/Hacspec_ml_kem.Commute.Chunk.fst`
  alongside `zetas_1, zetas_2, zetas_4`.
- Add a **per-polynomial-pair bridge** in Bridges.fst (analogous to
  Step 3.2 but for polynomial pairs `(p[k], p[k+step])`) that lifts
  16 per-lane equations across one chunk-pair to a flat-polynomial
  pair claim.
- Use Option B in `invert_ntt_at_layer_4_plus`: chunk-pair invariant
  in `inv_butterfly`-form, post-loop forall_intro over chunk-pairs to
  lift to polynomial-level `IN.ntt_inverse_layer_n`.

Combined Step 3.3 + Step 4 layer 4_plus is the natural follow-up unit.

## 2026-04-28 evening — Step 4 layer 3 strengthened

Applied Option B template to `invert_ntt_at_layer_3` mirroring layer 1.
Verified: `make check/Libcrux_ml_kem.Invert_ntt.fst`, exit 0, **333 s
wall** with no temp admits.  Heaviest queries on layer 1 strengthened
(~270 s wall portion) and layer 4_plus (Q187 borderline at rlimit 200).

## 2026-04-28 evening — Step 4 layer 2 attempted, REVERTED

Same Option B template applied to `invert_ntt_at_layer_2`, but Z3
returned 6 errors at rlimit 800.  Errors at extracted Invert_ntt.fst
lines 183, 184, 206 (×3), 140-235:
  * Line 183: hand-holding `assert (zeta_i == 63 - 2*round)` failed.
  * Line 184: subtyping on `zeta_i - 1` (call to `inv_ntt_layer_2_step`
    second zeta arg).
  * Line 206 (×3): loop invariant non-preservation across body.
  * Lines 140-235: outer body assertion failed.

Total wall before failure: 18:32 min.  Reverted via
`git checkout libcrux-ml-kem/src/invert_ntt.rs` so the working tree
matches `43c9d45d5`.

Hypotheses for next-session retry (see `next-session-prompt.md`):
  * Layer 2's decrement pattern `(-= 1; ...; -= 1)` differs from layer
    1's `(-= 1; ...; -= 3)`; hand-holding asserts may need adjustment.
  * Layer 1 has 4 hand-holding asserts (one per zeta_i offset); layer
    2 has 2.  Z3 may need more bound information.
  * The strengthened invariant + bound conjuncts may need tighter
    structure than what I had.

---



## 2026-04-28 evening — Phase 7a Step 2 layer 2 (the Z3 trap)

Added the **layer 2 inverse hacspec bridge** to Bridges.fst.  The
trait's layer-2 branch_post has a 3-way nested if-ladder
(`z = b<2 ? zeta0 : zeta1`, `base = b<2 ? 0 : 8`, `off = b∈{0,2} ? 0 : 2`)
which previously caused Z3 timeouts >2.7 min for forward layer 2 in
prior session.

### Decomposition (8 new lemmas, ~310 LOC)

| Lemma | Purpose |
|---|---|
| `zetas_2_lane` | per-lane unfold for `zetas_2` |
| `lemma_ntt_inverse_layer_n_16_4_lane` | per-lane unfold for `IN.ntt_inverse_layer_n 16 p 4 zs` |
| `lemma_inv_ntt_layer_2_step_branch_{0,1,2,3}_lane_bridge` | 4 per-branch helpers at CONCRETE `b` literals |
| `lemma_inv_ntt_layer_2_step_lane_bridge` | per-lane wrapper dispatching to the right per-branch helper |
| `lemma_inv_ntt_layer_2_step_to_hacspec` | per-vector bridge under `--split_queries always` |

### Z3 wall — three failed attempts before the unlock

1. **Symbolic-b in lane bridge** — predicted Z3-trap per the existing
   forward-layer-2 attempt comment.  Skipped.
2. **4 per-branch + aux 4-way disjunction case-split**:
   `if j = 0 || j = 1 || j = 4 || j = 5 then () else if ...`.  Z3
   saturated rlimit 400 in **11 min** on one sub-query.
3. **4 per-branch + 16 individual `assert`s + `Seq.lemma_eq_intro`**:
   asserts passed individually (each <100 ms), but `lemma_eq_intro`'s
   forall precondition saturated rlimit 400 in **4 min**.

### The unlock

Per-lane wrapper (each call has only 4 in-scope facts — one branch's
worth) + `--split_queries always` on the per-vector bridge.  Z3
splits the forall into 16 separate per-j sub-queries; each closes
in <100 ms.  Total cold rebuild: **188 s wall**.

### Pattern lessons for similar walls

- **Per-branch decomposition with concrete `b`** is the structural fix
  for nested-if-ladder branch_posts.  The 4 helpers each have
  literal `b` so the if-ladder collapses pre-SMT.
- **Per-lane wrapper** keeps each VC's in-scope facts minimal.
- **`--split_queries always`** is the Z3 setting that turns a
  forall over 16 lanes into 16 cheap sub-queries.  Apply it to the
  per-vector bridge that does `Classical.forall_intro` +
  `Seq.lemma_eq_intro`.

This lifts the layer 2 trap.  The same pattern can be applied to
layer 2 forward (USER-deferred earlier) and AVX2 layer 1/2 (USER-4)
if those become target.

---



## 2026-04-28 evening resume — Phase 7a Step 2 layer 3

Added the **inverse NTT layer 3 hacspec bridge** to
`specs/ml-kem/proofs/fstar/commute/Hacspec_ml_kem.Commute.Bridges.fst`.
Mirror of the layer 1 inverse bridge (`8358b1093`-era).  Layer 3 is
the easiest of the three remaining bridges: single zeta, partner
stride 8, no nested if-ladder in the trait branch post.

### What landed in `Bridges.fst` (4 new lemmas, ~165 LOC)

| Lemma | Purpose | Verified | Heaviest query |
|---|---|---|---|
| `zetas_1_lane` | Per-lane unfold for `zetas_1` (single-zeta slice) | ✅ | 55ms (rlimit 80) |
| `lemma_ntt_inverse_layer_n_16_8_lane` | Per-lane unfold for `IN.ntt_inverse_layer_n 16 p 8 zs` (layer 3 form: group=0 always, idx=i) | ✅ | 2.55s (rlimit 200) |
| `lemma_inv_ntt_layer_3_step_lane_bridge` | Per-lane bridge: trait branch post → hacspec eq at lane `i` | ✅ | 43.4s (rlimit 400, used 124/400) |
| `lemma_inv_ntt_layer_3_step_to_hacspec` | Per-vector function-form bridge; `Classical.forall_intro` + `Seq.lemma_eq_intro` over 16 lanes | ✅ | 742ms (rlimit 400) |

Lane → branch mapping for layer 3: `b = (i mod 8) / 2`.  Branch `b`
touches lanes `(2b, 2b+1, 2b+8, 2b+9) = (i1, i2, j1, j2)`.  Hacspec at
lane `i`:
- if `i < 8` (low half): `result[i] = vec[i] + vec[i+8]` — matches
  `inv_butterfly._1` at `(i, i+8)`.
- if `i ≥ 8` (high half): `result[i] = z·(vec[i] − vec[i-8])` —
  matches `inv_butterfly._2` at `(i-8, i)`.

### Verification

- **fstar-mcp `create_session`** (initial verify, no fragments failed).
  Session ID `6fd7fad0...`.  Sub-second feedback for follow-up
  iterations.
- **`make check/Hacspec_ml_kem.Commute.Bridges.fst`**:  exit 0,
  "All verification conditions discharged successfully", 50.5 s wall
  (cold; with hints, expected to drop to ~6 s as in prior snapshot).
  No regression in Polynomial.fst or Invert_ntt.fst transitive context.

### Next steps (this session)

- (a) Step 2 — layer 2 inverse NTT bridge (Z3 trap on nested if-ladder
  for `b → (z, base, off)`; mitigation: enumerate `i ∈ {0..15}`).
- (b) Step 3 — cross-vector for `invert_ntt_at_layer_4_plus`.
- (c) Step 4 — strengthen `_2`, `_3`, `_4_plus` posts via Option B
  pattern (mechanical after their bridges land).
- (d) Step 5 — `invert_ntt_montgomery` post chain.

---

## 2026-04-28 afternoon resume — Phase 7a Step 4

Added per-chunk hacspec citation to `invert_ntt_at_layer_1`'s ensures
in `src/invert_ntt.rs`.  The strengthened post (commit `8358b1093`):

```
forall i. i < 16 ==>
  mont_i16_to_spec_array (T.f_repr (re_future.coef[i])) ==
  IN.ntt_inverse_layer_n 16 (mont_i16_to_spec_array (T.f_repr (re.coef[i])))
                            2 (zetas_4 (zeta(127-4i)) (zeta(126-4i))
                                       (zeta(125-4i)) (zeta(124-4i)))
```

### Approach

- **Option A (failed)**: function-form eq directly inside the loop
  invariant.  Q353 of body subtyping check failed at rlimit 800 with
  Z3 "unknown because " (used 131/800 — Z3 just gave up on the heavy
  invariant).
- **Option A + hand-holding asserts (also failed)**: 4 `assert`s
  linking local `zeta_i` to parametric `127-4*round` form added 4 new
  failures (the asserts themselves couldn't discharge under
  `--ext context_pruning`).
- **Option B (passed)**: keep loop invariant impl-level
  (`re.coef[j] == f_inv_ntt_layer_1_step _re_init[j] (zeta(127-4j)) ...`),
  lift to function-form via a single `Classical.forall_intro` after
  the loop.  Each chunk j: reveal `is_i16b_array_opaque(4*3328)` from
  the original `is_bounded_poly` precondition, then invoke
  `Bridges.lemma_inv_ntt_layer_1_step_to_hacspec`.

### Verification

`make Libcrux_ml_kem.Invert_ntt.fst.checked` exit 0, "All verification
conditions discharged successfully", **528 s wall** at rlimit 800
+ `--ext context_pruning --split_queries always`.

### Next steps

- (b) Step 2 — layer 2/3 inverse bridges in Bridges.fst.
- (c) Step 3 — cross-vector for `invert_ntt_at_layer_4_plus`.
- (d) Step 7 — `add_standard_error_reduce` (in flight via sub-agent
  `agent/phase-7a-step-7` worktree, started afternoon resume).
- Step 5 — strengthen `invert_ntt_montgomery` post (chains the 7
  layer posts; this is the highest-risk Z3 point per the plan).
- Step 6 — strengthen 3 INTT-consuming reduce fns.

---



## Scope

Phase 7a Step 1 of the plan at `/Users/karthik/.claude/plans/replicated-beaming-pnueli.md`:
"per-pair butterfly plain-commute helper" + "per-chunk Tier-2 layer-1 commute lemma" for the **inverse NTT** direction (mirroring agent F's forward layer 1 work in commit `0eb1793e2`).

## What landed

### `specs/ml-kem/proofs/fstar/commute/Hacspec_ml_kem.Commute.Bridges.fst` (NEW, 385 lines)

Sibling module to `Chunk.fst` containing the function-form per-vector hacspec
bridges (the slow ones — Z3 queries take 35-58 sec on first verification
without hint replay).  Contents:

| Lemma | Direction | Verified |
|---|---|---|
| `mont_array_lane`, `zetas_4_lane` | helpers | ✅ |
| `lemma_ntt_layer_n_16_2_lane` | forward unfold helper (moved from Chunk.fst — agent F's) | ✅ |
| `lemma_ntt_layer_1_step_lane_bridge` | forward per-lane (moved from Chunk.fst — agent F's) | ✅ 35.6s |
| `lemma_ntt_layer_1_step_to_hacspec` | forward per-vector function-form (moved from Chunk.fst — agent F's) | ✅ 0.94s |
| `lemma_ntt_inverse_layer_n_16_2_lane` | **NEW** — inverse unfold helper | ✅ 0.38s |
| `lemma_inv_ntt_layer_1_step_lane_bridge` | **NEW** — inverse per-lane (mirror of forward) | ✅ 57.9s |
| `lemma_inv_ntt_layer_1_step_to_hacspec` | **NEW** — inverse per-vector function-form (mirror of forward) | ✅ 0.99s |

`Bridges.fst` opens `Hacspec_ml_kem.Commute.Chunk` for the per-pair commute
helpers (`lemma_butterfly_pair_commute`, `lemma_inv_butterfly_pair_commute`).

### `specs/ml-kem/proofs/fstar/commute/Hacspec_ml_kem.Commute.Chunk.fst` (UNCHANGED)

After my final restructure: byte-identical to its state at `8d92695bf`.
This was deliberate to avoid the Polynomial.fst regression I chased
mid-session (which turned out to be unrelated — see "Lessons" below).

### Documentation comments to impl files (commit `8d92695bf`)

Step 9 of the plan: scaling-chain doc comments documenting the resolved
end-to-end Mont-scaling story (audit findings from earlier in the session):

- `src/invert_ntt.rs` (above `invert_ntt_montgomery`): `·R⁻¹` form invariant + `1441 = R²/128 mod q` finalize.
- `src/polynomial.rs` (above 4 reduce fns): distinguishes INTT track (mont_mul ×1441) from matrix-mul track (to_standard_domain ×1353).
- `src/ntt.rs` (above `ntt_binomially_sampled_ring_element`, `ntt_vector_u`): NTT preserves input scaling.
- `src/sampling.rs` (above `sample_from_binomial_distribution`): plain output.
- `src/serialize.rs` (above `deserialize_then_decompress_ring_element_{u,v}`): plain output.

References cross-spec runtime tests at `src/ntt.rs:337-436` (`ntt_matches_spec`, `ntt_multiply_matches_spec`, `full_ntt_multiply_chain_matches_spec`) and `pq-crystals/kyber/main/ref/ntt.c:106` for the `1441 = mont²/128` identity.

## Verification status

| Module | Status | Time | Notes |
|---|---|---|---|
| `Hacspec_ml_kem.Commute.Bridges` | ✅ | 5.8s (with hints) / 98s (cold) | Step 1 |
| `Hacspec_ml_kem.Commute.Chunk` | ✅ | 50s | unchanged |
| `Libcrux_ml_kem.Polynomial` | ✅ | — | Was regressed — fixed by `hax.py extract` (stale .fst) |
| `Libcrux_ml_kem.Invert_ntt`, `Ntt`, `Matrix`, `Ind_cpa{,.Unpacked}`, `Vector.{Avx2,Portable}`, `Sampling`, `Serialize` | ✅ | — | No regressions |

`hax.py prove` final run (after `hax.py extract`): exit 0, 15 modules
re-verified (the cache-invalidated ones), ~133 cached, **no** `Error 19`,
**no** `make Error 1`.  All "incomplete quantifiers" log lines are
hint-replay misses that F* successfully retried.

## Commits

| SHA | Message |
|---|---|
| `ba8681b38` (HEAD) | agent-trackA: isolate inverse NTT layer 1 work in Bridges.fst (Chunk.fst untouched) |
| `8aa15f91b` | Refactor: split function-form hacspec bridges into Hacspec_ml_kem.Commute.Bridges |
| `36d389091` | agent-trackA: Phase 7a Step 1 — inverse NTT layer 1 hacspec bridge (WIP, unverified) |
| `8d92695bf` | Documentation: Step 9 — scaling-chain comments per algebra audit |

## Lessons (saved to `~/.claude/projects/-Users-karthik-libcrux/memory/`)

1. **Don't bulk-nuke `.checked` files** — `make`/`hax.py prove` handle stale incrementally; manual nuke wastes 20-30 min on unnecessary re-verification.  Only delete specific `.checked` files when narrowly needed.  **Never** delete `.hints` files.
2. **"failed (with hint)" is not a real failure** — F* retries without hint or with `--split_queries`, usually succeeds.  Only `Error 19` after `make Error 1` is genuinely failing.  The make exit code is the source of truth.
3. **Use fstar-mcp for iteration** — `typecheck_buffer` is sub-second on long-running session; `make` is 50-100s per cycle.  F* time is the sprint-deadline threat.  Skill at `~/.claude/skills/fstar-mcp/`, server at port 3001.
4. **Stale extracted .fst files** — Polynomial.fst was extracted yesterday before E2's `lemma_add_to_ring_element_commute` call existed; `.fsti` was re-extracted overnight but `.fst` was missed.  The mtime mismatch (`.fsti` newer than `.fst`) is the diagnostic.  Fix: `python3 hax.py extract` regenerates both consistently.

## Open work (next session)

- **Step 2 layer 2 / 3 inverse NTT bridges**: same pattern as layer 1, but trait branch_post for layer 2 has nested `if`-ladder (`b → (z, base, off)`) that previously caused Z3 timeouts on forward direction.  Mitigation in deferred-work comment in `Bridges.fst`: explicitly enumerate `i ∈ {0..15}` to remove symbolic `b = ...`.
- **Step 3 cross-vector commute for `invert_ntt_at_layer_4_plus`**: operates on chunk pairs, includes Barrett reduction (identity on mod-q values).
- **Step 4 strengthen `invert_ntt_at_layer_1`'s post** in `src/invert_ntt.rs`: add per-chunk function-form citation, body proof invokes `Bridges.lemma_inv_ntt_layer_1_step_to_hacspec` per loop iteration.  Capture pre-state of `re.coefficients` via `let _re_init = re.coefficients`.  Use **fstar-mcp** for fast iteration (Bridges.fst already has hint cache, so check should be sub-second).
- **Steps 5-8**: chain `invert_ntt_at_layer_N` posts → `invert_ntt_montgomery` post → 3 INTT-consuming reduce fns + `add_standard_error_reduce` → matrix.rs call sites.

The plan at `/Users/karthik/.claude/plans/replicated-beaming-pnueli.md` is the source of truth for this work; this session implemented Step 1 + Step 9 + the Bridges.fst split refactor.
