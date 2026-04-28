# agent-trackA — session log

**Session date:** 2026-04-28 (resumed evening, Step 2 layer 3 added)
**Branch:** `trait-opacify`
**Tip at end:** `fa2151ea8` (was `7bb7e1a81` at start of this evening resume)

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
