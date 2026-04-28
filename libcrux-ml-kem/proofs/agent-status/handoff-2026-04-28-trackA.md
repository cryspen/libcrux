# Session handoff — 2026-04-28 (post track A — Phase 7a Step 1 done)

This document is the resume entry point for a new session picking up
where track A left off.  Pair with the resume prompt at the bottom.

Supersedes the morning's `handoff-2026-04-28.md` (which is the
pre-track-A snapshot — kept for reference).

## TL;DR — where we are

`trait-opacify` (tip `ba8681b38`) has Phase 7a Step 1 done and verified.
The function-form per-vector hacspec bridge for **inverse NTT layer 1**
is delivered (mirrors agent F's forward layer 1 bridge), in a NEW
sibling module `Hacspec_ml_kem.Commute.Bridges`.

| Item | Status | Location |
|---|---|---|
| Phase 7a Step 1 (inverse NTT layer 1 hacspec bridge) | ✅ Closed, verified | `Bridges.fst:lemma_inv_ntt_layer_1_step_to_hacspec` |
| Phase 7a Step 9 (scaling-chain doc comments) | ✅ Closed | 5 .rs files in libcrux-ml-kem/src/ |
| Phase 7a Steps 2/3/4/5/6/7/8 | ⏸ Pending | see plan |
| Phase 7a 4 reduce fns (`subtract_reduce` etc.) | ⏸ Pending | needs Steps 4-6 |

## What landed this session

### `specs/ml-kem/proofs/fstar/commute/Hacspec_ml_kem.Commute.Bridges.fst` (NEW)

Sibling of `Chunk.fst`.  Holds the function-form per-vector hacspec
bridges (the slow ones — Z3 lane bridge queries take 35-58 sec on
first verification).  Splitting them out keeps `Chunk.fst` fast to
iterate (50 sec full verify) and isolates the slow queries.

Contents (all verified):

- `mont_array_lane`, `zetas_4_lane`: per-lane unfold helpers.
- `lemma_ntt_layer_n_16_2_lane`: forward spec function unfold helper.
- `lemma_ntt_layer_1_step_lane_bridge`: forward per-lane (agent F's, moved here).
- `lemma_ntt_layer_1_step_to_hacspec`: forward per-vector function-form (agent F's, moved here).
- `lemma_ntt_inverse_layer_n_16_2_lane`: NEW inverse spec function unfold helper.
- `lemma_inv_ntt_layer_1_step_lane_bridge`: NEW inverse per-lane.
- `lemma_inv_ntt_layer_1_step_to_hacspec`: NEW inverse per-vector function-form.

Bridges.fst opens `Hacspec_ml_kem.Commute.Chunk` for the per-pair
butterfly commute helpers.  Chunk.fst is byte-identical to its state
at `8d92695bf` (= the last working state before track A's edits).

### Doc comments in `libcrux-ml-kem/src/{invert_ntt,polynomial,ntt,sampling,serialize}.rs`

Step 9 of the plan: scaling-chain comments documenting the audit
findings.  No functional code changes; cargo check passes.

## What was investigated this session (and resolved)

### Polynomial.fst regression — RESOLVED

Mid-session, `Polynomial.fst.add_to_ring_element` failed with
"incomplete quantifiers" on Q60.  Investigation traced it to a STALE
extraction:

- `Polynomial.fst` was extracted on 2026-04-27 16:21 (BEFORE E2's
  commit `1d6cacc50` at 00:48 today which added the
  `lemma_add_to_ring_element_commute` body proof).
- `Polynomial.fsti` was re-extracted at 01:23 today (overnight),
  pulling in E2's strengthened `ensures`.
- The .fst body was missing the lemma call, so the new ensures
  could not be discharged.

Fix: `python3 hax.py extract` regenerated both files consistently.
After re-extract, `Polynomial.fst` verified cleanly.

The regression was NOT caused by track A's Bridges split; this was
verified by moving `Bridges.fst` out of `specs/ml-kem/proofs/fstar/commute/`
and observing the same `Polynomial.fst` failure.

## Final verification status (post `hax.py extract` + `hax.py prove`)

`hax.py prove` exit 0.  Latest `verification_result.txt` (in
`libcrux-ml-kem/`):

- 15 modules re-verified (the cache-invalidated ones); ~133 cached.
- ZERO `Error 19`, ZERO `make Error 1`.
- All "incomplete quantifiers" log entries are hint-replay misses
  that F* successfully retried (a counted-but-not-real failure
  pattern).

Verified modules include: `Polynomial`, `Invert_ntt`, `Ntt`, `Matrix`,
`Ind_cpa{,.Unpacked}`, `Vector.{Avx2,Portable}`, `Sampling`,
`Serialize`, `Vector.Portable.Vector_type`, `Vector.Neon.{Ntt,Vector_type}`,
`Vector.Avx2.{Compress,Sampling}`.

`Hacspec_ml_kem.Commute.Bridges.fst` separately verified from the
commute directory (5.8 sec with hints).

## Lessons (saved to `~/.claude/projects/-Users-karthik-libcrux/memory/`)

1. **Don't bulk-nuke `.checked` files** — `make` and `hax.py prove`
   handle stale incrementally via F*'s dep tracking.  Manual nuke
   wastes 20-30 min on unnecessary re-verification.  Only delete
   specific `.checked` files when narrowly needed.  **Never** delete
   `.hints` files.
2. **"failed (with hint)" lines aren't real failures** — F* retries
   without hint or with `--split_queries always`, frequently
   succeeding.  Only `Error 19` after `make Error 1` indicates a
   genuinely failing proof.  The make exit code is the source of
   truth.
3. **Use fstar-mcp for iteration** — `typecheck_buffer` is sub-second
   on a long-running session; `make` is 50-100s+ per cycle.  F* time
   is the sprint-deadline threat.  Skill at `~/.claude/skills/fstar-mcp/`,
   server at port 3001.
4. **Stale extracted .fst files** — `.fsti` newer than `.fst` is the
   diagnostic.  Fix: `python3 hax.py extract` regenerates both
   consistently.

## Recommendation for next session

The natural next step is **Step 4** (post-strengthen `invert_ntt_at_layer_1`
in `src/invert_ntt.rs`):

- Add a per-chunk function-form citation to the `ensures`:
  ```
  forall i. i < 16 ==>
    mont_i16_to_spec_array(future re.coefficients[i].repr) ==
      IN.ntt_inverse_layer_n 16
        (mont_i16_to_spec_array(re.coefficients[i].repr))
        2
        (zetas_4 (zeta(127-4i)) (zeta(126-4i)) (zeta(125-4i)) (zeta(124-4i)))
  ```
- Body proof: capture `_re_init = re.coefficients` at fn entry.
  Loop invariant tracks per-chunk equation for processed chunks.
  After the call to `Vector::inv_ntt_layer_1_step`, invoke
  `Hacspec_ml_kem.Commute.Bridges.lemma_inv_ntt_layer_1_step_to_hacspec`
  with the actual zetas from `zeta(*zeta_i .. *zeta_i - 3)`.
- Use **fstar-mcp** for iteration — Bridges.fst hint cache is fresh,
  so each typecheck round should be sub-second.
- After Step 4 verifies, repeat for layers 2/3/4_plus (Steps 2/3),
  then chain into `invert_ntt_montgomery`'s post (Step 5).

Estimated effort: Step 4 alone = 1-2 hours with fstar-mcp.

## Read order for new session

1. **THIS FILE.**
2. `proofs/agent-status/agent-trackA.md` — full session log.
3. `proofs/proof-style-guide.md` §12 — Mont-arithmetic-in-posts antipattern.
4. `proofs/agent-status/dashboard.md` — current state table.
5. `MLKEM_STATUS.md` — phase plan + USER tasks.
6. `/Users/karthik/.claude/plans/replicated-beaming-pnueli.md` — the plan.

## Hard rules R1-R10 (from prior sessions, still apply)

See `proofs/agent-status/agent-F-brief.md`.  Distilled:

- R1. Admit-driven scaffolding = unacceptable.  Skip-with-comment AFTER a real attempt is OK.
- R2. Trait posts deliver per-lane FE equations via opaque predicates.
- R3. Mandatory first-target proof; 30-min cap on target #1.
- R4. Existing pre-trait-opacify proofs are reference-only.
- R4a. REPLACE `Spec.MLKEM` cite with `Hacspec_ml_kem.*` in-place.
- R5. Body assumes are unacceptable.
- R6. ulimit -v 8388608, F* rlimit ≤ 800.
- R7. Default `make`/`hax.py prove` for end-of-chunk regression; **prefer fstar-mcp** for inner-loop iteration.
- R8. Eager-commit log to `proofs/agent-status/agent-X.md` on the agent branch.
- R9. Don't redesign trait spec; minor loop-invariant strengthening OK.
- R10. Hacspec extension is allowed when documented (e.g., F's `ntt_inverse_butterflies`); modifying canonical hacspec algebra (introducing Mont scaling) is NOT.

Plus the four new lessons from track A above (no cache nuke, hint-replay failures aren't real, fstar-mcp for iteration, stale .fst diagnosis).

## Resume protocol (paste into new Claude Code session)

```bash
cd /Users/karthik/libcrux-trait-opacify
git status              # should be clean on trait-opacify
git log --oneline trait-opacify -5   # tip = ba8681b38
pgrep -f fstar.exe      # should be 0 ml-kem-related (only fstar-mcp at port 3001)
# Read this file first, then agent-trackA.md, then dashboard.md.
```
