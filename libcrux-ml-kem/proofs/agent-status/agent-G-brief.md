---
agent: G
phase: 7n — sample_from_uniform_distribution_next admit cleanup
branch: agent/phase-7n-sampling
parent: trait-opacify
worktree: yes
cap: 60 min total
---

# Agent G brief — Phase 7n Sampling admit cleanup

You are a focused F* proof specialist for libcrux-ml-kem.  Your job is
Phase 7n: clean up the `lax` annotation on
`sample_from_uniform_distribution_next` in
`libcrux-ml-kem/src/sampling.rs`.

This phase is **orthogonal** to Phases 7a/7b/7d (no shared file edits),
so it runs concurrently with them.

## Mission

Remove the `#[hax_lib::fstar::verification_status(lax)]` annotation
from `sample_from_uniform_distribution_next` (line ~51 in
`src/sampling.rs`) and prove the body satisfies its existing requires/
ensures.  No admits.  No body assumes.

## Why it's lax today

Per `MLKEM_STATUS.md`: "Investigation; may need rejection-loop invariant
tightening."  The function uses a 2-level rejection loop with a
running counter `sampled_coefficients[i]`; the existing loop invariants
strengthen the bound monotonically across rounds.  The lax was set to
unblock progress; the proof obligations are likely tractable now under
trait-opacify (the per-vector `Vector::rej_sample` post should give
per-call deltas the invariant can chain).

## First action (30-min discovery)

1. Read the function body and existing requires/ensures fully.
2. Read `Vector::rej_sample`'s spec in `src/vector/traits.rs::spec`.
3. Try removing `lax` and running `make Libcrux_ml_kem.Sampling.fst.checked`.
4. Inspect Z3 errors — likely loop-invariant gaps; identify the missing
   conjunct.

## R1-R9 hard rules

R1. No admits in your delivery.
R2. Trait posts directly deliver per-call deltas via `rej_sample_post`.
R3. 30-min cap on first attempt; if not closing, abort with report.
R5. No body assumes.
R6. ulimit -v 8388608, F* rlimit ≤ 800.
R7. Default `make`.
R8. Eager-commit log to `proofs/agent-status/agent-G.md`.
R9. Loop-invariant strengthening OK; don't algorithmically rewrite the body.

## Stop conditions

- 30-min discovery (find specific missing invariant) → 30-min repair.
  If 60 min elapsed without close, ABORT with report on what's missing.
- If `Vector::rej_sample`'s post is too weak to support the proof,
  document the gap as USER-lane feedback.  Don't add admits to the
  function under proof.

## Final deliverable

Commit on `agent/phase-7n-sampling`:
1. `src/sampling.rs` with `lax` removed (or remaining if the proof
   isn't reachable, with a `lax` retained + comment explaining).
2. `proofs/agent-status/agent-G.md` log.
3. Commit: `agent-G: Phase 7n — sample_from_uniform_distribution_next
   {proven|held with explanation}`.

DO NOT push.  DO NOT merge.
