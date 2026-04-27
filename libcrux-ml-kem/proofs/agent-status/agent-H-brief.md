---
agent: H
phase: 7d — Matrix 4 fns
branch: agent/phase-7d-matrix
parent: trait-opacify (NEEDS Phase 7a's Tier-1 lemmas merged first)
worktree: yes
cap: 120 min total, 30 min hard cap on target #1
---

# Agent H brief — Phase 7d Matrix post-strengthening

You are a focused F* proof specialist for libcrux-ml-kem.  Your job is
Phase 7d: above-trait Matrix functions.

**This phase depends on Phase 7a's Tier-1 lemmas (poly add/sub/etc.)
and Phase 7b's Tier-2 NTT lemmas.**  Branch off `trait-opacify` AFTER
Phase 7a (E2) is merged.

## Mission

Add Tier-4 vector/matrix commute lemmas to
`Hacspec_ml_kem.Commute.Chunk.fst` and strengthen 4 (or 5) Matrix posts
to cite `Hacspec_ml_kem.Matrix.*`.

## Targets

In `libcrux-ml-kem/src/matrix.rs`:
1. `compute_message` — uses Phase 7a's `subtract_reduce` + ntt_multiply
2. `compute_ring_element_v` — uses Phase 7a's `add_message_error_reduce`
3. `compute_vector_u` — uses Phase 7a's `add_error_reduce` + per-row NTT
4. `compute_As_plus_e` — uses Phase 7a's `add_standard_error_reduce` + matrix-vec
5. `sample_matrix_A` — out of scope; depends on sampling layer (7n)

## First target — `compute_message` (30-min cap)

Why simplest: composes ntt_multiply + subtract_reduce, both with
Tier-1 lemmas now available.

Recipe:
- `to_spec_poly_plain` already defined (Phase 7a).
- The Tier-4 lemma chains: per-row inner_product (NTT_INV(NTT(s) ◦ NTT(u))
  → poly), then subtract from v.
- Both component lemmas exist post-7a / post-USER-2 (or use the
  available admitted-with-statement form for ntt_multiply per A1-A4 in
  Polynomial.Commute).
- `Classical.forall_intro` over K rows.

If `compute_message` requires `ntt_multiply`'s full Tier-3 wrap (which
is USER-5 / Tier-3 NTT composition), abort target #1 and switch to
`compute_ring_element_v` instead — it doesn't need ntt_multiply.

## R1-R9 hard rules (see agent-E2-brief.md for full text)

R1. No admits.
R2. Trait posts deliver per-lane FE equations via opaque predicates.
R3. 30-min cap on target #1; abort if not closed.
R4a. REPLACE `Spec.MLKEM` cite with `Hacspec_ml_kem.Matrix` in-place.
R5. No body assumes.
R6. ulimit -v 8388608, F* rlimit ≤ 800.
R7. Default `make`; fstar-mcp only if iterating ≥5x.
R8. Eager-commit log to `proofs/agent-status/agent-H.md`.
R9. Loop-invariant strengthening OK; don't redesign trait spec.

## Concurrency caveat

Phase 7b (agent F) edits the same `Hacspec_ml_kem.Commute.Chunk.fst`
in a different section.  Add Tier-4 lemmas under
`(*** Phase 7d Tier-4 commute lemmas — Matrix ***)` near the bottom.

## Verification cadence

```bash
cd libcrux-ml-kem/proofs/fstar/extraction
ulimit -v 8388608
make Libcrux_ml_kem.Matrix.fst.checked
```

## Stop conditions

- 30-min cap target #1; abort if not closed.  If Tier-1/Tier-3
  prerequisites missing, report and pause.
- 120-min total cap.
- 22-min cap per target after #1.

## Final deliverable

Commits on `agent/phase-7d-matrix`:
1. `Hacspec_ml_kem.Commute.Chunk.fst` — new Tier-4 lemmas (real bodies).
2. `src/matrix.rs` — strengthened posts.
3. `proofs/agent-status/agent-H.md` log.
4. Commit: `agent-H: Phase 7d — N/4 Matrix fns proved`.

DO NOT push.  DO NOT merge.
