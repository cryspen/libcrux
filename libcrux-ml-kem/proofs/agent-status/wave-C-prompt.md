# Wave-C coordinator prompt — Phase 3 critical chain (A6 → A7 → A8)

**STATUS: SKELETAL.**  This prompt is intentionally light.  Wave-C
will be **recalibrated** based on what Waves A and B learn in flight
(especially: A3's Chunk.fst additions, A5's Bridges.fst additions,
A6's matrix-level commute lemmas needed, and the Z3 budget for
ind_cpa / ind_cca after the trait posts strengthen).

The Wave-B coordinator updates this file at end-of-wave with the
recalibrated lane briefs, time budgets, and known unknowns.

---

## Wave-C scope (provisional)

Wave-C's job: close the consumer chain — Matrix (A6), Ind_cpa (A7),
Ind_cca (A8).  This is the strictly-sequential critical path; ~6
sessions wall.

**Worktree:** `~/libcrux-ml-kem-above-trait/` (continues from Wave-B's
HEAD; same worktree).
**Branch family:** `agent/lane-A<N>` per lane.

| Lane | Files | Effort | Depends on |
|---|---|---|---|
| A6 | `src/matrix.rs`, Chunk.fst (compute_message, compute_ring_element_v, compute_vector_u, compute_As_plus_e — Tier-4 commute) | 2 sess | A3 + A5 |
| A7 | `src/ind_cpa.rs`, Makefile (unadmit Ind_cpa) | 2 sess | A1, A2, A6 |
| A8 | `src/ind_cca.rs`, `src/matrix.rs`, Makefile (unadmit Ind_cca; simplify sample_matrix_A invariant) | 2 sess | A7 |

Sequential: A6 → A7 → A8 (strictly).  No within-Wave-C parallelism.

A4 (opportunistic, may be inherited from Wave-B if not attempted
there): can land any time after A3 if it converges; OK to leave
admitted.

## What to recalibrate at Wave-C kickoff

The Wave-B end-of-wave report should answer:

  1. **Chunk.fst state**: which sections did A1/A3/A5 add?  Do A6's
     Tier-4 vector/matrix commute lemmas need new infrastructure on
     top, or do they compose existing pieces?
  2. **Bridges.fst state**: did A5 leave a clean "polynomial-pair
     bridge" for A6 to chain across the matrix dimension?
  3. **A4 outcome**: did Wave-B attempt it?  If yes, did it close?
     If no, does it stay admitted forever or is it Wave-C's problem?
  4. **Z3 budget on Ind_cpa / Ind_cca**: are there any new findings
     about query saturation now that the trait posts are stronger?
     `ind_cpa::compute_message` and `ind_cca::decapsulate` are the
     historical pain points (rlimit 800 + memory).
  5. **Net admit count entering Wave-C**: this is the bar Wave-C
     must improve on.

## Hard rules (carried over)

R1-R10 from `wave-B-prompt.md` apply.  Specifically:
  - Trait FROZEN; don't touch traits.rs.
  - 20-min cap per function/lemma; default to (c) admit + USER-N
    if the property is genuinely Z3-walled.
  - No broad `panic_free` band-aids; small scoped admits OK if
    handed to USER-N.
  - Wave-C does not touch `src/vector/*` (Wave-A's surface).
  - Wave-C does not touch `src/serialize.rs`, `src/sampling.rs`,
    `src/polynomial.rs`, `src/invert_ntt.rs` (Wave-B's surface).

## Coordination conventions

`Hacspec_ml_kem.Commute.Chunk.fst` is touched by A6 only within
Wave-C.  Append to a clearly-marked `(* Phase 7d / lane A6 additions *)`
section; never edit Wave-A or Wave-B's additions.

`Makefile` (`proofs/fstar/extraction/Makefile`) is edited by A7
then A8 sequentially to remove modules from ADMIT_MODULES.

## Wave-C merge order

  1. A6 (Matrix; Chunk.fst Tier-4 lemmas).
  2. A7 (Ind_cpa unadmit; Makefile edit).
  3. A8 (Ind_cca unadmit; sample_matrix_A simplification; Makefile
     edit).
  4. A4 if not done (opportunistic; OK to leave admitted).

## Wave-C deliverable

  • A6 / A7 / A8 merged on `trait-opacify`.
  • Final admit-count report (sprint-end snapshot).
  • Closure of Spec.MLKEM teardown plan items currently open
    (Phases 7j-m if scope extends; not part of Wave-C critical path
    unless inherited).
  • Updated MLKEM_STATUS.md / agent-trackA.md.
  • End-of-sprint summary in `proofs/agent-status/sprint-summary.md`
    (NEW file): trait-opacify branch end state, total admit delta,
    USER-lane backlog, recommended next sprint.

---

**Note for Wave-C coordinator:** when you arrive, EDIT THIS FILE
to replace this skeletal scope with the recalibrated brief based on
Wave-B's findings.  The structure above is a starting point, not
a contract.
