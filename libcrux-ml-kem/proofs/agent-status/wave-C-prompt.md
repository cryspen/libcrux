# Wave-C coordinator prompt — Phase 3 critical chain (A6 → A7 → A8)

**STATUS: BLOCKED on Wave-B.**  Wave-B's coordinator session
2026-04-29 11:00–11:30 closed 0 lanes.  Wave-B's findings (recorded
below) recommend ONE-LANE-AT-A-TIME for the next series of sessions;
the multi-lane "wave" structure is not the right unit of work for
Phase 3 given the Z3-wall density.

**Sprint state at end of Wave-B:**
  - trait-opacify HEAD: `fa31480cd` (unchanged from Wave-A).
  - Above-trait worktree: `~/libcrux-ml-kem-above-trait/` (Wave-B
    setup is reusable for follow-on lane sessions).
  - Wave-B local Makefile: TEMP-admits `Libcrux_ml_kem.Invert_ntt.fst`
    in addition to the standard below-trait + Wave-C surface.  Lane
    A5 will UNADMIT when it begins.
  - Net admit-count delta from Wave-B: **0 net**.

## Wave-B's findings (2026-04-29) — the Phase 3 recalibration

1. **Lane scope is mis-sized for "wave" coordination.**  Each
   above-trait lane (A1-A5) is 1-3 sessions of Z3-walled body
   discharge.  A coordinator session that "spawns" them sequentially
   doesn't fit a typical 30-60 min Claude session budget.  Treat each
   lane as its OWN session henceforth; coordinator role atrophies.

2. **A2 spike: hax-lib `panic_free` semantics (recorded surprise).**
   Changing `verification_status(lax)` → `verification_status(panic_free)`
   on `sample_from_uniform_distribution_next` does NOT add an
   `--admit_smt_queries true` push-options block in the generated F*.
   `lax` IS the only annotation that emits that.  So `panic_free` is
   the same as full verification for SMT purposes; the only thing it
   affects is the panic-freedom check.  This means dropping `lax`
   directly to `panic_free` (or removing `verification_status` entirely)
   triggers the full body proof.  A2 hit the rejection-loop invariant
   subtyping wall (`forall j. j < K ==> ...` two-level forall) at
   rlimit 400 / "incomplete quantifiers".

3. **A1 / A3 / A5 untouched.**  Same Z3-wall risk as A2; deferred to
   USER-N or to dedicated single-lane sessions.

4. **Invert_ntt.fst Q101 baseline regression.**  In the Wave-B worktree
   (clone of trait-opacify HEAD `fa31480cd`), `inv_ntt_layer_int_vec_step_reduce`
   Q101 saturates rlimit 200 in the without-hint retry path (after
   hint replay fails).  This was passing in the source worktree at
   `0784e3b72` per agent-trackA but no longer at `fa31480cd`.  Suspect
   cause: B6's edit to `Hacspec_ml_kem.Commute.Chunk.fst` invalidated
   the hint chain into Q101; the genuine Z3 problem is borderline at
   rlimit 200.  Mitigation: either bump rlimit to 400 on
   `inv_ntt_layer_int_vec_step_reduce`, or (Wave-B's choice) keep
   Invert_ntt.fst admitted until A5 begins.

5. **Perf top-20: a much smaller surface in Wave-B baseline.**  See
   `proofs/agent-status/fstar-perf-top20.md` Snapshot 2.  With Wave-A's
   below-trait surface admitted away, only ~11 functions report
   non-trivial Query-stats.  `compress_then_serialize_message`'s
   single-query 4.9 s / max 4867 ms is the new top culprit and is
   directly in A1's Phase 7c migration path.

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

## Recommended next-session sequence (Wave-B's parting advice)

Skip the "wave" framing.  Do single-lane sessions in this order:

1. **Single-lane A2 session (1-2 hr).**  Tighten the rejection-loop
   invariant on `sample_from_uniform_distribution_next` with explicit
   per-`j` case-split + `Classical.forall_intro` over the K range.
   Then drop `verification_status(lax)`.  Expect Q1-Q3 to land at
   rlimit 400 ± `--split_queries always`.  After this lane succeeds:
   re-snapshot perf-top20.
2. **Single-lane A1 session (2-3 hr).**  Pick one of the smaller
   Phase 7c targets (`to_unsigned_field_modulus` or
   `serialize_uncompressed_ring_element`) and drop its `panic_free`.
   Mechanical Phase 7c migration on `compress_then_serialize_message`
   etc. is a separate session each — this is N×1-hour work, not 1×N.
3. **Single-lane A5 session (3+ hr) — the unblock for Wave-C.**
   Step 5 spike: admit layer-4_plus's strengthened post citing
   `IN.ntt_inverse_layer_n 256`, push the post chain up to
   `invert_ntt_montgomery`, validate against consumers.  If the spec
   shape holds, then come back and discharge layer 4_plus's body.
   This MUST land before A6 (Wave-C's first lane) can proceed.
4. **Single-lane A3 session.**  Pick fix hypothesis (b) from USER-7
   (define `to_spec_poly_mont_arr` array-form lemma) — sidesteps the
   record-bridge issue that killed the 3 prior attempts.

Wave-C (A6/A7/A8) remains gated on at least A5.  A4 remains
opportunistic (OK to leave admitted indefinitely).
