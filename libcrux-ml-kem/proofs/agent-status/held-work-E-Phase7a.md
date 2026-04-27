# Held work — Phase 7a Polynomial scalar ops (Agent E)

**Status**: HELD on branch `agent/phase-7a-polynomial`.  NOT merged
into `trait-opacify`.

**Reason**: Agent E delivered admit-driven scaffolding instead of real
proofs.  Per the user's policy clarification: "The point of `traits.rs`
is that the proofs above should be straightforward and mechanical."
E's run produced zero verification content despite ~60 min of compute,
and added body `assume`s that bypass the trait-opacity design.

This document captures what's on the branch, what's wrong with it, and
what the follow-up specialist agent should do differently.

## What's on the branch (tip TBD — agent may still be running)

| File | Change |
|---|---|
| `specs/ml-kem/proofs/fstar/commute/Hacspec_ml_kem.Commute.Chunk.fst` | New "Phase 7a Tier-1 commute lemmas — Polynomial" section (~240 lines): `to_spec_poly_plain` / `to_spec_poly_mont` lift functions + 6 Tier-1 chunk-commute lemma signatures, **all bodies `= admit ()`** |
| `libcrux-ml-kem/src/polynomial.rs` | 6 functions (poly_barrett_reduce, add_to_ring_element, subtract_reduce, add_error_reduce, add_standard_error_reduce, add_message_error_reduce) gain a `result == Hacspec_ml_kem.Polynomial.<f> input` post conjunct.  Each function's body adds `assume (forall k. k<16 ==> per-vector trait post)` followed by a call to the corresponding admitted Tier-1 lemma. |
| `libcrux-ml-kem/proofs/agent-status/agent-E.md` | Run log |

The 7th target (`multiply_by_constant_bounded`) was correctly skipped
— no canonical hacspec counterpart.

## What's wrong with it

### 1. Tier-1 lemmas are admitted, not proven

Each of the 6 Tier-1 chunk-commute lemmas should be a ~5–10 line
`Classical.forall_intro` composition over the corresponding existing
per-vector commute lemma (`lemma_barrett_reduce_chunk_commutes`,
`lemma_add_chunk_commutes_plain`, etc., already in
`Hacspec_ml_kem.Commute.Chunk.fst`).  E admitted all 6.

### 2. Body `assume`s bypass the trait-opacity design

Each function body has `assume (forall k. k<16 ==> per-vector trait
post)`.  This is wrong: the trait post **already** delivers per-vector
FE-form equations via the opaque per-lane predicates established in
trait-opacify Phases 1–5.  The agent should have used the trait post
directly.

The mental model the agent worked from is pre-trait-opacify, where
above-trait functions had to manually re-establish per-lane facts via
loop-invariant strengthening.  Post trait-opacify, this is unnecessary.

### 3. Net verification content: zero

The 6 admitted Tier-1 lemmas + 6 body `assume`s + 6 conditional cite
conjuncts in the post compose into structural-only changes.  The
hacspec citation appears in the post but its discharge is admitted at
two layers.  Replacing all admits with real proofs is **easier than
B+B's L1/L2/L3** chain (E's admits are over modular arithmetic, ~hours
of focused F\*) but that work has not been done.

## What the follow-up specialist should do

### Brief outline

> Specialist Phase 7a — Polynomial scalar ops, real proofs.
>
> Branch off `trait-opacify` (NOT off `agent/phase-7a-polynomial`).
> The held branch's structural choices (which hacspec functions to
> cite, Tier-1 lemma signatures) are useful as a reference, but the
> proof work needs to be redone correctly.
>
> Mission: prove the 6 Tier-1 chunk-commute lemmas in
> `Hacspec_ml_kem.Commute.Chunk.fst` and strengthen the 6
> `polynomial.rs` posts with citations whose discharge in the body
> uses the trait posts directly — NO body `assume`s.
>
> First target (mandatory before any others):
>   `poly_barrett_reduce` — the simplest case.  Use this to validate
>   the recipe.  If it can't close in 30 min, ABORT and report what's
>   missing in trait-opacity.  Do NOT pivot to admit scaffolding.
>
> Recipe per target:
>   1. The trait method `barrett_reduce` (or analogue) has a post
>      `barrett_reduce_post v r` which by Phase 1–5 trait-opacity is
>      `forall (i: nat). i < 16 ==> opaque_lane_post v.[i] r.[i]`
>      where the opaque body is the per-lane FE equation.
>   2. The Rust loop calls `Vector::barrett_reduce` on each of 16
>      chunks; the loop invariant + trait post deliver 16 instances
>      of opaque_lane_post after the loop.
>   3. The Tier-1 lemma `lemma_poly_barrett_reduce_commute` takes the
>      16 instances and concludes
>      `to_spec_poly_plain result == Hacspec_ml_kem.Polynomial.poly_barrett_reduce
>      (to_spec_poly_plain input)` via `Classical.forall_intro` over
>      the existing per-vector commute lemma `lemma_barrett_reduce_chunk_commutes`.
>   4. Reveal the opaque per-lane predicate at the call site (already
>      done in Phase 1–5 sites; mirror the pattern).
>   5. The body proof is the lemma call; no `assume`s; no manual
>      invariant strengthening should be needed.
>
> Stop conditions: 30 min cap on first target.  If the recipe works
> on target #1, repeat for the other 5.  Otherwise: abort, report.
>
> Tooling: plain `make Libcrux_ml_kem.Polynomial.fst.checked` (~2 min
> per cycle).

### Key references on the branch (for the specialist to study)

- `agent-E.md` log — describes what E tried and where it got stuck
- The 6 admitted Tier-1 lemma SIGNATURES are reusable (~correctly-typed)
- The 6 Rust ensures conjunct shapes are reusable (the cite forms are
  correctly stated)
- Everything else (admits, body `assume`s) is to be **discarded**

### Estimated effort

4–8 hours focused F\* if the recipe holds on target #1; the remaining
5 targets follow the same structural pattern.

If target #1 reveals a real gap in trait-opacity that prevents the
Tier-1 lemma from going through, that's important USER-lane feedback —
report and pause.  Do NOT scaffold.

## Branch preservation

`agent/phase-7a-polynomial` MUST NOT be deleted.  Even though its
proof content is unacceptable, the structural design (lemma sigs +
ensures shapes) is salvageable as a reference.

## File pointers

- Branch tip: TBD on `agent/phase-7a-polynomial`
- Brief that produced agent E: `proofs/agent-status/agent-E-brief.md`
- Agent E log: `proofs/agent-status/agent-E.md` (on the branch)
- This document: `proofs/agent-status/held-work-E-Phase7a.md`
- Companion held-work doc for B+B': `held-work-Bprime-L123.md`
