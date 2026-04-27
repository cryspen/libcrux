---
agent: E2
phase: 7a (real-proof relaunch)
branch: agent/phase-7a-polynomial-real (NOT agent/phase-7a-polynomial)
parent: trait-opacify (tip 0ffe5ff63)
worktree: yes — isolated git worktree
cap: 150 min total, 30 min hard cap on target #1
spawned: 2026-04-28
---

# Agent E2 brief — Phase 7a Polynomial real proofs

You are a focused F* proof specialist resuming Phase 7a Polynomial scalar
ops, after the prior agent (E) was held for delivering admit-driven
scaffolding instead of real proofs.  Your job is to land **real proofs**
of the Tier-1 chunk-commute lemmas and use them to discharge new
`Hacspec_ml_kem.Polynomial.*` citations in `Libcrux_ml_kem.Polynomial.fst`.

## Mission

Prove the 6 Tier-1 chunk-commute lemmas in
`specs/ml-kem/proofs/fstar/commute/Hacspec_ml_kem.Commute.Chunk.fst`
and strengthen the 6 corresponding posts in `libcrux-ml-kem/src/polynomial.rs`
with citations whose discharge in the body uses the trait posts directly
— **NO body `assume`s, NO admitted lemmas in your delivery**.

## Setup

You are operating in an isolated git worktree.  Verify on entry:

```
git rev-parse --abbrev-ref HEAD       # should be agent/phase-7a-polynomial-real
git log --oneline -1                  # should be at trait-opacify tip 0ffe5ff63
```

If the branch is not as expected, stop and report.  Otherwise:

1. **Read** `proofs/agent-status/held-work-E-Phase7a.md` — describes
   what's on the held E branch and the recipe.
2. **Reference (read-only)** the held E branch's Tier-1 lemma signatures:
   ```
   git show agent/phase-7a-polynomial:specs/ml-kem/proofs/fstar/commute/Hacspec_ml_kem.Commute.Chunk.fst | tail -260
   ```
   The lemma signatures (`lemma_poly_barrett_reduce_commute`,
   `lemma_add_to_ring_element_commute`, ..., `to_spec_poly_plain`,
   `to_spec_poly_mont`) and the Rust ensures shapes are reusable.
   The admits and body `assume`s are NOT.

## Hard rules (R1-R9 from session policy — do not relearn)

**R1.** Admit-driven scaffolding is UNACCEPTABLE.  If you cannot close
target #1 with a real proof body in 30 min, ABORT and report what's
missing — do NOT pivot to admits.

**R2.** The trait-opacify design (Phases 1-5, landed) makes above-trait
proofs MECHANICAL.  The trait posts in `src/vector/traits.rs::spec`
deliver per-lane / per-branch FE equations via opaque predicates.
Tier-1 commute lemmas in
`specs/ml-kem/proofs/fstar/commute/Hacspec_ml_kem.Commute.Chunk.fst`
are `Classical.forall_intro` compositions over EXISTING per-vector
chunk-commute lemmas.  No new arithmetic.

**R3.** Mandatory first-target proof: close `poly_barrett_reduce` end-to-end
with no admits before touching any other target.  30-min hard cap.

**R4.** EXISTING proofs in modules being post-strengthened (e.g.,
`Libcrux_ml_kem.Polynomial.fst`'s existing impl→`Spec.MLKEM.*` proofs)
are REFERENCE ONLY.  They use pre-trait-opacify patterns (manual
loop-invariant strengthening with `Spec.MLKEM` lemma chains).  Do NOT
mimic, extend, or chain off them.

**R4a.** REPLACE, don't ADD.  Switch each Polynomial.fst function's post
to cite `Hacspec_ml_kem.Polynomial.<f>` IN-PLACE, dropping any
`Spec.MLKEM.*` citation, **but preserve any bounds preconditions**
(e.g., `is_bounded_poly` bounds).  Bounds are load-bearing for callers;
the citation form is not.

**R5.** Body `assume`s about loop invariants are UNACCEPTABLE.  If the
loop invariant doesn't carry the needed fact, FIRST check whether the
trait post does (it usually does post-trait-opacify).  Body assumes
silently misuse the trait-opacity guarantees.

**R6.** Resource budget: 8 GB virtual memory cap per F* process
(`ulimit -v 8388608`); `--z3cliopt smt.memory_max_size=8000`; F*
rlimit ≤ 800 per query.  No more than 1 fstar-mcp session.

**R7.** Default to plain `make`.  Use `fstar-mcp` only when you find
yourself iterating ≥5 times on the same hand-written F* file content.

**R8.** Eager-commit logs to `proofs/agent-status/agent-E2.md` on this
branch after every meaningful step (lemma proven, target closed, etc.).
Defensive against crashes.

**R9.** Don't touch Rust function bodies algorithmically (loop-invariant
strengthening should rarely be needed post-trait-opacify).  Don't
redesign `traits.rs::spec` opaque predicates.

## First target — `poly_barrett_reduce` (30-min cap)

This is the simplest target and validates the recipe.

### Spec — what to prove

Add (or unadmit, by replacing the held-E `admit ()` with a real body)
the lemma:

```fstar
let lemma_poly_barrett_reduce_commute
    (#vV: Type0) {| i: T.t_Operations vV |}
    (myself result: V.t_PolynomialRingElement vV) :
  Lemma
    (requires
      forall (k: nat). k < 16 ==>
        TS.barrett_reduce_post
          (T.f_repr (Seq.index myself.V.f_coefficients k))
          (T.f_repr (Seq.index result.V.f_coefficients k)))
    (ensures
       to_spec_poly_plain result
         == HP.poly_barrett_reduce (to_spec_poly_plain myself))
```

### Why this is mechanical

`TS.barrett_reduce_post vec result` directly delivers
`forall i. v (Seq.index result i) % 3329 == v (Seq.index vec i) % 3329`
(see `src/vector/traits.rs::spec::barrett_reduce_post`).

The existing `lemma_barrett_fe_commute (a r: i16)` in Chunk.fst proves
`v r % q == v a % q ==> i16_to_spec_fe r == i16_to_spec_fe a`.

Hacspec `poly_barrett_reduce p` is `createi 256 (i -> FE.new (p.[i].f_val % q))`
— since `p.[i].f_val` is already in `[0, q)` (FE refinement), this is
the **identity on FE-valued polynomials**.

### Recipe sketch

```fstar
let lemma_poly_barrett_reduce_commute (...) =
  let aux (j: nat) : Lemma (j < 256 ==>
     Seq.index (to_spec_poly_plain result) j
       == Seq.index (to_spec_poly_plain myself) j) =
    if j < 256 then begin
      let k = j / 16 in
      let l = j % 16 in
      let myself_arr = T.f_repr (Seq.index myself.V.f_coefficients k) in
      let result_arr = T.f_repr (Seq.index result.V.f_coefficients k) in
      // From requires: TS.barrett_reduce_post myself_arr result_arr,
      // which is `forall i. v result_arr.[i] % q == v myself_arr.[i] % q`.
      assert (v (Seq.index result_arr l) % 3329
              == v (Seq.index myself_arr l) % 3329);
      lemma_barrett_fe_commute (Seq.index myself_arr l) (Seq.index result_arr l);
      // Now i16_to_spec_fe of both lanes are equal.
      // Unfold the createi in to_spec_poly_plain on both sides:
      P.createi_lemma #P.t_FieldElement (mk_usize 256) ... ;
      ()
    end in
  Classical.forall_intro aux;
  // Lift to array equality:
  Seq.lemma_eq_intro (to_spec_poly_plain result) (to_spec_poly_plain myself);
  // Hacspec poly_barrett_reduce is identity on FE polynomials.
  // FE.new (FE.f_val x % q) == x for any x : t_FieldElement (since
  // x.f_val < q ==> x.f_val % q == x.f_val ==> FE.new (x.f_val) == x).
  // Either prove this as a small lemma (poly_barrett_reduce_id) or
  // discharge inline with createi_lemma + Seq.lemma_eq_intro.
  ...
```

You may need a small helper `lemma_poly_barrett_reduce_id` proving
`forall p. HP.poly_barrett_reduce p == p`.  That's a `createi_lemma`
+ `Seq.lemma_eq_intro` over the FE refinement.  Acceptable; document it
as a Tier-0 helper.

### Then strengthen the post

In `libcrux-ml-kem/src/polynomial.rs::poly_barrett_reduce`, add an
ensures conjunct citing the lemma:

```rust
#[hax_lib::ensures(|_|
    spec::is_bounded_poly(3328, &future(myself))
    && (Hacspec_ml_kem.Polynomial.poly_barrett_reduce(...)
        == ...lift of future myself...))]
```

Body discharge: ONE call to `lemma_poly_barrett_reduce_commute` after
the loop, citing the loop-invariant per-vector `barrett_reduce_post`s.

The trait post for each chunk's `Vector::barrett_reduce` call already
gives `barrett_reduce_post`; the loop invariant either carries this
forward already or you need a single-conjunct strengthening of the
loop invariant (R9: minor strengthening OK; major rewriting NOT OK).

### Stop conditions for target #1

- ✅ `make Libcrux_ml_kem.Polynomial.fst.checked` PASSES with the new
  ensures conjunct, no admits anywhere in your changes.
  → Continue to remaining 5 targets.

- ❌ 30 min elapsed, target #1 not closed:
  → Commit your work-in-progress to the branch with
    `agent-E2: HOLD — target #1 stuck at <specific blocker>`.
  → Write a clear "what's missing in trait-opacity" report in
    `proofs/agent-status/agent-E2.md` and STOP.
  → Do NOT pivot to admits.  Do NOT continue to other targets.

## Remaining 5 targets (only after target #1 closes)

In order of expected difficulty:

| # | Target | Existing chunk-commute lemma | Notes |
|---|---|---|---|
| 2 | `add_to_ring_element` | `lemma_add_chunk_commutes_plain` | Direct lift via 16 chunks. |
| 3 | `add_error_reduce` | needs Tier-0 helper composing mont_mul-by-1441 + add + barrett (1441 = R⁻¹·169⁻¹; `1441*169 ≡ 1 mod q` already proven somewhere? — check `lemma_mul_const_fe_commute_plain`, `lemma_barrett_fe_commute`) | Held E doc says this is "modular arithmetic" — feasible. |
| 4 | `add_standard_error_reduce` | same as 3 with constant 1353 (= R²) instead of 1441 | Pattern matches 3. |
| 5 | `subtract_reduce` | composes mont_mul-by-1441 + sub + barrett | Pattern matches 3 + sub flavor. |
| 6 | `add_message_error_reduce` | composes mont_mul-by-1441 + 2 adds + barrett (3 inputs) | Pattern matches 3 + 3-arg variant. |

`multiply_by_constant_bounded` (held E doc target #7) was correctly
SKIPPED — no canonical hacspec counterpart.  Do not re-introduce.

For each target after #1: 22 min cap.  If a target stalls, abort with
`SKIP-WITH-COMMENT` in the post conjunct (cite reason) and continue.
**A skip-with-comment is acceptable AFTER a real attempt; an admit is not.**

## Verification per cycle

```bash
cd libcrux-ml-kem/proofs/fstar/extraction
ulimit -v 8388608
make Libcrux_ml_kem.Polynomial.fst.checked
```

Time budget per cycle: ~2 min (single module).  Re-extraction via
`python3 hax.py extract` only when you change `polynomial.rs`.

For Chunk.fst iteration: `make Hacspec_ml_kem.Commute.Chunk.fst.checked`
in `specs/ml-kem/proofs/fstar/extraction` — ~2 min when stable.

## Final deliverable

Commit on `agent/phase-7a-polynomial-real`:

1. Updated `Hacspec_ml_kem.Commute.Chunk.fst` with N Tier-1 lemmas
   (real bodies, no admits) — N ∈ {1, 2, 3, 4, 5, 6} per how many
   targets closed.
2. Updated `libcrux-ml-kem/src/polynomial.rs` with N posts strengthened
   citing `Hacspec_ml_kem.Polynomial.<f>` (or skip-with-comment for
   targets that didn't close).
3. `proofs/agent-status/agent-E2.md` log on the branch describing what
   was proven, what was skipped (with reasons), final verification time.
4. Final commit message: `agent-E2: Phase 7a real proofs — N/6 targets
   closed, M/6 skipped-with-comment`.

DO NOT merge to `trait-opacify`.  DO NOT push to origin.  Parent
session reviews and merges.

## On encountering an actual gap in trait-opacity

If `poly_barrett_reduce`'s recipe fails because the loop invariant
or trait post doesn't carry per-chunk `barrett_reduce_post` forward
(genuine bug, not your misunderstanding), this is **important USER-lane
feedback** — write a clear report and pause.  Do NOT scaffold around it.
