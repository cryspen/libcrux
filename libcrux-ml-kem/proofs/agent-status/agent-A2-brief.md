# Agent A2 — Phase 6 follow-up: close the 2 remaining layer-1 admits

Continuation of agent A's run on branch `agent/phase-6-portable-ntt`
(tip `65668af62`).  Agent A landed 4/6 admits proven and documented a
refactor recipe in source for the remaining 2.  This brief tells A2 to
execute that recipe.

## Mission

Drop the `--admit_smt_queries true` annotations on:
- `op_ntt_layer_1_step` (line ~331 in `src/vector/portable.rs`)
- `op_inv_ntt_layer_1_step` (line ~563)

via the documented refactor: **factor 4 dedicated per-zeta lemmas + use
`Spec.Utils.forall4` intro**, in `Hacspec_ml_kem.Commute.Chunk.fst`.
Agent A's in-source comment block has the recipe.  Read it first.

## Required reading (in order)

1. The in-source comment immediately above `op_ntt_layer_1_step` in
   `src/vector/portable.rs` on branch `agent/phase-6-portable-ntt` —
   describes WHY the original 4-way zeta dispatch caused Z3 case-split
   blowup, and the refactor recipe.
2. Agent A's log: `proofs/agent-status/agent-A.md` on the same branch.
3. `libcrux-ml-kem/proofs/proof-style-guide.md` — esp. §3.4
   `Classical.forall_intro` + §3.6 Tier-2 NTT layer-step composition.
4. The 4 already-proven layer_2/3 wrappers (`op_ntt_layer_{2,3}_step`,
   `op_inv_ntt_layer_{2,3}_step`) — same shape but smaller dispatch.
   Mirror their proof strategy after the refactor.
5. `Hacspec_ml_kem.Commute.Chunk.fst` — where the 4 new per-zeta lemmas
   should live.  Read existing `lemma_butterfly_pair_commute` /
   `lemma_inv_butterfly_pair_commute` for the template.

## Operating constraints

- **Wall clock**: 60 min total (generous because the refactor needs 4
  new lemmas + 2 call-site rewrites).
- **Per-target budget**: ~25 min (op_ntt_layer_1_step first, then the
  inverse).  If the refactor proves harder than expected, restore the
  current admit-with-comment on either or both, commit, and report
  back.
- **Memory**: `ulimit -v 8388608`, `--z3cliopt smt.memory_max_size=8000`.
- **F\* concurrency**: at most 1 F\* process at a time.
- **F\* rlimit**: never exceed 800.
- **Tooling**: plain `make` for verification.  fstar-mcp on port 3002
  ONLY if you iterate ≥5 times on the same hand-written
  `Hacspec_ml_kem.Commute.Chunk.fst` content; tear down at end.

## Code change policy (delta from original A brief)

- **Rust function bodies of `op_ntt_layer_*_step`**: still NOT touched.
- **F\* annotations on those functions**: editable.
- **`Hacspec_ml_kem.Commute.Chunk.fst`**: editable — add 4 new per-zeta
  lemmas (`lemma_layer_1_zeta_<n>_commute` for n ∈ {0,1,2,3}, or analogous
  naming) factored from the existing per-branch one.  Each new lemma
  takes a single zeta argument, no internal dispatch.
- **`traits.rs::spec` opaque per-branch predicates**: do NOT redesign.
  The refactor lives ABOVE these — at call sites, decompose the
  per-branch hypothesis into 4 per-zeta lemma applications.
- **Specs (`Spec.Utils.fsti` or analogous)**: editable to add helper
  forall-introductions if needed.

## Known refactor recipe (from agent A's source comment)

Replacing the per-branch dispatch lemma at the call site:
```fstar
// Old (case-splits on b ∈ {0,1,2,3}):
forall4 (fun b -> ntt_layer_1_step_branch_post v b r) ==>
  forall16 (fun i -> i16_to_spec_fe r.[i] == hacspec_butterfly_eq i)

// New (4 separate forall instantiations per zeta):
let lemma_zeta_0 : Lemma (per_zeta_post zeta0 v r) -> ... = ()
let lemma_zeta_1 : Lemma (per_zeta_post zeta1 v r) -> ... = ()
...
Classical.forall_intro_4 lemma_zeta_<n>
```

Verify the layer_2/3 already-proven wrappers' proofs to see the exact
pattern they use — adapt for 4 zetas.

## Eager-commit logging

Continue updating `proofs/agent-status/agent-A.md` on
`agent/phase-6-portable-ntt`.  Append a new section header
`## Phase 6 follow-up (agent A2) — YYYY-MM-DD`.  After every meaningful
step, commit `agent-A2: ...`.

## Stop conditions

- 60 min wall clock exceeded
- Z3 OOM kill on same target twice
- F\* segfault twice on same target
- Both targets handled (proven, or admit-with-comment-with-additional-detail)

## Final deliverable

1. Final status commit on `agent-A.md`
2. `make Libcrux_ml_kem.Vector.Portable.fst.checked` final regression run, time recorded
3. Concise summary back to parent: count newly proven (0-2), last commit hash, verification time

## Hard rules

- DO NOT push to origin.
- DO NOT merge to `trait-opacify`.
- DO NOT touch other agents' branches.
- DO NOT exceed F\* rlimit 800.
- DO NOT alter Rust function bodies of `op_*`.
- DO NOT regress the 4 already-proven admits.
