# agent-trackD — session log

**Session date:** 2026-04-28
**Branch:** `agent/phase-7a-step-7` (in worktree `agent-a513e4593e611de20`)
**Tip at end:** `5922b5721`
**Forked from:** `trait-opacify` tip `86a0c31a2`

## Scope

Phase 7a Step 7 of `/Users/karthik/.claude/plans/replicated-beaming-pnueli.md`:
**`add_standard_error_reduce` post-strengthening** — write the F* per-lane
Mont→plain commute lemma analogous to agent F's `lemma_intt_mont_finalize_fe`
but for the `to_standard_domain` (matrix-mul) track, then strengthen the
Rust `add_standard_error_reduce` post + body proof.

## What landed (verified)

### `specs/ml-kem/proofs/fstar/commute/Hacspec_ml_kem.Commute.Chunk.fst`

NEW lemmas in the "Phase 7a Step 7 — to_standard_domain finalization
(matrix-mul track)" section:

| Lemma / definition | Purpose | Verified |
|---|---|---|
| `lemma_1353_eq_R` | Numeric `1353·169 ≡ 2285 (mod q)` and `2285·169 ≡ 1 (mod q)` | ✅ |
| `lemma_mont_form_post` | Int-level core: `mont_mul(myself, 1353)` recovers plain | ✅ |
| `mont_form_lane` | Opaque per-lane `·R⁻¹` form predicate | ✅ |
| `lemma_mont_form_lane_reveal/intro` | Opacity helpers | ✅ |
| `mont_form_chunk` | Per-chunk wrap via `forall16` | ✅ |
| `lemma_to_standard_domain_finalize_fe` | Per-lane consumer (mirror of `lemma_intt_mont_finalize_fe`) | ✅ |
| `lemma_add_standard_error_reduce_lane` | Full lane bridge (mont_mul + add + barrett ⟹ FE-add equation) | ✅ |
| `lemma_add_standard_error_reduce_commute` | Tier-1 poly-level commute (256 lane equations → hacspec function identity, parameterized by ghost `ntt_product`) | ✅ |

Module verifies clean at rlimit 400 with `--split_queries always`
(`lemma_add_standard_error_reduce_commute`); other Step 7 lemmas at
default rlimit 80.  Full module re-verifies in **65 s**.

### `libcrux-ml-kem/src/polynomial.rs`

`add_standard_error_reduce` body unchanged (reverted from attempted
strengthening — see "Held work" below).  Added a detailed TODO comment
block above the function documenting:
- The F* infrastructure that is now landed and verified.
- The blocker (Z3 ~85 s/query timeout on loop-accumulator subtyping).
- Suggested next steps for follow-up.

`Libcrux_ml_kem.Polynomial.fst.checked` re-verifies clean (73 s) with
NO regression vs trait-opacify tip `86a0c31a2`.

## Held work (Step 7.2)

Attempted to strengthen `add_standard_error_reduce`'s Rust post to:
```fstar
forall (k l: nat). k < 16 /\ l < 16 ==>
  (forall (ntt_lane: P.t_FieldElement).
    Hacspec_ml_kem.Commute.Chunk.mont_form_lane (orig.[k].[l]) ntt_lane
    ==> i16_to_spec_fe (myself_future.[k].[l])
        == FE.add ntt_lane (i16_to_spec_fe (error.[k].[l])))
```

The loop body invokes `lemma_add_standard_error_reduce_lane` per lane
inside a `Classical.move_requires` to discharge the per-chunk parameterized
FE-add equation in the strengthened invariant.

**Blocker:** at rlimit 800 with `--split_queries always`, Z3 timed out
(~85 s wall clock per query, 4 errors) on:
- `Polynomial.fst:843` — assertion failure inside the
  `Classical.move_requires (fun _ -> lemma_add_standard_error_reduce_lane …)`
  call site (lemma's preconditions about the trait posts not visible).
- `Polynomial.fst:855, 859` — subtyping check on the loop accumulator
  refinement (the strengthened invariant on the post-update `myself`).

The infrastructure F* lemmas are all in place and verified.  The Rust
integration likely needs one of:
1. **Tighter loop invariant**: drop the inner `forall ntt_lane` and
   instead specialize per chunk-slice of an explicit ghost `ntt_product`
   parameter.  Trade-off: requires adding a ghost array param to the
   function (and threading it through the `impl` wrapper).
2. **External Tier-1 helper**: factor the body proof into an external
   lemma that reasons about the impl trace abstractly, then invoke it
   on a concrete trace.  Keeps the body proof single-pass.
3. **Investigate the 85 s cost**: profile the `Classical.move_requires`
   query via `--query_stats --log_queries` to identify which assertion
   inside the body proof is the actual hot spot.  May be a false-positive
   timeout.

Recommended approach for follow-up: try option (1) first — it most
closely mirrors the lemma's natural shape and avoids `move_requires`.

## Verification status (end of session)

| Module | Status | Time | Notes |
|---|---|---|---|
| `Hacspec_ml_kem.Commute.Chunk` | ✅ | 65 s | Step 7 lemmas added |
| `Libcrux_ml_kem.Polynomial` | ✅ | 73 s | Body unchanged from `86a0c31a2` |

`hax.py extract` exit 0 (final extraction includes the doc-comment-only
diffs to `Libcrux_ml_kem.Polynomial.fsti`).

## Commits (chronological)

| SHA | Message |
|---|---|
| `5922b5721` (HEAD) | agent-trackD: Step 7.1c — simplify lane lemma post; add Step 7.2 TODO |
| `bc3b214a7` | agent-trackD: Step 7.1b — poly-level commute lemma for add_standard_error_reduce |
| `d07959066` | agent-trackD: Step 7.1 — to_standard_domain finalize lemmas (F*) |

(Branched from `86a0c31a2` = `trait-opacify` tip.)

## Worktree bootstrap notes

The worktree at `/Users/karthik/libcrux/.claude/worktrees/agent-a513e4593e611de20`
was originally on a default branch with no `.fstar-cache` and an empty
`specs/ml-kem/proofs/fstar/extraction/` directory.  Bootstrapped by:
1. `git checkout -b agent/phase-7a-step-7 86a0c31a2` (trait-opacify tip).
2. Copied `.fstar-cache` (138 MB) from parent repo
   `/Users/karthik/libcrux-trait-opacify/.fstar-cache/`.
3. Copied `libcrux-ml-kem/proofs/fstar/extraction/` files from parent
   (147 files; gitignored, regenerated by `hax.py extract`).
4. Copied `specs/ml-kem/proofs/fstar/extraction/*.fst` from parent
   (12 files; gitignored).
5. Removed stale `Libcrux_ml_kem.Polynomial.{fst,fsti}.checked` and
   `Hacspec_ml_kem.Commute.{Chunk,Bridges}.fst.checked` to force re-verify.
6. Restored `Libcrux_ml_kem.Polynomial.fsti` from HEAD (parent had a WIP
   diff that was unrelated to Step 7).

This bootstrap is a one-time cost (~30 s for cache copy).  Subsequent
incremental builds via `hax.py extract` + `make` are fast.

## Lessons learned

1. **Nested-forall posts that look natural to humans (`forall k l. ... ==>
   (forall ntt_lane. mont_form_lane ==> FE-add)`) are Z3-hostile** in
   loop-invariant position — Z3 has to instantiate the inner `forall` per
   iteration, and the chain of `Classical.move_requires` cascades quantifier
   instantiations.  Use specialized per-chunk slices when possible.
2. **Hax doesn't accept F* `(* ... *)` block comments inside `fstar!()`
   raw strings** when that string is in a complex expression position
   (it parses fine in `#[hax_lib::fstar(...)]` annotations).  Strip
   comments from inline `fstar!()` calls.
3. **The 30-min-per-fn rule pays off**: detecting Z3 timeouts early
   and committing the F* infrastructure separately from the Rust
   integration preserves progress and lets a fresh agent attack the
   integration with a clean Z3 context.  Each attempt at the Rust
   integration cost ~5 min of make + ~85 s of timeout × 4 queries.

## Resume protocol (next agent)

```bash
cd /Users/karthik/libcrux/.claude/worktrees/agent-a513e4593e611de20
git status               # should be on agent/phase-7a-step-7, clean
git log --oneline -5     # tip = 5922b5721

# Optional regression check (fast — just Polynomial.fst):
ulimit -v 8388608
cd libcrux-ml-kem/proofs/fstar/extraction
make /Users/karthik/libcrux/.claude/worktrees/agent-a513e4593e611de20/.fstar-cache/checked/Libcrux_ml_kem.Polynomial.fst.checked
```

Read order:
1. **THIS FILE.**
2. The TODO block in `libcrux-ml-kem/src/polynomial.rs` above
   `add_standard_error_reduce` — describes the held work.
3. The new lemmas in `Hacspec_ml_kem.Commute.Chunk.fst` (§ "Phase 7a
   Step 7 — to_standard_domain finalization (matrix-mul track)").
4. `proofs/proof-style-guide.md` §12 (Mont-arithmetic-in-posts antipattern)
   for context on why the strengthened post is shaped the way it is.
