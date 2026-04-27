# Agent E — Phase 7a: Polynomial scalar ops post-strengthening

Wave 2.  Brand new branch `agent/phase-7a-polynomial` from `trait-opacify`
tip `81e201c73`.

## Mission

Strengthen post-conditions of 7 functions in
`libcrux-ml-kem/src/polynomial.rs` to cite `Hacspec_ml_kem.Polynomial.*`
alongside any existing assertions.  Add Tier-1 chunk-commute lemmas in
`specs/ml-kem/proofs/fstar/commute/Hacspec_ml_kem.Commute.Chunk.fst`
where needed.  All changes are POST-ONLY and ADDITIVE.

These lemmas become inputs for Phase 7b (Ntt + Invert_ntt) and Phase 7d
(Matrix), so Wave 3 is gated on this work.

## Targets (in priority order — easier first)

| # | Rust fn | Hacspec counterpart | Notes |
|---|---|---|---|
| E1 | `poly_barrett_reduce` (line ~262) | `Hacspec_ml_kem.Polynomial.poly_barrett_reduce` | Per-vector trait post (`barrett_reduce_post`) → per-poly hacspec equation |
| E2 | `add_to_ring_element` (line ~236) | `Hacspec_ml_kem.Polynomial.add_to_ring_element` | Loop over 16 vectors, per-vector add; commute is direct |
| E3 | `subtract_reduce` (line ~287) | `Hacspec_ml_kem.Polynomial.subtract_reduce` | Same shape as E2 with sub + barrett |
| E4 | `add_error_reduce` (line ~392) | `Hacspec_ml_kem.Polynomial.add_error_reduce` | add + montgomery + barrett |
| E5 | `add_standard_error_reduce` (line ~440) | `Hacspec_ml_kem.Polynomial.add_standard_error_reduce` | Same shape |
| E6 | `add_message_error_reduce` (line ~337) | `Hacspec_ml_kem.Polynomial.add_message_error_reduce` | Decompress + add + barrett |
| E7 | `multiply_by_constant_bounded` (line ~114) | (no obvious Hacspec_ml_kem counterpart) | Skip if no canonical hacspec function exists; flag in log |

Do them in priority order.  If a target proves stubborn (can't close in
~25 min including its chunk-commute lemma), restore the previous post,
add an English admit-with-comment in the new conjunct, commit, move on.

## Required reading (in order)

1. `libcrux-ml-kem/MLKEM_STATUS.md` — Phase 7a section
2. `libcrux-ml-kem/proofs/session-handoff.md`
3. `libcrux-ml-kem/proofs/proof-style-guide.md` — esp. §3.4–§3.7
4. **Existing per-element commute templates** in
   `Hacspec_ml_kem.Commute.Chunk.fst`: A1–A4 (NTT base-case), A5–A7
   (compress/decompress).  These mirror what you'll write for Tier-1
   poly composition.
5. `Hacspec_ml_kem.Polynomial.fst` — canonical spec
6. **Don't conflict with Agent B'** — B' is currently editing
   `Hacspec_ml_kem.Commute.Chunk.fst` to scaffold L1 sub-lemmas for
   Serialize bit-vector bridges.  Add YOUR new chunk-commute lemmas in
   a clearly-marked `(*** Phase 7a Tier-1 commute lemmas — Polynomial ***)`
   section, separate from B's edits.  Merge will reconcile via standard
   git, but keep the section separation.

## Recipe (per target)

For each target `f`:

**Step 1**: Identify the per-vector trait post used by `f`'s body
(`barrett_reduce_post`, `add_post`, etc.) in
`src/vector/traits.rs::spec`.

**Step 2**: Add a Tier-1 chunk-commute lemma in
`Hacspec_ml_kem.Commute.Chunk.fst`:
```fstar
let lemma_<f>_poly_commute (...args...) : Lemma
  (requires (per-vector trait posts hold for each of the 16 chunks))
  (ensures result_as_hacspec_poly == Hacspec_ml_kem.Polynomial.<f> input_as_hacspec_poly)
  = (* use Classical.forall_intro over 16 vectors;
       per-vector commute is direct from existing trait posts *)
```
The proof is straightforward iteration if each per-vector post is a
clean per-lane FE equation (the pattern Phases 1–5 set up).

**Step 3**: Strengthen the Rust function's `#[hax_lib::ensures(...)]`
to include `result_as_hacspec_poly == Hacspec_ml_kem.Polynomial.<f> input_as_hacspec_poly`
as a new conjunct.

**Step 4**: In the Rust body's loop, invoke the chunk-commute lemma
once at loop exit (or in the loop invariant) to discharge the new
conjunct.

**Step 5**: Re-extract + verify with `make`.

## Operating constraints

- **Wall clock**: 150 min total.
- **Per-target budget**: ~22 min (7 targets × 22 = 154 min ≈ budget).
- **Memory**: `ulimit -v 8388608`, `--z3cliopt smt.memory_max_size=8000`.
- **F\* concurrency**: at most 1 F\* process at a time.
- **F\* rlimit**: never exceed 800.

## Code change policy

- **Rust function bodies**: editable for **loop invariant strengthening
  ONLY**.  No algorithmic changes; no new branches; no statement
  reordering.
- **`#[hax_lib::ensures(...)]`**: editable to ADD the Hacspec citation
  as a new conjunct.  Existing conjuncts STAY.
- **`#[hax_lib::requires(...)]`**: do NOT touch.
- **`Hacspec_ml_kem.Commute.Chunk.fst`**: editable for new Tier-1
  lemmas.  Add them in a clearly-labeled `Phase 7a` section near end
  of file.  Do NOT modify existing lemmas.  Be mindful of B's
  potential concurrent edits.
- **Trait-side opaque per-lane predicates** in `traits.rs::spec`: do
  NOT redesign.  Use as-is.

## Tooling

Default plain `make Libcrux_ml_kem.Polynomial.fst.checked` (the heaviest
target) plus `make Libcrux_ml_kem.Vector.Portable.fst.checked` if you
modify shared infrastructure.  fstar-mcp on port **3005** ONLY if you
iterate ≥5 times on `Hacspec_ml_kem.Commute.Chunk.fst` content.

Trait-opacify shares `.fstar-cache/checked` across worktrees, so cold
builds will be fast for unchanged modules.

## Eager-commit logging — CRITICAL

Maintain `libcrux-ml-kem/proofs/agent-status/agent-E.md` on your
branch.  After every meaningful step, append timestamped entry,
`git add`, `git commit -m "agent-E: ..."`.

Initial log skeleton:

```markdown
# Agent E — Phase 7a Polynomial scalar ops

**Branch**: agent/phase-7a-polynomial
**Brief**: see proofs/agent-status/agent-E-brief.md on trait-opacify

## Targets (7)
- [ ] E1: poly_barrett_reduce
- [ ] E2: add_to_ring_element
- [ ] E3: subtract_reduce
- [ ] E4: add_error_reduce
- [ ] E5: add_standard_error_reduce
- [ ] E6: add_message_error_reduce
- [ ] E7: multiply_by_constant_bounded (skip if no hacspec counterpart)

## Progress (append-only, newest at bottom)

### YYYY-MM-DD HH:MM:SS UTC — Started
...
```

Use `[x]` (proven), `[~]` (admit-with-comment), `[!]` (blocker),
`[?]` (skipped — no hacspec counterpart).

## Stop conditions

- 150 min wall clock exceeded
- Z3 OOM kill on same target twice
- F\* segfault twice on same target
- All 7 targets handled

## Final deliverable

1. Final status commit on `agent-E.md`
2. `make Libcrux_ml_kem.Polynomial.fst.checked` final regression run, time recorded
3. Concise summary: count proven / admit-with-comment / skipped, last commit hash on
   `agent/phase-7a-polynomial`, verification time, regressions if any

## Hard rules

- DO NOT push.
- DO NOT merge to `trait-opacify`.
- DO NOT touch other agents' branches or files outside scope.
- DO NOT exceed F\* rlimit 800.
- DO NOT modify Rust function bodies algorithmically.
- DO NOT remove existing post conjuncts.

## Concurrency note

Agent B' is running concurrently on `agent/phase-7c-serialize` editing
`Hacspec_ml_kem.Commute.Chunk.fst` (adding L1/L2/L3 sub-lemma stubs for
Serialize bit-vector bridges).  You'll be on a different branch, so no
direct conflict; merge-time conflicts will be resolved by parent.
Just keep your additions in a clearly-labeled section.
