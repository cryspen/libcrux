# Agent C2 — Phase 6c follow-up: stretch goals on the 3 admit-with-comment targets

Continuation of agent C's run on branch `agent/phase-6c-avx2-stragglers`
(tip `aa48507b5`).  Agent C landed C3, C4 proven and documented C1, C2,
C5 with admit-with-comment + clear next-step recipes.  This brief tells
C2 to attempt those next steps.

## Mission (in priority order — drop a target if it doesn't go in budget)

1. **C5** (`rejection_sample` panic_free body): strengthen the
   `mm256_cmpgt_epi16` post in
   `crates/utils/intrinsics/proofs/fstar/extraction/Libcrux_intrinsics.Avx2_extract.fsti:175–181`
   to expose the comparison semantics, then close the `count_ones <= 8`
   chain.  Highest-value target — agent C identified the post-strengthening
   work explicitly.
2. **C1** / **C2** (Vec256 model gap): try the brief's "strengthen
   `mm256_xor_si256` post + add `lemma_vec256_as_i16x16_*` bit-extraction
   lemma" path.  This requires SPEC changes to
   `Libcrux_intrinsics.Avx2_extract.fsti` — per user policy, spec changes
   are OK if they make impl proofs go through.

## Required reading (in order)

1. Agent C's log on branch `agent/phase-6c-avx2-stragglers`:
   `proofs/agent-status/agent-C.md` — esp. the in-line analysis of C5
   and the recommended next steps.
2. The in-source comments agent C wrote in
   `src/vector/avx2/{compress,sampling}.rs` `fstar::before` blocks —
   they describe what's missing.
3. `crates/utils/intrinsics/proofs/fstar/extraction/Libcrux_intrinsics.Avx2_extract.fsti`
   — current weak posts for `mm256_xor_si256`, `mm256_srli_epi16`,
   `mm256_cmpgt_epi16`.
4. `proofs/simd-model-unification-plan.md` — context for why the
   `vec256_as_i16x16` `val`-only abstraction exists.

## Operating constraints

- **Wall clock**: 45 min total.
- **Per-target budget**: ~15 min.  If a target doesn't go through,
  re-restore agent C's admit-with-comment, commit, move on.
- **Memory**: `ulimit -v 8388608`, `--z3cliopt smt.memory_max_size=8000`.
- **F\* concurrency**: at most 1 F\* process at a time.
- **F\* rlimit**: never exceed 800.
- **Tooling**: plain `make` for verification.

## Code change policy (delta from original C brief)

- **Rust function bodies**: still NOT touched.
- **`fstar::before` helper-lemma blocks**: editable.
- **`Libcrux_intrinsics.Avx2_extract.fsti`** posts: **editable** — this
  is the spec strengthening agent C identified.  Allowed because:
  - User policy: "Changing the spec structure is more often ok"
  - The strengthening must remain consistent with the actual SIMD
    intrinsics — describe the strengthening in a comment alongside.
  - **Test downstream**: after strengthening, run `make` for at least
    `Libcrux_ml_kem.Vector.Avx2.{Compress,Sampling,Ntt,Arithmetic,Serialize}.fst.checked`
    to ensure no other consumer regresses.  If anything regresses,
    revert the strengthening; that target falls back to admit-with-comment.

## Useful pointers (from agent C's analysis)

- `Rust_primitives.Integers.logxor_lemma` is the one-stop lemma for
  i16/u16 xor identities — reuse if patterns recur.
- `count_ones_u8`'s return type is `r:u32{v r <= 8}` — refinement gives
  bound for free; multiple `assume` blocks can become `assert`.  Agent
  C cleaned 2 of these in `sampling.rs`; check if more remain.
- The `vec256_as_i16x16` `val`-only abstraction is the structural
  blocker for C1/C2.  If you can't strengthen it, fall back gracefully
  to the existing admit-with-comment.

## Eager-commit logging

Continue updating `proofs/agent-status/agent-C.md` on the agent's branch.
Append `## Phase 6c follow-up (agent C2) — YYYY-MM-DD`.  Commit eagerly.

## Stop conditions

- 45 min wall clock exceeded
- Z3 OOM kill on same target twice
- F\* segfault twice on same target
- All targets attempted (proven, or restored admit-with-comment)
- A spec strengthening regresses ≥1 downstream module that doesn't
  recover within 5 minutes — revert and admit

## Final deliverable

1. Final status commit on `agent-C.md`
2. Final `make` regression on the affected modules, times recorded
3. Concise summary back to parent: count newly proven (0–3), spec
   strengthening landed (yes/no, which posts), last commit hash, any
   downstream regressions encountered

## Hard rules

- DO NOT push to origin.
- DO NOT merge to `trait-opacify`.
- DO NOT touch other agents' branches.
- DO NOT exceed F\* rlimit 800.
- DO NOT regress C3, C4 (already proven), or any module currently
  passing.
