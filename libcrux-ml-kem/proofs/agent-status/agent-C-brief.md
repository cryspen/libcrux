# Agent C — Phase 6c: AVX2 Sampling/Compress admit drops

Brief for the agent originally spawned on branch
`agent/phase-6c-avx2-stragglers`.  Eager-commit log lives at
`proofs/agent-status/agent-C.md` on that branch.

## Mission

Investigate and (where feasible) close the F\* admits in
`libcrux-ml-kem/src/vector/avx2/{sampling,compress}.rs`'s `fstar::before`
helper-lemma blocks.  Where a proof isn't tractable in the per-target
budget, replace `admit ()` with `admit ()` + an English comment that
records what was tried, hypothesis why it should hold, and a pointer for
the user to attack later.

## Required reading (in order)

1. `libcrux-ml-kem/MLKEM_STATUS.md` — Phase 6c table, "Genuinely out of scope" row
2. `libcrux-ml-kem/proofs/session-handoff.md`
3. `libcrux-ml-kem/proofs/proof-style-guide.md`
4. The 5 admit sites listed below, with surrounding context

## Targets (5 admits — line numbers may drift)

In `src/vector/avx2/compress.rs` (4 admits in the `fstar::before` block
of `compress_message_coefficient` or similar):

| # | Lemma | Admit at line | What it asserts |
|---|---|---|---|
| C1 | `lemma_mm256_xor_si256_lane` | 40 | per-lane xor on Vec256: `(xor lhs rhs).[i] == lhs.[i] ^. rhs.[i]` |
| C2 | `lemma_mm256_srli_epi16_15` | 48 | per-lane srli-15: produces 1 iff lane is negative, else 0 |
| C3 | `lemma_i16_xor_neg1` | 62 | bitvector fact: `v (x ^. mk_i16 (-1)) == -(v x) - 1` |
| C4 | `lemma_i16_xor_zero` | 67 | bitvector fact: `v (x ^. mk_i16 0) == v x` |

In `src/vector/avx2/sampling.rs` (1 admit, panic-freedom):

| # | Site | Admit at line | What it concerns |
|---|---|---|---|
| C5 | `rejection_sample` panic_free body | ~98 (in extracted `Vector.Avx2.Sampling.fst`) | Hooked to `u8::count_ones` model gap |

## Operating constraints

- **Wall clock**: 90 min total.
- **Per-target budget**: ~15 min.  If proof doesn't go through, leave
  `admit ()` in place but **add an English comment immediately above**
  describing:
  - what mathematical fact the lemma asserts (one line)
  - why you think the proof should work (e.g., "follows from BitVec.Bv
    decomposition" / "blocked on abstract `vec256_as_i16x16` model — see
    simd-model-unification-plan.md")
  - what the user should try (specific tactic / reference module)
  Commit and move on.
- **Memory**: `ulimit -v 8388608` on any shell that spawns F\*.
- **F\* concurrency**: at most 1 F\* process at a time.
- **F\* rlimit**: never exceed 800.

## Code change policy

- **Rust function bodies**: do NOT touch.
- **`fstar::before` helper-lemma blocks**: editable.  Replacing `admit ()`
  with a real proof body is the goal.  Adding new helper lemmas inside the
  block (or in a sibling block on the same Rust function) is fine.
- **Pre/post conditions on the wrapping Rust functions**: do NOT touch.
- **Hand-written F\* spec / utility files**: editable for new helper
  lemmas if they're broadly useful (e.g., add to
  `proofs/fstar/spec/Spec.Utils.fsti`).

## Likely approaches per target

Don't blindly apply these — read the failure first.  These are leads.

- **C1, C2** (Vec256 per-lane facts): require knowing the abstract
  `vec256_as_i16x16` model.  Proof-style-guide §7 notes this is a
  known SIMD model gap (see `proofs/simd-model-unification-plan.md`).
  Likely **admit-with-comment** outcome.  Possibly: try
  `Tactics.GetBit.prove_bit_vector_equality'` (used elsewhere in
  `Libcrux_intrinsics.Avx2_extract`).
- **C3** (`x ^. -1 == -(v x) - 1`): integer-bitvector fact.  Try
  `BitVec.Intrinsics.bv_xor_minus_one_eq_neg_minus_one` if it exists, or
  `BitVec.Bv.decompose_eq` plus per-bit reasoning.  Or `FStar.UInt.logxor`
  identities.
- **C4** (`x ^. 0 == x`): trivial bitvector fact.  Should close in a few
  lines if the right lemma exists.  Try `FStar.Int16.logxor_zero_left`,
  `FStar.UInt.logxor_lemma_1`, or `BitVec.Bv.xor_zero`.
- **C5** (rejection_sample panic_free): Z3 query inspection first
  (`--query_stats`).  Likely a `u8::count_ones` model gap; if so,
  admit-with-comment pointing at `Core_models.Num.fst`.

## Tooling decision

- **Default**: plain `make Libcrux_ml_kem.Vector.Avx2.Compress.fst.checked`
  and `make Libcrux_ml_kem.Vector.Avx2.Sampling.fst.checked`.  These files
  are smaller than `Vector.Portable.fst` (under 5 s each in cold cache).
- **fstar-mcp**: optional.  These admits are in `fstar::before` blocks of
  Rust files; each iteration requires re-extract.  Prefer `make`.
  If you do start fstar-mcp, use port **3004**.

## Eager-commit logging — CRITICAL

Maintain `libcrux-ml-kem/proofs/agent-status/agent-C.md` on your branch
`agent/phase-6c-avx2-stragglers`.  Append a timestamped entry after every
meaningful step, `git commit -m "agent-C: ..."`.

Initial log skeleton:

```markdown
# Agent C — Phase 6c AVX2 Sampling/Compress admits

**Branch**: agent/phase-6c-avx2-stragglers
**Brief**: see proofs/agent-status/agent-C-brief.md on trait-opacify

## Targets
- [ ] C1: lemma_mm256_xor_si256_lane (compress.rs:40)
- [ ] C2: lemma_mm256_srli_epi16_15 (compress.rs:48)
- [ ] C3: lemma_i16_xor_neg1 (compress.rs:62)
- [ ] C4: lemma_i16_xor_zero (compress.rs:67)
- [ ] C5: rejection_sample panic_free (sampling.rs:~98)

## Progress (append-only, newest at bottom)

### YYYY-MM-DD HH:MM:SS UTC — Started
...
```

Use `[x]` (proven), `[~]` (admit with English comment), `[!]` (blocker).

## Stop conditions

- 90 min wall clock exceeded
- Z3 OOM kill on same target twice
- F\* segfault on same target twice
- All 5 targets handled

## Final deliverable

1. Final status commit on `agent-C.md`
2. `make Libcrux_ml_kem.Vector.Avx2.{Compress,Sampling}.fst.checked` final regression
3. Concise summary back to parent: count proven / admitted-with-comment /
   blocker, last commit hash, verification state, any escalations

## Hard rules

- DO NOT push to origin.
- DO NOT merge to `trait-opacify`.
- DO NOT touch other agents' branches.
- DO NOT exceed F\* rlimit 800.
- DO NOT delete an `admit ()` without replacing it (real proof or
  admit-with-comment).
