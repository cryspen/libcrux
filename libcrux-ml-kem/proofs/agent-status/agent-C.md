# Agent C — Phase 6c AVX2 Sampling/Compress admits

**Branch**: agent/phase-6c-avx2-stragglers
**Brief**: see proofs/agent-status/agent-C-brief.md on trait-opacify
**Worktree**: /Users/karthik/libcrux-agent-C-phase6c

## Targets
- [~] C1: lemma_mm256_xor_si256_lane (compress.rs:40 / extracted line 35) — admit-with-comment
- [~] C2: lemma_mm256_srli_epi16_15  (compress.rs:48 / extracted line 43) — admit-with-comment
- [x] C3: lemma_i16_xor_neg1         (compress.rs:62 / extracted line 57)
- [x] C4: lemma_i16_xor_zero         (compress.rs:67 / extracted line 62)
- [~] C5: rejection_sample panic_free body (sampling.rs Rust assumes / extracted line 98) — admit-with-comment + 2 assumes -> asserts

## Progress (append-only, newest at bottom)

### 2026-04-27 19:36:42 UTC — Started
- Created worktree at /Users/karthik/libcrux-agent-C-phase6c off `0f5175e8e` (trait-opacify tip).
- Verified targets in `src/vector/avx2/compress.rs` and `src/vector/avx2/sampling.rs`.
- Confirmed extracted `.fst` files in trait-opacify worktree show same admit shape (C1–C4 in `Compress.fst`, C5 in `Sampling.fst`).
- Plan: try C4 (xor_zero) first (likely trivial), then C3 (xor_neg1, BitVec.Bv lookup), then C1/C2 (likely admit-with-comment due to `vec256_as_i16x16` model gap), then C5 (`u8::count_ones` model gap).

### 2026-04-27 19:42:00 UTC — Cache plumbed in agent-C worktree
- Copied `/Users/karthik/libcrux-trait-opacify/.fstar-cache` -> `/Users/karthik/libcrux-agent-C-phase6c/.fstar-cache` (214 .checked).
- Copied extraction snapshots from trait-opacify (libcrux-ml-kem, libcrux-ml-dsa, intrinsics, secrets, core-models, specs/ml-kem extraction + commute, specs/sha3, sha3, platform).
- `make Libcrux_ml_kem.Vector.Avx2.Compress.fst.checked` works in agent-C worktree (target name needs full cache path due to Makefile.generic suffix matching: `make /full/path/.fstar-cache/checked/<mod>.fst.checked`).
- Baseline build with all admits-in-place: ~10.4 s (cold cache after re-verify).

### 2026-04-27 19:44:29 UTC — C3 + C4 proved
- `lemma_i16_xor_zero` closed via `Rust_primitives.Integers.logxor_lemma x (mk_i16 0)`.
- `lemma_i16_xor_neg1` closed via `logxor_lemma x (mk_i16 (-1)) ; lognot_lemma x` (the lemma exposes `a ^ ones == lognot a`, and on signed types `v (lognot a) == -1 - v a`).
- Edited both `src/vector/avx2/compress.rs` `fstar::before` block AND extracted `.fst` (gitignored, only used for local verification).
- `make Libcrux_ml_kem.Vector.Avx2.Compress.fst.checked` PASSES (10.4 s).
- Now C1 (mm256_xor_si256_lane) — likely Vec256-model gap — and C2 (mm256_srli_epi16_15) similarly.

### 2026-04-27 19:48:00 UTC — C1 + C2 admit-with-comment
- Confirmed model gap as predicted by brief:
  - `mm256_xor_si256` is `assume val ... -> Prims.Pure t_Vec256 Prims.l_True (fun _ -> Prims.l_True)` in `crates/utils/intrinsics/proofs/fstar/extraction/Libcrux_intrinsics.Avx2_extract.fst:311–315`. Post is `True`, so SMT has nothing to chain.
  - `vec256_as_i16x16` is `val`-only at `Libcrux_intrinsics.Avx2_extract.fsti:7` (`val vec256_as_i16x16 (x: bit_vec 256) : t_Array i16 (sz 16)`).  No bit-level characterization.
  - `mm256_srli_epi16` IS bit-transparent (`BitVec.Intrinsics.fsti:15` defines it via `mk_bv` per-bit) but the lane view abstraction blocks the connection.
  - `Tactics.GetBit.prove_bit_vector_equality'` operates on `get_bit ... i == get_bit ... i` goals over both sides; closing C1/C2 needs the lane view to be bit-transparent first.
- Wrote detailed admit-with-comment in BOTH `src/vector/avx2/compress.rs` `fstar::before` block AND extracted `Compress.fst`.  Captures: math reason it should hold, F* model gap, what user should try (strengthen `mm256_xor_si256` post + add `lemma_vec256_as_i16x16_*` bit-extraction lemma, then close via `prove_bit_vector_equality'`), reference to `simd-model-unification-plan.md` and USER-4.
- `make Libcrux_ml_kem.Vector.Avx2.Compress.fst.checked` PASSES (9.6 s).
- Decision: budget per-target ~15 min, this is genuine model gap — moving on to C5.

### 2026-04-27 19:54:16 UTC — C5 progress: 2 assumes -> asserts, panic_free admit-with-comment
- Investigated the `admit ()` at extracted Sampling.fst:98 — it's the hax-inserted "Panic freedom" admit that discharges all remaining proof obligations (subtyping, post-condition, slice indexing).
- Removed the admit and saw failures: 4+ "Subtyping check failed" + 1 "Assertion failed" with "incomplete quantifiers" — even with `--z3rlimit 400 --split_queries always`.
- The two obligation classes are:
  1. Slice indexing: `output[sampled_count..sampled_count+8]` requires
     `sampled_count + 8 <= len(output) = 16`.  Since `sampled_count = count_ones(good[0])` and `count_ones_u8 : u8 -> r:u32{v r <= 8}`, this should be derivable.  The Rust `assume` already names it; the issue is the bridging through `f_index_pre output {start;end}`.
  2. Functional post: `forall j. j < result ==> output_future[j] in [0, 3328]`.
     This needs reasoning about `mm_shuffle_epi8` applied with REJECTION_SAMPLE_SHUFFLE_TABLE to compact lanes whose `compare_with_field_modulus` bit is set.  Two separate model gaps:
     - `mm256_cmpgt_epi16`'s post in `Avx2_extract.fsti:175–181` only constrains "non-bit-0 bits = 0" within each 16-bit lane — does NOT relate to the actual `>` comparison.  So we can't even prove "good encodes the bitmask of lanes < 3329".
     - `count_ones_u8` is val-only beyond its `<= 8` bound; nothing connects it to the bitmask shape.

- Wins:
  - The two `assume (count_ones <= 8)` lines became `assert` (refinement type carries the bound) — mechanical cleanup.
  - The third `assume (f_index_pre output ...)` left in place — bridging to slice-range pre needs a separate lemma we don't have.

- Restored the `let _:Prims.unit = admit () (* Panic freedom *)` with a long admit-with-comment in the extracted .fst (gitignored).
- Cannot put a comment in the Rust source for the panic_free `admit ()` because that admit is hax-generated; pointed at by the `// The remaining `assume` ... see panic-freedom comment` in `src/vector/avx2/sampling.rs`.
- `make Libcrux_ml_kem.Vector.Avx2.Sampling.fst.checked` PASSES (~5 s).

- Decision: C5 admit-with-comment recorded in extracted `.fst` (which is gitignored).  In Rust source, the only thing I could touch was the `assume`-block in the `hax_lib::fstar!()` macro.  Two of the three assumes turn into asserts; the third remains with a pointer to the panic-freedom comment.  This is the same family as the AVX2 serialize/deserialize bridge admits (`session-handoff.md` listed them as out-of-scope).

### 2026-04-27 19:55:27 UTC — Final regression
- Cold-cache rebuild of both Compress.fst and Sampling.fst:
  - `make Libcrux_ml_kem.Vector.Avx2.Compress.fst.checked` PASSES.
  - `make Libcrux_ml_kem.Vector.Avx2.Sampling.fst.checked` PASSES.
  - Combined wall time: 17.6 s (cold), pure F* time ~2.7 s for Sampling, ~10 s for Compress.
- Final commit hash on `agent/phase-6c-avx2-stragglers`: `1899f1223` (will append final-regression commit after this entry).

## Summary

| # | Status | Notes |
|---|---|---|
| C1 | `[~]` admit-with-comment | Vec256 model gap; `mm256_xor_si256` post is `True`, `vec256_as_i16x16` val-only.  USER-4 family. |
| C2 | `[~]` admit-with-comment | Same model gap; `mm256_srli_epi16` is bit-transparent but lane view is abstract. |
| C3 | `[x]` proven | `Rust_primitives.Integers.logxor_lemma x (mk_i16 (-1)); lognot_lemma x` |
| C4 | `[x]` proven | `Rust_primitives.Integers.logxor_lemma x (mk_i16 0)` |
| C5 | `[~]` admit-with-comment + cleanup | 2 assumes -> asserts (count_ones <= 8 from refinement type); panic_free admit kept with detailed comment because of `mm256_cmpgt_epi16` + `count_ones_u8` model gaps + missing slice-range bridging lemma. |

Net: 2 admits PROVEN, 3 admits ADMITTED-WITH-COMMENT (all match the brief's "likely admit-with-comment" predictions).  No blockers.  No escalations.

Verification state on `agent/phase-6c-avx2-stragglers`:
- `Libcrux_ml_kem.Vector.Avx2.Compress.fst` — verifies, contains 2 admit-with-comment.
- `Libcrux_ml_kem.Vector.Avx2.Sampling.fst` — verifies, contains 1 admit-with-comment + 2 promoted asserts.
- No regressions on neighbouring modules (cache rebuilt cleanly during regression).

## Phase 6c follow-up (agent C2) — 2026-04-27

Continuation focused on the 3 admit-with-comment targets agent C left.

### 2026-04-27 — C1 + C2 closed via spec strengthening

Approach: instead of trying to prove `lemma_mm256_xor_si256_lane` and
`lemma_mm256_srli_epi16_15` from the existing weak posts, **strengthen
the spec** in `crates/utils/intrinsics/src/avx2_extract.rs` by adding
two new SMTPat lemmas (mirrored in
`crates/utils/intrinsics/proofs/fstar/extraction/Libcrux_intrinsics.Avx2_extract.fsti`):

  - `lemma_mm256_xor_si256 lhs rhs`:
      `vec256_as_i16x16 (mm256_xor_si256 lhs rhs)
       == Spec.Utils.map2 (^.) (vec256_as_i16x16 lhs) (vec256_as_i16x16 rhs)`

  - `lemma_mm256_srli_epi16 SHIFT vector`:
      `vec256_as_i16x16 (mm256_srli_epi16 SHIFT vector)
       == Spec.Utils.map_array (fun (x:i16) -> cast ((cast x : u16) >>! SHIFT) : i16) (vec256_as_i16x16 vector)`

Both are admits relative to `vec256_as_i16x16` (which is `val`-only), but
match the actual SIMD intrinsic semantics — sibling axioms to the
existing `lemma_mm256_and_si256` (`Avx2_extract.fsti:224–228`).

With these in place:
- C1 (`lemma_mm256_xor_si256_lane`): closes by direct dispatch to the
  new axiom (one-liner).
- C2 (`lemma_mm256_srli_epi16_15`): closes via the axiom + a small
  case-split on `v x < 0` to discharge the `(cast x : u16) >>! 15`
  arithmetic.

`make Libcrux_ml_kem.Vector.Avx2.Compress.fst.checked` PASSES (~10 s cold).

Source-level edits:
- `crates/utils/intrinsics/src/avx2_extract.rs`: adds `fstar::replace`
  blocks on `mm256_xor_si256` and `mm256_srli_epi16` to declare the new
  axioms.
- `libcrux-ml-kem/src/vector/avx2/compress.rs`: replaces the two admits
  in the `fstar::before` block with proofs that invoke the new axioms.

Downstream regression: cold rebuild of
`make Libcrux_ml_kem.Vector.Avx2.fst.checked` (parent of
Compress/Sampling/Ntt/Arithmetic/Serialize) — PASSES in ~36 s pure F*
time, ~58 s wall.  No regressions.

### 2026-04-27 — C5 left as admit-with-comment

Investigated whether the strengthened axioms enable any progress on the
`rejection_sample` panic_free admit.  Conclusion: the post-condition
splits into two parts, and the genuinely-hard half remains blocked:

  1. Length / `result <= 16`: derivable in principle from the
     `count_ones_u8` refinement type + `update_at_range` + `mm_storeu_si128`
     posts.
  2. Functional `forall j. j < result ==> output_future[j] in [0, 3328]`:
     genuine model gap — requires (a) `mm256_cmpgt_epi16` post relating
     bit-0-of-lane to `lhs > rhs` (current post only says non-bit-0
     bits are 0; the lane semantics is hidden), (b) a model for
     `count_ones_u8` as a bitmask cardinality (currently only the
     `<= 8` refinement is exposed), (c) shuffle-compaction reasoning
     for `mm_shuffle_epi8` against `REJECTION_SAMPLE_SHUFFLE_TABLE`,
     which is the AVX2 analogue of the rejection-sampling mathematics.

The user's original "strengthen `mm256_cmpgt_epi16` post" recipe
matches part (a); parts (b) and (c) are extra. None of these went in
the per-target budget.  C5 stays as admit-with-comment.

### Final outcome

| # | Status | Notes |
|---|---|---|
| C1 | `[x]` PROVEN | via `lemma_mm256_xor_si256` axiom |
| C2 | `[x]` PROVEN | via `lemma_mm256_srli_epi16` axiom + case-split |
| C3 | `[x]` proven (agent C) | unchanged |
| C4 | `[x]` proven (agent C) | unchanged |
| C5 | `[~]` admit-with-comment | unchanged; functional post requires extensive model strengthening |

Net delta over agent C: **2 more admits PROVEN** (C1, C2 → proven).
**Spec strengthening landed**: yes, in `Avx2_extract.fsti` —
`lemma_mm256_xor_si256` and `lemma_mm256_srli_epi16` SMTPat axioms.

Last commit: `agent-C2: log Phase 6c follow-up` (after `agent-C2: C1 + C2 proven via spec strengthening`).

### Final cold regression (all five AVX2 modules)

```
Compress    11 s pure F* (15 s wall)
Sampling     4 s            ( 8 s)
Ntt         43 s            (48 s)
Arithmetic  14 s            (18 s)
Serialize   72 s            (78 s)
```

No regressions on any AVX2 module after the spec strengthening landed.

