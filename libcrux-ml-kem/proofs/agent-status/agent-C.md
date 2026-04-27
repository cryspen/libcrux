# Agent C — Phase 6c AVX2 Sampling/Compress admits

**Branch**: agent/phase-6c-avx2-stragglers
**Brief**: see proofs/agent-status/agent-C-brief.md on trait-opacify
**Worktree**: /Users/karthik/libcrux-agent-C-phase6c

## Targets
- [ ] C1: lemma_mm256_xor_si256_lane (compress.rs:40 / extracted line 35)
- [ ] C2: lemma_mm256_srli_epi16_15  (compress.rs:48 / extracted line 43)
- [x] C3: lemma_i16_xor_neg1         (compress.rs:62 / extracted line 57)
- [x] C4: lemma_i16_xor_zero         (compress.rs:67 / extracted line 62)
- [ ] C5: rejection_sample panic_free body (sampling.rs Rust assumes / extracted line 98)

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
