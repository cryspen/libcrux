# Agent C — Phase 6c AVX2 Sampling/Compress admits

**Branch**: agent/phase-6c-avx2-stragglers
**Brief**: see proofs/agent-status/agent-C-brief.md on trait-opacify
**Worktree**: /Users/karthik/libcrux-agent-C-phase6c

## Targets
- [ ] C1: lemma_mm256_xor_si256_lane (compress.rs:40 / extracted line 35)
- [ ] C2: lemma_mm256_srli_epi16_15  (compress.rs:48 / extracted line 43)
- [ ] C3: lemma_i16_xor_neg1         (compress.rs:62 / extracted line 57)
- [ ] C4: lemma_i16_xor_zero         (compress.rs:67 / extracted line 62)
- [ ] C5: rejection_sample panic_free body (sampling.rs Rust assumes / extracted line 98)

## Progress (append-only, newest at bottom)

### 2026-04-27 19:36:42 UTC — Started
- Created worktree at /Users/karthik/libcrux-agent-C-phase6c off `0f5175e8e` (trait-opacify tip).
- Verified targets in `src/vector/avx2/compress.rs` and `src/vector/avx2/sampling.rs`.
- Confirmed extracted `.fst` files in trait-opacify worktree show same admit shape (C1–C4 in `Compress.fst`, C5 in `Sampling.fst`).
- Plan: try C4 (xor_zero) first (likely trivial), then C3 (xor_neg1, BitVec.Bv lookup), then C1/C2 (likely admit-with-comment due to `vec256_as_i16x16` model gap), then C5 (`u8::count_ones` model gap).
