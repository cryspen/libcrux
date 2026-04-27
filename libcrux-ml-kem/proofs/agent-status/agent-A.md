# Agent A — Phase 6 portable NTT admit drops

**Branch**: agent/phase-6-portable-ntt
**Brief**: see proofs/agent-status/agent-A-brief.md on trait-opacify
**Worktree**: /Users/karthik/libcrux/.claude/worktrees/agent-a7fe3b80a83ae3715
**Base commit**: fc5aa244a

## Targets
- [x] op_ntt_layer_3_step  (start here) — verified with --z3rlimit 200 --split_queries always
- [x] op_inv_ntt_layer_3_step — same recipe
- [x] op_ntt_layer_2_step — same recipe
- [ ] op_inv_ntt_layer_2_step — fails at rlimit 200
- [ ] op_ntt_layer_1_step — fails at rlimit 200
- [ ] op_inv_ntt_layer_1_step — fails at rlimit 200

## Progress (append-only, newest at bottom)

### 2026-04-27 19:17:35 UTC — Started
Branched from trait-opacify tip fc5aa244a. Read brief, MLKEM_STATUS, session-handoff, proof-style-guide.
Reviewed AVX2 ntt_layer_3_step / inv_ntt_layer_3_step templates — they use `--z3rlimit 200 --split_queries always`.
Portable scaffold currently has only `--admit_smt_queries true`; need to add `--z3rlimit 200 --split_queries always` and drop the admit.

### 2026-04-27 19:35 UTC — env setup
Copied F* extraction artifacts + .depend (with paths rewritten) from main worktree at /Users/karthik/libcrux-trait-opacify.
Symlinked .fstar-cache/{checked,hints} to main worktree caches (shared, content-keyed).
Baseline `make Vector.Portable.fst.checked` passes in 17s with admits in place.

### 2026-04-27 19:42 UTC — first attempt (drop layer 3 admit)
Edited F* file directly: replaced `#push-options "--admit_smt_queries true"` with `#push-options "--z3rlimit 200 --split_queries always"` for op_ntt_layer_3_step.
Verified: All VC discharged, 20.5s. PASS.

### 2026-04-27 19:48 UTC — bulk drop attempt (all 6)
Replaced all 6 admit push_options with rlimit 200 + split_queries always. F* fails at op_ntt_layer_1_step (Error 19 at lines 326-400) — Assertion failed.
Then restored layer_1 + inv_layer_1 admits; F* fails at op_inv_ntt_layer_2_step (Error 19 at 664-758).
Then restored inv_layer_2 admit. PASS in 38s with 3 admits dropped:
  op_ntt_layer_3_step, op_inv_ntt_layer_3_step, op_ntt_layer_2_step.

Mirrored those 3 changes to src/vector/portable.rs (lines 410, 488, 718 — same `--z3rlimit 200 --split_queries always` swap).

### 2026-04-27 19:55 UTC — analysis of remaining 3 failures
Failing targets: op_inv_ntt_layer_2_step, op_ntt_layer_1_step, op_inv_ntt_layer_1_step.
Common shape: 4 zeta groups (or asymmetric inv direction with widening reveals).
Layer 2 inv has the Barrett-widening reveal (3328 → 2*3328) before the assertion block — extra reveal_opaque step compared to ntt_layer_2_step.
Layer 1 (both) has the largest predicate (4 zeta groups, 4 calls per branch = 16 lemma calls).
Try: bump rlimit to 400 / 800 first; if still fails, refactor or admit.
