# Agent A — Phase 6 portable NTT admit drops

**Branch**: agent/phase-6-portable-ntt
**Brief**: see proofs/agent-status/agent-A-brief.md on trait-opacify
**Worktree**: /Users/karthik/libcrux/.claude/worktrees/agent-a7fe3b80a83ae3715
**Base commit**: fc5aa244a

## Targets
- [ ] op_ntt_layer_3_step  (start here)
- [ ] op_inv_ntt_layer_3_step
- [ ] op_ntt_layer_2_step
- [ ] op_inv_ntt_layer_2_step
- [ ] op_ntt_layer_1_step
- [ ] op_inv_ntt_layer_1_step

## Progress (append-only, newest at bottom)

### 2026-04-27 19:17:35 UTC — Started
Branched from trait-opacify tip fc5aa244a. Read brief, MLKEM_STATUS, session-handoff, proof-style-guide.
Reviewed AVX2 ntt_layer_3_step / inv_ntt_layer_3_step templates — they use `--z3rlimit 200 --split_queries always`.
Portable scaffold currently has only `--admit_smt_queries true`; need to add `--z3rlimit 200 --split_queries always` and drop the admit.
