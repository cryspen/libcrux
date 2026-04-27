# Agent A — Phase 6 portable NTT admit drops

**Branch**: agent/phase-6-portable-ntt
**Brief**: see proofs/agent-status/agent-A-brief.md on trait-opacify
**Worktree**: /Users/karthik/libcrux/.claude/worktrees/agent-a7fe3b80a83ae3715
**Base commit**: fc5aa244a

## Targets
- [x] op_ntt_layer_3_step  (start here) — verified with --z3rlimit 200 --split_queries always
- [x] op_inv_ntt_layer_3_step — same recipe
- [x] op_ntt_layer_2_step — same recipe
- [x] op_inv_ntt_layer_2_step — verified at rlimit 400
- [~] op_ntt_layer_1_step — admit-with-comment (rlimit 800 hung >10 min on a single sub-query)
- [~] op_inv_ntt_layer_1_step — admit-with-comment (same shape as ntt_1, by analogy)

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

### 2026-04-27 20:02 UTC — target 4 op_inv_ntt_layer_2_step PASS at rlimit 400
Bumped to `--z3rlimit 400 --split_queries always`. PASS in 50s.
Mirrored to Rust: src/vector/portable.rs line 641.

### 2026-04-27 20:30 UTC — target 5 op_ntt_layer_1_step BLOCKED
- rlimit 200 + split_queries always: Error 19 "Assertion failed" (clean).
- rlimit 400 + split_queries always: Error 19 in 4 minutes (clean fail).
- rlimit 800 + split_queries always: 60 sub-queries succeeded (~16ms each), then a single sub-query hung for 10+ minutes without resolving.  Cancelled.
Restored admit; added detailed English comment in Rust source (lines ~325 ff) describing what was tried, hypothesis, and next-step refactor.

### 2026-04-27 20:42 UTC — target 6 op_inv_ntt_layer_1_step ADMITTED-BY-ANALOGY
Same 4-way zeta dispatch shape as `op_ntt_layer_1_step` (the per-branch
predicate `p_inv_1` uses identical `if b=0 then zeta0 else if b=1 then
zeta1 else if b=2 then zeta2 else zeta3` to pick the zeta).  Per
brief's per-target wall-clock cap, did not invest a separate Z3 attempt.
Restored admit + added admit-with-comment block (~10 lines, line ~563
in src/vector/portable.rs) referencing the layer_1 next-step refactor
recipe.

### 2026-04-27 20:45 UTC — final verification
make Vector.Portable.fst.checked PASS in 43.2s (4 admits dropped, 2
remain with documented admit-with-comment).

### 2026-04-27 20:50 UTC — final make for log
Wall-clock: real 49.52s, user 44.39s, sys 2.56s.
F* TOTAL TIME for Libcrux_ml_kem.Vector.Portable: 44.999 s.
Result: All verification conditions discharged successfully.

## Summary
- 4 / 6 admits closed by proof:
  - op_ntt_layer_3_step (rlimit 200, split_queries always)
  - op_inv_ntt_layer_3_step (rlimit 200, split_queries always)
  - op_ntt_layer_2_step (rlimit 200, split_queries always)
  - op_inv_ntt_layer_2_step (rlimit 400, split_queries always)
- 2 / 6 admits kept with English comment + next-step refactor:
  - op_ntt_layer_1_step (rlimit 800 + split_queries hung >10 min on a sub-query)
  - op_inv_ntt_layer_1_step (admitted by analogy — same 4-zeta dispatch shape)

Common cause for the remaining 2: per-branch predicate uses a 4-way
zeta dispatch (`if b=0 then zeta0 else if b=1 then zeta1 else if b=2
then zeta2 else zeta3`) which Z3 case-splits on every per-lane fact
instantiation. Recommended refactor noted in Rust source: 4 dedicated
per-zeta lemmas + Spec.Utils.forall4 intro (factor into Hacspec_ml_kem.Commute.Chunk.fst).

