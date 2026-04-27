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

## Phase 6 follow-up (agent A2) — 2026-04-27

Continuation brief: close the 2 remaining layer-1 admits by factoring 4
per-branch lemmas into `Hacspec_ml_kem.Commute.Chunk.fst`.

### plan
- Add 4 lemmas `lemma_ntt_layer_1_branch_{0,1,2,3}` to Commute.Chunk.fst.
  Each takes `(vec result: t_Array i16 16)` + 4 zetas + `Lemma (requires
  <2 ntt_spec residues for that branch>) (ensures
  ntt_layer_1_step_branch_post n vec zeta0 zeta1 zeta2 zeta3 result)`.
  Body: `reveal_opaque ntt_layer_1_step_branch_post` then 2 calls to
  `lemma_butterfly_pair_commute`.  With `n` literal, the per-branch
  if-ladder collapses to the right zeta on both pre and post sides.
- Same for `lemma_inv_ntt_layer_1_branch_{0,1,2,3}` using
  `lemma_inv_butterfly_pair_commute` and `inv_ntt_layer_1_step_branch_post`.
- At the wrappers in src/vector/portable.rs: drop the 4 `assert (p_layer_1 b)`
  steps; instead call the 4 new branch lemmas.  Final `forall4 p_layer_1`
  follows from the 4 branch posts directly.

### outcome (2026-04-27 22:45 UTC)

**Result: 0 of 2 newly proven.  Both targets keep admit-with-comment.**

Two helper lemmas successfully landed in
`specs/ml-kem/proofs/fstar/commute/Hacspec_ml_kem.Commute.Chunk.fst`:
- `lemma_ntt_layer_1_butterfly_to_fe` (vec, result, z, i1, j1, i2, j2)
  — packages 2 `lemma_butterfly_pair_commute` calls and yields the 4
  FE equalities for one zeta-pair group.  Verified ~25 ms.
- `lemma_inv_ntt_layer_1_butterfly_to_fe` — mirror for the inverse
  direction.  Verified ~25 ms.

Per-branch lemmas (`lemma_ntt_layer_1_branch_{0..3}` and inv mirror)
**failed to verify** even with `b` literal.  Symptoms:
- rlimit 200 + `--split_queries always`: 16 sub-queries succeed in
  ~7-130 ms each, then a single sub-query (#17 onward) hangs > 60 s.
- rlimit 400 without split_queries: full timeout, no progress.
- rlimit 200 with `--fuel 0 --ifuel 0`: branch lemma never returned a
  query (Z3 stuck in pre-solve simplification).

Diagnosis: revealing `ntt_layer_1_step_branch_post` exposes the
`let z = if b = 0 then zeta0 else if b = 1 then zeta1 ...` ladder
inside the post body.  Even when the outer `b` is a literal `0`, Z3
case-splits on the if-ladder during instantiation of the
`mont_i16_to_spec_fe` post equations — the same blowup that the layer-1
admits suffered originally.  The literal `b = 0` does not trigger
F*-side normalization of the if-ladder before SMT.

The `ntt_layer_1_butterfly_to_fe` helpers (which DO verify) bridge from
`ntt_spec` residues to FE-form equations for one zeta-pair group, so
they remain useful for the next-step refactor.

Restoration: per-branch lemma definitions removed from Commute.Chunk;
both wrappers in `src/vector/portable.rs` retain
`#[hax_lib::fstar::options("--admit_smt_queries true")]` (unchanged
from agent A's tip 65668af62).  Helper lemmas + a documentation comment
explaining the failure mode were committed as a partial gain.

### Recommended next-step (USER)

Two viable refactor paths, roughly equal effort:

(a) **Reshape `ntt_layer_1_step_branch_post`** in
   `libcrux-ml-kem/src/vector/traits.rs::spec` so the zeta is selected
   *outside* the opaque body and passed in as an `i16` argument:
   ```fstar
   let ntt_layer_1_step_branch_post
       (b: nat{b < 4}) (z: i16)             // z chosen by caller
       (input: t_Array i16 16) (result: t_Array i16 16) : prop = ...
   ```
   The 4-way zeta dispatch then lives at the *call site* (which in F*
   is post-`forall4`-binding, not inside the opaque body), and Z3's
   per-branch reasoning never sees the if-ladder.  This change is
   additive at the post level (one extra arg) and ripples through
   the post construction `ntt_layer_1_step_post` (which assembles the
   `forall4`).  The brief explicitly forbade redesigning per-branch
   predicates *for this agent*, but a USER pass can do it.

(b) **Tactic-based normalization at the wrappers**.  Replace each
   `assert (p_layer_1 b)` with
   `assert (p_layer_1 b) by (FStar.Tactics.norm [iota; primops; delta])`
   to fully reduce the if-ladder before passing to SMT.  Lower
   architectural change but adds tactic-language dependency at the
   wrappers.

Both approaches preserve the helper lemmas above; the helpers'
refactor recipe (move ladder out of opaque body / norm before SMT)
applies symmetrically to inv direction.

### Commits on agent/phase-6-portable-ntt
- 3e4bc21ea: `agent-A2: layer-1 helper FE-bridge lemmas + analysis comment`

### Final regression (post-A2)
- `make run/Libcrux_ml_kem.Vector.Portable.fst` PASS.
- Wall: 1:28.32 (user 83.66 s).  TOTAL TIME 83260 ms.
- 4 layer-2/3 admits remain dropped (no regression).
- 2 layer-1 admits retained with admit-with-comment.

