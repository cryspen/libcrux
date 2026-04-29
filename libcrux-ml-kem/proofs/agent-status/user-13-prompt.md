# USER-13 single-lane prompt — close `inv_ntt_layer_2` body via SD3 opaque-wrapper unlock

**Worktree**: `~/libcrux-ml-kem-lane-A5/` already exists (preserved from
Wave-B; branch `agent/lane-A5`, tip `44646f0cd`).  Re-base onto current
`trait-opacify` HEAD (`3feaa8316`) at session start.

Alternative: fresh worktree off `trait-opacify` HEAD if the A5 worktree
state is uncomfortable to inherit.

Paste the block below into a fresh Claude Code session opened in
`~/libcrux-ml-kem-lane-A5/libcrux-ml-kem`.

---

```
You are a single-lane USER-13 agent for the libcrux-ml-kem F* verification sprint.  Your goal: close the `inv_ntt_layer_2` body proof in `Hacspec_ml_kem.Commute.Bridges.fst` (currently the 153 s top-1 perf culprit, with 1 failed query + 1 rlimit-saturated query at rlimit 200).  This is THE top of the critical path post-Wave-B.

═══════════════════════════════════════════════════════════════════
SPRINT STATE AT SESSION START
═══════════════════════════════════════════════════════════════════

Branch: trait-opacify, tip 3feaa8316 (handoff doc).
Last clean baseline: take-6 in ~/libcrux-ml-kem-above-trait/, FINAL_EXIT=0.
Lane worktree: `~/libcrux-ml-kem-lane-A5/` — branch agent/lane-A5 at 44646f0cd.

REBASE STEP (do this first):
  cd ~/libcrux-ml-kem-lane-A5
  git fetch /Users/karthik/libcrux-trait-opacify trait-opacify
  git checkout agent/lane-A5
  git rebase FETCH_HEAD
  # Conflicts may appear in MLKEM_STATUS.md / agent-trackA.md — keep
  # both sides, the lane's USER-13 entries are additive.

═══════════════════════════════════════════════════════════════════
SCOPE — THIS LANE ONLY
═══════════════════════════════════════════════════════════════════

The Wave-B A5 lane left `Libcrux_ml_kem.Invert_ntt.fst::invert_ntt_at_layer_2_` with `--admit_smt_queries true` (filed as USER-13).  The wall is on the loop-accumulator subtyping check (Q2/Q96 saturate rlimit 400 in 75-110 s; rlimit 800 + split_queries hung 12 min).

PER `proofs/agent-status/handoff-2026-04-29-end-of-day.md` USER-13 strategy (1):

> Per-chunk opaque predicate (SD3 pattern from lane-split-protocol.md) — same trick that closed FORWARD layer_2 in commit `b7b49c358`.  Wrap the loop invariant's per-chunk post in `[@@ "opaque_to_smt"]`.

THE PATTERN IS PROVEN.  Do NOT try to invent a new approach.

═══════════════════════════════════════════════════════════════════
CONCRETE FIX PATH — STEP-BY-STEP
═══════════════════════════════════════════════════════════════════

Step 1.  READ the proven-pattern reference: `git show b7b49c358 -- specs/ml-kem/proofs/fstar/commute/Hacspec_ml_kem.Commute.Bridges.fst`.  This is the FORWARD layer_2 unlock; copy its structure for the inverse direction.  Also read memory `feedback_layer2_branch_post_z3_unlock`.

Step 2.  Look at the current inverse layer_2 setup in `specs/ml-kem/proofs/fstar/commute/Hacspec_ml_kem.Commute.Bridges.fst` (around line 200-450).  The Wave-B regression (Snapshot 3) shows `lemma_inv_ntt_layer_2_step_lane_bridge` itself takes 146 s.  Note: the wall on `invert_ntt_at_layer_2_` body is DOWNSTREAM of this Bridges lemma — closing the lemma should NOT require Bridges changes if it already verifies (it does, the regression is just slow).

Step 3.  The actual block is in `src/invert_ntt.rs::invert_ntt_at_layer_2_`'s body.  Look at lines 140-235 region.  The loop invariant references the per-chunk strengthened post (`inv_ntt_layer_int_vec_step_reduce`'s output FE eqs).  Z3 saturates because each iteration re-derives the 16-lane FE algebra from scratch.

Step 4.  Apply SD3:
  (a) Define an opaque per-chunk predicate `inv_ntt_layer_2_chunk_post` in `Hacspec_ml_kem.Commute.Chunk.fst` (NEW section `(* USER-13 / lane SD3 additions *)`) wrapping `[@@ "opaque_to_smt"]`.  Body asserts the relevant FE-algebra fact for one chunk-pair.
  (b) Define an `assume`-or-`reveal_opaque`-ed reveal lemma so callers can unwrap it on demand.
  (c) Modify the loop invariant in `invert_ntt_at_layer_2_` to use this opaque predicate.  Z3 sees one atomic fact per processed chunk instead of unfolding 16-lane FE algebra.
  (d) Inside the body F* fragment, after invoking `inv_ntt_layer_int_vec_step_reduce`, invoke a 1-line lemma that produces the opaque per-chunk fact from the strengthened post (mirror `lemma_subtract_reduce_iter`'s shape from Wave-B A3).

Step 5.  After loop: invoke a per-vector composition lemma (NEW in `Bridges.fst` if not already there) that takes the 16 opaque per-chunk facts and produces the polynomial-level claim.  Use `Classical.forall_intro` over `j: usize{j < 16}`.

Step 6.  Remove `--admit_smt_queries true` from `invert_ntt_at_layer_2_`'s options.

═══════════════════════════════════════════════════════════════════
WORKFLOW
═══════════════════════════════════════════════════════════════════

1. `cd ~/libcrux-ml-kem-lane-A5/libcrux-ml-kem`
2. Read these in order (CONTEXT FIRST):
   - `proofs/agent-status/handoff-2026-04-29-end-of-day.md` (full sprint state)
   - `proofs/agent-status/lane-split-protocol.md` (SD1/2/3 rules)
   - `MLKEM_STATUS.md` USER-13 section
   - `proofs/agent-status/agent-trackA.md` 2026-04-28 evening "Phase 7a Step 2 layer 2 (the Z3 trap)" entry — this is the FORWARD layer_2 closure narrative; replicate the inverse direction.
   - `git show b7b49c358 -- specs/ml-kem/proofs/fstar/commute/Hacspec_ml_kem.Commute.Bridges.fst` — the proven pattern.
3. Locate the current admit:
   ```
   grep -n "admit_smt_queries" src/invert_ntt.rs
   ```
   Find the `invert_ntt_at_layer_2_` block; understand the loop structure.
4. Edit `Hacspec_ml_kem.Commute.Chunk.fst` first — add the opaque predicate + reveal lemma in a new `(* USER-13 / SD3 additions *)` section at end-of-file.
5. Build: `cd proofs/fstar/extraction; ulimit -v 8388608; rm -f /Users/karthik/libcrux-ml-kem-lane-A5/.fstar-cache/checked/Hacspec_ml_kem.Commute.Chunk.fst.checked; make check/Hacspec_ml_kem.Commute.Chunk.fst`
6. Edit `src/invert_ntt.rs` — modify the loop invariant + body F* fragment; remove `--admit_smt_queries true` from options.
7. Re-extract: `python3 hax.py extract`
8. Touch unchanged .checked (per `feedback_touch_unchanged_checked` memory):
   ```
   cd proofs/fstar/extraction
   find . -maxdepth 1 -name "Libcrux_ml_kem*.fst" -o -name "Libcrux_ml_kem*.fsti" | sort | xargs shasum > /tmp/USER13-pre.sha
   # ... extract ...
   find . -maxdepth 1 -name "Libcrux_ml_kem*.fst" -o -name "Libcrux_ml_kem*.fsti" | sort | xargs shasum > /tmp/USER13-post.sha
   diff /tmp/USER13-pre.sha /tmp/USER13-post.sha > /tmp/USER13-diff.sha
   for f in $(find . -maxdepth 1 -name "Libcrux_ml_kem*.fst" -o -name "Libcrux_ml_kem*.fsti"); do
     base=$(basename $f); chk=/Users/karthik/libcrux-ml-kem-lane-A5/.fstar-cache/checked/$base.checked
     if ! grep -qF "$base" /tmp/USER13-diff.sha && [ -f "$chk" ]; then touch "$chk"; fi
   done
   rm -f /Users/karthik/libcrux-ml-kem-lane-A5/.fstar-cache/checked/Libcrux_ml_kem.Invert_ntt.fst.checked
   ```
9. Inner loop: `make check/Libcrux_ml_kem.Invert_ntt.fst > /tmp/USER13-iter.log 2>&1; grep -E "^\* Error|All verification|Verified module" /tmp/USER13-iter.log`
10. Iterate on the opaque-predicate body and reveal-lemma until clean.  Cap: 20 min per attempt.
11. After Invert_ntt.fst clean: full make.  Confirm no regression elsewhere.

═══════════════════════════════════════════════════════════════════
HARD RULES
═══════════════════════════════════════════════════════════════════

R1 Branch `agent/lane-A5` (already on it post-rebase).  Do NOT merge to trait-opacify; the user does that.
R2 Trait FROZEN — DO NOT touch `src/vector/traits.rs`.
R3 No NEW broad admits.  The `[@@ "opaque_to_smt"]` predicate is OPACITY (intentional), not an admit; this is correct SD3.
R4 `ulimit -v 8388608`.  F* `--z3rlimit` ≤ 800.
R5 Inner loop: `make check/Libcrux_ml_kem.Invert_ntt.fst`.  Cross-module: `make check/Hacspec_ml_kem.Commute.Chunk.fst`, `make check/Hacspec_ml_kem.Commute.Bridges.fst`.
R6 20-min cap per attempt.  3 attempts → step back to user.  Total session budget: ~3 hr.
R7 Don't bulk-delete `.checked`.
R8 No `fstar-mcp` (per `feedback_use_fstar_mcp` and `feedback_fstar_mcp_session_dies_after_make`).
R9 Chunk.fst additions go in NEW `(* USER-13 / SD3 additions *)` section AT END-OF-FILE.  Don't edit existing sections.
R10 The Wave-B local Makefile is in working tree of `~/libcrux-ml-kem-above-trait/` (uncommitted); your worktree's Makefile is upstream-clean.  Don't add Wave-B local admits to your worktree's Makefile.

═══════════════════════════════════════════════════════════════════
PRIOR DIAGNOSTICS (carry-over from Wave-B / Wave-A)
═══════════════════════════════════════════════════════════════════

Forward layer_2 unlock (commit `b7b49c358`, 2026-04-28):
  - 4 per-branch lemmas at concrete `b ∈ {0..3}` (NOT symbolic-b).
  - Per-lane wrapper dispatching to the right per-branch.
  - Per-vector composition under `--split_queries always`.
  - 16 sub-queries, each <100 ms.  Total cold rebuild 188 s.

A5 (Wave-B) layer_2 attempt 2026-04-29:
  - rlimit 800 + `--split_queries always` → hung past 12 min.
  - rlimit 400 → Q2/Q96 cancel at 75-110 s.
  - REVERTED to admit_smt_queries true.
  - Diagnosis: same shape as forward layer_2 wall.  SD3 NOT YET TRIED on inverse direction.

This lane: APPLY THE PROVEN SD3 PATTERN.  Do NOT try rlimit bumps or split_queries alone — those are confirmed to fail.

═══════════════════════════════════════════════════════════════════
DELIVERABLE
═══════════════════════════════════════════════════════════════════

Commit prefix: `agent-user13:` — separate commits for:
  (1) `agent-user13: Chunk.fst — SD3 opaque per-chunk predicate + reveal lemma`
  (2) `agent-user13: Invert_ntt.rs — loop invariant uses opaque predicate; remove admit`

Report ONE paragraph:
  - Closure status: ✅ admit_smt_queries removed and proof closes / ⏸ deferred (with what specifically blocked).
  - Layer_2 lemma `lemma_inv_ntt_layer_2_step_lane_bridge` total wall (was 146 s in Snapshot 3).
  - Invert_ntt.fst Query-stats summary before/after.
  - Any new lemmas added (cite section name + lemma names).
  - Final commit SHA on agent/lane-A5.
  - Update `proofs/agent-status/fstar-perf-top20.md` with Snapshot 4.

DO NOT push to trait-opacify.  DO NOT touch other lane worktrees.  DO NOT touch matrix.rs / ind_cpa.rs / ind_cca.rs (Wave-C surface).

═══════════════════════════════════════════════════════════════════
IF SD3 STILL WALLS (escape hatch)
═══════════════════════════════════════════════════════════════════

If after 2-3 SD3 iterations the Invert_ntt.fst still fails to close:

(a) Try `--smtencoding.elim_box true --smtencoding.l_arith_repr native` on the function — sometimes breaks quantifier instantiation walls.
(b) Decompose the loop invariant into a pre-loop-only assertion + a post-loop-only assertion.  Z3 then doesn't have to maintain the invariant across iterations.
(c) Step back: file as USER-13 with the per-attempt diagnostic + concrete next strategy; the user can drive with `smtprofiling`.
```
