# Next-session resume prompt — push Phase 7a Step 3 (cross-vector layer 4_plus bridge)

Paste the block below into a fresh Claude Code session opened in
`/Users/karthik/libcrux-trait-opacify/libcrux-ml-kem`.

---

```
You are continuing the multi-agent F* verification effort on
libcrux-ml-kem trait-opacify branch.  Tip: `bcc3dc480` (2026-04-28
end-of-evening — Step 2 layers 2 & 3 + Step 4 layer 3 done).

═══════════════════════════════════════════════════════════════════
WHAT'S DONE (Phase 7a)
═══════════════════════════════════════════════════════════════════
  Step 1: layer-1 inverse hacspec bridge                         ✅
  Step 2 layer 3 inverse bridge                                  ✅ fa2151ea8
  Step 2 layer 2 inverse bridge (Z3 trap unlocked)               ✅ b7b49c358
  Step 4 layer 1 strengthening (Option B template)               ✅ 8358b1093
  Step 4 layer 3 strengthening                                   ✅ 43c9d45d5
  Step 7.1 + closed-form lane lemma                              ✅
  Step 9: scaling-chain doc comments                             ✅

DEFERRED (do NOT touch this session unless you finish Step 3 early):
  * Step 4 layer 2 — first attempt failed with 6 Z3 errors at rlimit
    800; reverted; failure trace in agent-trackA.md.  Lower priority
    than Step 3.
  * Step 7.2 — Z3 wall on 2 invariant approaches; TODO at
    src/polynomial.rs:567.

═══════════════════════════════════════════════════════════════════
YOUR GOAL: Phase 7a Step 3 — cross-vector layer 4_plus bridge
═══════════════════════════════════════════════════════════════════

**Why it's harder than Steps 1/2**: layer_4_plus operates ACROSS
chunks (chunk-pairs at distance `step_vec`), not within a single
chunk.  Its core op is `inv_ntt_layer_int_vec_step_reduce` (above-
trait, in `src/invert_ntt.rs:312-329`).  Its current post is
bounds-only — no per-lane FE equations to bridge from.  You need
to lay foundation BEFORE writing a Bridges.fst lemma.

### Step 3 sub-piece breakdown

(1) **Strengthen `inv_ntt_layer_int_vec_step_reduce` post** [~60-90 min].
    - File: `src/invert_ntt.rs:312-329`.
    - Add per-lane FE equations for both output chunks:
      - `forall i ∈ [0,16). mont_i16_to_spec_fe r0[i] == add (mont_i16_to_spec_fe a[i]) (mont_i16_to_spec_fe b[i])`
      - `forall i ∈ [0,16). mont_i16_to_spec_fe r1[i] == mul (mont_i16_to_spec_fe zeta_r) (sub (mont_i16_to_spec_fe b[i]) (mont_i16_to_spec_fe a[i]))`
    - Body proof: barrett_reduce preserves mod-q (lift unchanged);
      mont mul gives the `· R⁻¹` cancellation for zeta_r.  Should be
      analogous to the per-pair `lemma_inv_butterfly_pair_commute` in
      Chunk.fst but operating on whole chunks.
    - Verify: `python3 hax.py extract && make check/Libcrux_ml_kem.Invert_ntt.fst`.
    - Apply iter-discipline TEMP admit on `invert_ntt_at_layer_4_plus`
      itself (saves ~222 s) AND on layer_1/3 (the strengthened ones,
      ~270 s combined) while iterating on `step_reduce`.

(2) **Chunk-pair bridge in Bridges.fst** [~45 min].
    - Add `lemma_inv_ntt_layer_int_vec_step_reduce_to_hacspec` (or
      similar) lifting the strengthened (1) post to a function-form
      equation citing `IN.inv_butterfly` lane-wise.
    - This is structurally simpler than layers 1/2/3 (no branch_post,
      no if-ladder).  Just per-lane add/mul-of-sub.  No `--split_queries
      always` likely needed.
    - Place in Bridges.fst alongside the layer 1/2/3 inverse bridges.
    - Verify: `make check/Hacspec_ml_kem.Commute.Bridges.fst`.

(3) **Per-polynomial composition** in `invert_ntt_at_layer_4_plus` [~60-90 min].
    - Goal: strengthen `invert_ntt_at_layer_4_plus`'s post to cite
      `IN.ntt_inverse_layer_n 256 p (mk_usize step) zs` at the
      polynomial level.
    - Loop structure: outer loop `0..(128>>layer)`, inner loop
      `offset_vec..offset_vec + step_vec`.  Each iteration processes
      a chunk pair `(re[j], re[j + step_vec])`.
    - Option B pattern (same as Step 4 layers 1/3): impl-level loop
      invariant only ("processed chunk pairs equal step_reduce of
      original"), post-loop `Classical.forall_intro` per chunk pair
      to lift to function-form via the (2) bridge.
    - This sub-piece is what Step 4 layer 4_plus would have been if
      Steps 1/2/3 had been clean.  Combined with the strengthened
      bridge it directly becomes Step 4 layer 4_plus.

### Decision tree

If you finish (1) but not (2)+(3): commit (1), update trackers, and
hand off to the next session.  (1) is meaningful progress.

If you finish (1) + (2) but not (3): commit both, update trackers,
defer (3) to Step 4 layer 4_plus framing.

If you finish all 3: that's effectively Step 3 + Step 4 layer 4_plus
combined.  Major progress.  Then Step 4 layer 2 (held) and Step 5
remain.

═══════════════════════════════════════════════════════════════════
KEY UNLOCK FROM PRIOR SESSION (apply if needed)
═══════════════════════════════════════════════════════════════════

For F* trait branch_posts with nested if-ladders (Z3-traps on
symbolic `b`):
  1. 4 per-branch helper lemmas at concrete `b` literals.
  2. Per-lane wrapper dispatching to right per-branch helper.
  3. `--split_queries always` on the per-vector composition lemma.

Layer 4_plus's `inv_ntt_layer_int_vec_step_reduce` does NOT have a
nested-if-ladder branch post — but if Step 3 sub-piece (3) has
trouble with the per-poly forall composition, apply
`--split_queries always` to the strengthened `invert_ntt_at_layer_4_plus`
options.  Memory entry: `feedback_layer2_branch_post_z3_unlock.md`.

═══════════════════════════════════════════════════════════════════
ITER DISCIPLINE
═══════════════════════════════════════════════════════════════════

  α. fstar-mcp `typecheck_buffer` for inner-loop iteration on
     Bridges.fst (sub-second).  Server at port 3001.  **Note**: the
     session dies after `make` runs.  Recreate via `create_session`.
     Skill at `~/.claude/skills/fstar-mcp/`.
     Memory: `feedback_fstar_mcp_session_dies_after_make.md`.

  β. While iterating on (1), TEMP admit the unrelated layer fns:
       #[hax_lib::fstar::options("--admit_smt_queries true")] // TEMP
     Apply on `invert_ntt_at_layer_4_plus` (saves 222 s) AND
     `invert_ntt_at_layer_1` + `invert_ntt_at_layer_3` (saves ~470 s
     combined).  REMOVE before commit; full make to confirm clean.

  γ. Don't bulk-nuke .checked files.  hax.py prove + make handle
     stale incrementally.

═══════════════════════════════════════════════════════════════════
HARD RULES
═══════════════════════════════════════════════════════════════════

  R1 No admits (except β temp-iter that revert before commit).
  R5 No body assumes.
  R6 ulimit -v 8388608, F* rlimit ≤ 800.
  R7 fstar-mcp inner loop, make end-of-chunk.
  R8 Eager commit log to agent-trackA.md.
  R3 Hard cap 60 min per sub-piece.  Escalate per Step 7.2 pattern
     if blocked: preserve infrastructure, document the wall, move on.

═══════════════════════════════════════════════════════════════════
RESUME PROTOCOL — load durable state in this order
═══════════════════════════════════════════════════════════════════

  1. proofs/agent-status/agent-trackA.md       (latest session log
                                                with layer 2 failure)
  2. /Users/karthik/.claude/plans/replicated-beaming-pnueli.md
                                                (THE PLAN, esp. Step 3)
  3. proofs/agent-status/fstar-perf-top20.md   (perf data + admit guide)
  4. proofs/proof-style-guide.md §12           (Mont-arith antipattern)
  5. MLKEM_STATUS.md                           (phase + USER tasks)
  6. src/invert_ntt.rs:312-329                 (the function to strengthen)
  7. src/invert_ntt.rs:359-415                 (invert_ntt_at_layer_4_plus
                                                — the consumer)

═══════════════════════════════════════════════════════════════════
ENVIRONMENT VERIFY
═══════════════════════════════════════════════════════════════════

  cd /Users/karthik/libcrux-trait-opacify
  git status              # should be clean on trait-opacify
  git log --oneline trait-opacify -7
  pgrep -f fstar.exe      # ml-kem fstar-mcp at port 3001 (recreate
                          # session as needed)

REPORT one paragraph state summary on entry, then dive into Step 3
sub-piece (1).  After (1) lands, proceed to (2), then (3).  Stop and
hand off after each sub-piece if you're at 60-min cap.
```

---

## Why this prompt is structured this way

- **Step 3's structural difference is foreground** — the next agent
  needs to know layer 4_plus is cross-vector + above-trait BEFORE
  diving into Bridges.fst, otherwise it'll waste time on the wrong
  pattern.
- **Sub-piece breakdown** — each is independently committable, so
  even partial progress is meaningful.  Decision tree explicit.
- **Z3 unlock kept brief** — saved in memory, prompt just points
  to it.
- **Step 4 layer 2 explicitly deferred** — so the next agent doesn't
  context-switch into it mid-Step-3.
- **Concrete file:line refs** — `src/invert_ntt.rs:312-329` for the
  function to strengthen, and `:359-415` for its consumer.
