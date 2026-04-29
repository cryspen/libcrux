# Wave-A coordinator prompt — Phase 2 (below-trait closure, 6 lanes)

Wave-A's job: close the below-trait surface — `Vector.Portable.*`,
`Vector.Avx2.*`, plus the 4-case Barrett enumeration in
`Hacspec_ml_kem.Commute.Chunk.fst` (B6 / USER-1).  When done, hand off
to Wave-B (Phase 3 parallel lanes).

**Worktree:** `/Users/karthik/libcrux-trait-opacify/` (below-trait;
this worktree).
**Branch family:** `agent/lane-B<N>` per lane; merge to `trait-opacify`.

Paste the block below into a fresh Claude Code session opened in
`/Users/karthik/libcrux-trait-opacify/libcrux-ml-kem`.

---

```
You are the Wave-A coordinator for the libcrux-ml-kem F* verification
sprint.  Phase 1 (trait pre/post fixes) is complete; trait contract is
FROZEN.  Wave-A spawns Phase 2 (below-trait) lanes.  When you're done,
you hand off to Wave-B for Phase 3 parallel lanes (A1/A2/A3/A5),
which will cherry-pick Wave-A's trait/Vector commits into a separate
above-trait worktree.

═══════════════════════════════════════════════════════════════════
SPRINT STATUS (at Wave-A start)
═══════════════════════════════════════════════════════════════════

✅ Phase 0, Phase H, Phase 1.
   - Trait contract is FROZEN at `trait-opacify` HEAD post-Phase-1.
   - Phase 1 commits: `05967b8fe`, `a51ddbfc3`, `bf571e575`, `047da6de8`.

⏸ Phase 2 — Wave-A's responsibility (this prompt).
⏸ Phase 3 parallel — Wave-B (`wave-B-prompt.md`).
⏸ Phase 3 critical chain — Wave-C (`wave-C-prompt.md`; recalibrated
   after Wave-A + Wave-B succeed).

═══════════════════════════════════════════════════════════════════
WAVE-A SCOPE — Phase 2 below-trait, 6 lanes
═══════════════════════════════════════════════════════════════════

  Lane | Files | Effort | Risk | Sequential constraint
  -----|-------|--------|------|---------------------
  B1   | src/vector/portable.rs (drop stale compress/decompress panic_free) | 1 sess | low | parallel
  B2   | src/vector/portable.rs, portable/ntt.rs (NTT layer 1) | 2 sess | med (Z3) | parallel
  B3   | src/vector/avx2.rs, libcrux-intrinsics/...Avx2_extract.fst | 2 sess | low-med | parallel
  B4   | src/vector/avx2.rs, vector/avx2/ntt.rs, Bridges.fst | 1 sess spike | high | serial after B6 if Bridges touched
  B5   | src/vector/{portable,avx2}.rs (drop ntt_multiply panic_free) | 1 sess | low | parallel
  B6   | Hacspec_ml_kem.Commute.Chunk.fst (USER-1 A8 4-case Barrett) | 1-2 sess | med | LAND FIRST; gates Wave-B (A1/A3/A5)

  B7 DESCOPED — keep AVX2 SIMD lane lemmas as admit boundary.

  Sequential within Wave-A: B6 first (gates Wave-B).
  Parallel: B1 ‖ B5 ‖ B3 ‖ B2 (file-disjoint).
  B4 high-risk; spike then defer if blocked.

OUT OF SCOPE for Wave-A (Wave-B/C own):
  - All A-lanes (above-trait modules).
  - USER-8, USER-9, USER-10 trait wire-ups (deferred from Phase 1).

═══════════════════════════════════════════════════════════════════
RESUME PROTOCOL — read these in order
═══════════════════════════════════════════════════════════════════

  1. ~/.claude/plans/immutable-snacking-dewdrop.md (sprint plan)
  2. proofs/agent-status/lane-split-protocol.md (worktrees, SD1-3)
  3. proofs/agent-status/inter-wave-protocol.md (Wave-A/B/C handoff)
  4. proofs/agent-status/edit-check-loop-comparison.md
  5. MLKEM_STATUS.md (USER-1..USER-10 task list)
  6. proofs/agent-status/agent-trackA.md (recent log)

═══════════════════════════════════════════════════════════════════
COORDINATOR'S RESPONSIBILITY — overall proof status
═══════════════════════════════════════════════════════════════════

Track OVERALL admit count, not just per-lane "did the lane compile":

  • PROGRESS: an existing admit (`--admit_smt_queries true`,
    `panic_free`, `lax`, or `admit ()`) was REMOVED and the proof
    closes for real.  Net admit count goes DOWN.
  • SIDEWAYS: an admit was moved to a NEW admitted lemma.  Sometimes
    right (factoring) — but notice it isn't progress.
  • FAIR GAME: a NEW admit scoped to a small (≤10 line)
    arithmetic/bitvec property.  File USER-N; do not block lane.

After every lane merge: re-run `make` from `proofs/fstar/extraction/`,
grep admits, track running count.  Flag if rising.

At Wave-A start, baseline the admit count.  At Wave-A end, report:
  - admits removed (PROGRESS)
  - admits relocated (SIDEWAYS)
  - admits added to USER-N (FAIR GAME)
  - net delta
This is your handoff metric for Wave-B.

═══════════════════════════════════════════════════════════════════
F*/Z3 TIME BUDGET — when to step back
═══════════════════════════════════════════════════════════════════

If a single function/lemma is not closing after **20 minutes** of
strategy iteration, STOP and audit:

  (a) Is the property actually true?  Counter-example check.
  (b) Is the property truly needed?  Often the post is stronger
      than the consumer requires.
  (c) Is the user better placed to close it?  Calc proofs, bit-vec
      bashes, 4-case Barrett enumerations are often faster for a
      human with smtprofiling than for an agent burning rlimit.

Default to (c) at 20 min.  Sunk-cost on Z3 walls is the largest
source of session slip.

═══════════════════════════════════════════════════════════════════
HARD RULES
═══════════════════════════════════════════════════════════════════

R1 Spawn lane agents in their own branches `agent/lane-B<N>` off
   `trait-opacify`.  All Wave-A lanes share the below-trait worktree
   (`/Users/karthik/libcrux-trait-opacify/`).
R2 Maintain SD1 (mod-q opacity), SD2 (forall<N>), SD3 (opaque
   per-branch wrappers) per lane-split-protocol.md.
R3 No new admits in lane bodies — *unless* the admit is a small,
   well-scoped arithmetic/bitvec property handed off to USER-N
   (per coordinator rubric).  No broad `panic_free` band-aids.
R4 ulimit -v 8388608, F* rlimit ≤ 800.
R5 Inner loop: plain `make check/<Mod>.fst` from
   `proofs/fstar/extraction/`.
R6 Lane budget: 1 sess for B1/B4/B5/B6 / 2 sess for B2/B3.  Within
   a lane, hard cap 20 min per function/lemma before triggering the
   step-back audit.
R7 Don't bulk-delete `.checked` files — `make` handles staleness.
   Surgical `rm` only the target's `.checked` when iterating; prefer
   `touch <file>.fst`.
R8 fstar-mcp is unreliable on this branch (per Phase 0 study); use
   plain `make` for the inner loop.
R9 Trait is FROZEN.  Don't touch `src/vector/traits.rs`.  If a lane
   discovers a trait gap, file under "Open findings" in
   lane-split-protocol.md — don't fix.
R10 Wave-A's local Makefile keeps above-trait modules
    (Polynomial, Ntt, Invert_ntt, Matrix, Serialize, Sampling,
    Compress, Ind_cpa*, Ind_cca*, Mlkem*) in ADMIT_MODULES — they
    already are; do not remove during Wave-A.  Wave-B/C will
    unadmit them in their above-trait worktree.

═══════════════════════════════════════════════════════════════════
COORDINATION CONVENTIONS (within Wave-A)
═══════════════════════════════════════════════════════════════════

`Hacspec_ml_kem.Commute.Chunk.fst` is touched by B6 only within
Wave-A.  B6 appends to a clearly-marked
`(* Phase 2 / B6 additions *)` section; never edits existing lemma
bodies.  Wave-B/C will add their own appends later.

`Hacspec_ml_kem.Commute.Bridges.fst` is touched by B4 only within
Wave-A (and only if B4's spike doesn't descope).

═══════════════════════════════════════════════════════════════════
WAVE-A MERGE ORDER back to `trait-opacify`
═══════════════════════════════════════════════════════════════════

  1. B1, B5 (low-risk file-disjoint) — clear backlog, build admit-
     count momentum.
  2. B6 (Chunk.fst foundation) — gates Wave-B.
  3. B3, B2 (medium effort, can fan out).
  4. B4 (opportunistic spike; descope on first wall).

═══════════════════════════════════════════════════════════════════
SPAWNING LANES — recommended kickoff
═══════════════════════════════════════════════════════════════════

Highest priority (start first, parallelizable):
  - B1 (drop stale panic_free in src/vector/portable.rs).
  - B5 (drop ntt_multiply panic_free, both backends).
  - B6 (USER-1 / A8 4-case Barrett enumeration).

Parallel kickoff (alongside above):
  - B3 (AVX2 serialize bridges).

After B6 lands: start B2 (Portable NTT layer 1; benefits from B6's
Chunk.fst additions).

Spike (1 session, descope if blocked):
  - B4 (AVX2 NTT layer 1/2; Z3-walled per USER-4).

═══════════════════════════════════════════════════════════════════
WAVE-A DELIVERABLE
═══════════════════════════════════════════════════════════════════

  • All Wave-A lane commits merged on `trait-opacify`.
  • Updated MLKEM_STATUS.md with B-lane outcomes.
  • Updated proofs/agent-status/agent-trackA.md with Wave-A session log.
  • Final admit-count report (PROGRESS / SIDEWAYS / FAIR GAME / net).
  • Updated proofs/agent-status/wave-B-prompt.md with Wave-A's final
    commit SHA + any new findings or scope changes.

REPORT one paragraph end-of-wave summary.
```
