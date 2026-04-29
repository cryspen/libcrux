# Wave-B coordinator prompt — Phase 3 parallel lanes (A1, A2, A3, A5)

Wave-B's job: close the parallel-with-critical-path Phase 3 lanes —
Serialize migration (A1), Sampling (A2 + USER-10), Polynomial
(A3 = USER-7), Invert-NTT critical path (A5 = USER-6).  When done,
hand off to Wave-C for the consumer chain A6 → A7 → A8.

**Worktree:** `~/libcrux-ml-kem-above-trait/` (above-trait;
SETUP REQUIRED — see protocol below).
**Branch family:** `agent/lane-A<N>` per lane; merge to `trait-opacify`.

Paste the block below into a fresh Claude Code session opened in
`~/libcrux-ml-kem-above-trait/libcrux-ml-kem` (after worktree setup).

---

```
You are the Wave-B coordinator for the libcrux-ml-kem F* verification
sprint.  Phase 1 (trait pre/post) and Phase 2 (below-trait, all
B-lanes) are complete.  Wave-B spawns the parallel-with-critical-path
Phase 3 lanes; A5 is the critical path that gates Wave-C.

═══════════════════════════════════════════════════════════════════
SPRINT STATUS (at Wave-B start)
═══════════════════════════════════════════════════════════════════

✅ Phase 0, Phase H, Phase 1.
🔶 Phase 2 (Wave-A) — PARTIAL.  Final tip: `2f96abe99` (B6 closure)
   on top of `749b0136c` (concurrent serialize-prompt doc commit by
   the user).  Branch: `trait-opacify` (FF'd to B6).
   - **B6 LANDED (gates Wave-B).**  USER-1 / A8 4-case Barrett
     enumeration closed in `Hacspec_ml_kem.Commute.Chunk.fst` —
     `lemma_compress_ciphertext_coefficient_fe_commute` proven via
     2 f_val asserts + 4 pow2 witnesses at rlimit 400.  Verifies in
     86s cold (full Chunk.fst module).
   - **B1, B2, B3, B4, B5 DEFERRED.**  See "Wave-A deferral
     rationale" section in `agent-trackA.md` (2026-04-29 entry).
     Each lane has a tractable scope but exceeded the 1-session
     budget given hax-extract churn + body proof complexity.  The
     deferred admit cleanup is non-gating for Wave-B/C.
   - Net admit-count delta: -1 PROGRESS (Chunk.fst:985 admit removed),
     0 SIDEWAYS, 0 FAIR GAME, **-1 net**.

⏸ Phase 3 parallel — Wave-B's responsibility (this prompt).
⏸ Phase 3 critical chain — Wave-C (`wave-C-prompt.md`; recalibrated
   after Wave-B succeeds).

═══════════════════════════════════════════════════════════════════
WAVE-B WORKTREE SETUP (do this once before spawning lanes)
═══════════════════════════════════════════════════════════════════

  cd ~
  git clone /Users/karthik/libcrux-trait-opacify libcrux-ml-kem-above-trait
  cd libcrux-ml-kem-above-trait
  git fetch /Users/karthik/libcrux-trait-opacify trait-opacify:trait-opacify
  git checkout trait-opacify

  # Edit libcrux-ml-kem/proofs/fstar/extraction/Makefile to ADD
  # below-trait modules to ADMIT_MODULES (see "ADMIT MAP" below).

  # Verify clean: cd libcrux-ml-kem/proofs/fstar/extraction; make

═══════════════════════════════════════════════════════════════════
WAVE-B ADMIT MAP — local Makefile ADMIT_MODULES
═══════════════════════════════════════════════════════════════════

In addition to the existing ADMIT_MODULES, ADD:

  Libcrux_ml_kem.Vector.Portable.fst
  Libcrux_ml_kem.Vector.Portable.Arithmetic.fst
  Libcrux_ml_kem.Vector.Portable.Compress.fst
  Libcrux_ml_kem.Vector.Portable.Ntt.fst
  Libcrux_ml_kem.Vector.Portable.Sampling.fst
  Libcrux_ml_kem.Vector.Portable.Serialize.fst
  Libcrux_ml_kem.Vector.Portable.Vector_type.fst
  Libcrux_ml_kem.Vector.Avx2.fst
  Libcrux_ml_kem.Vector.Avx2.Arithmetic.fst
  Libcrux_ml_kem.Vector.Avx2.Compress.fst
  Libcrux_ml_kem.Vector.Avx2.Ntt.fst
  Libcrux_ml_kem.Vector.Avx2.Sampling.fst
  Libcrux_ml_kem.Vector.Avx2.Serialize.fst

ALSO ADD (Wave-C-owned modules):

  Libcrux_ml_kem.Matrix.fst
  Libcrux_ml_kem.Ind_cpa.fst        (already admitted)
  Libcrux_ml_kem.Ind_cca.Unpacked.fst (already admitted)
  Libcrux_ml_kem.Ind_cca.fst         (if not already)
  Libcrux_ml_kem.Mlkem*

REMOVE from ADMIT_MODULES (Wave-B unadmits):

  Libcrux_ml_kem.Polynomial.fst    (currently NOT admitted post-Phase-1; verify)
  Libcrux_ml_kem.Invert_ntt.fst    (currently NOT admitted; verify)

Trait files stay verified on both sides — Wave-B never edits them.

═══════════════════════════════════════════════════════════════════
WAVE-B SCOPE — Phase 3 parallel, 4 lanes
═══════════════════════════════════════════════════════════════════

  Lane | Files | Effort | Depends on | Critical path?
  -----|-------|--------|------------|---------------
  A1   | src/serialize.rs, Chunk.fst (Phase 7c migration; absorb USER-9 if AVX2 SIMD↔BitVec bridge fits) | 1-2 sess | B6 (done) | no
  A2   | src/sampling.rs (Phase 7n + USER-10 rej_sample wire-up) | 1 sess | none | no
  A3   | src/polynomial.rs, Chunk.fst (USER-7 + add_message_error_reduce + add_error_reduce) | 2 sess | Phase 1 trait (done) | no
  A5   | src/invert_ntt.rs, Bridges.fst, Chunk.fst (USER-6 invert_ntt_montgomery; Step 3.3 + Step 4 layer 4_plus + Step 5) | 3 sess | B6 (done) | YES (gates Wave-C)

OPPORTUNISTIC (Wave-B may attempt or defer to Wave-C):
  - A4 (Phase 7.2 std_error_reduce; A3 templates).  OK to leave admitted.

OUT OF SCOPE for Wave-B (Wave-C owns):
  - A6, A7, A8 (Matrix → Ind_cpa → Ind_cca consumer chain).

═══════════════════════════════════════════════════════════════════
RESUME PROTOCOL — read these in order
═══════════════════════════════════════════════════════════════════

  1. ~/.claude/plans/immutable-snacking-dewdrop.md (sprint plan)
  2. proofs/agent-status/lane-split-protocol.md (worktrees, SD1-3)
  3. proofs/agent-status/inter-wave-protocol.md (Wave-A/B/C handoff)
  4. proofs/agent-status/edit-check-loop-comparison.md
  5. MLKEM_STATUS.md (USER-1..USER-10; A5 is USER-6, A3 is USER-7)
  6. proofs/agent-status/agent-trackA.md (recent log; Wave-A entry)
  7. proofs/agent-status/wave-A-prompt.md "Deliverable" section
     (final SHA, admit-count baseline)

═══════════════════════════════════════════════════════════════════
COORDINATOR'S RESPONSIBILITY — overall proof status
═══════════════════════════════════════════════════════════════════

Same rubric as Wave-A (PROGRESS / SIDEWAYS / FAIR GAME).  At
Wave-B start, INHERIT Wave-A's final admit count as your baseline.
At Wave-B end, report delta.

A1, A3, A5 all touch `Hacspec_ml_kem.Commute.Chunk.fst`.  Each
appends to a clearly-marked `(* Phase 7X / lane A<N> additions *)`
section; never edits Wave-A's B6 additions.

═══════════════════════════════════════════════════════════════════
F*/Z3 TIME BUDGET — when to step back (carried over from Wave-A)
═══════════════════════════════════════════════════════════════════

20-minute cap per function/lemma.  Step-back audit: (a) is property
true, (b) is it needed, (c) is user better placed.  Default to (c)
at 20 min; admit + USER-N + move on.

A5 is the highest-risk lane (USER-6 invert_ntt_montgomery is a
3-session Z3-walled task).  Allocate the time budget per its
3-session estimate; but apply the 20-min-per-lemma cap aggressively
within the lane.

═══════════════════════════════════════════════════════════════════
HARD RULES
═══════════════════════════════════════════════════════════════════

R1 Spawn lane agents in their own branches `agent/lane-A<N>` off
   `trait-opacify` HEAD (= Wave-A final SHA).  All Wave-B lanes share
   the above-trait worktree (`~/libcrux-ml-kem-above-trait/`).
R2 Maintain SD1 / SD2 / SD3 per lane-split-protocol.md.
R3 No new admits in lane bodies — *unless* small scoped
   arithmetic/bitvec property to USER-N.  No broad `panic_free`.
R4 ulimit -v 8388608, F* rlimit ≤ 800.
R5 Inner loop: plain `make check/<Mod>.fst`.
R6 Lane budget: A1 / A2 = 1-2 sess; A3 = 2 sess; A5 = 3 sess.
   20-min cap per function/lemma.
R7 Don't bulk-delete `.checked` files.  `touch <file>.fst` to
   invalidate downstream.
R8 Use plain `make` (fstar-mcp unreliable).
R9 Trait FROZEN.  Don't touch `src/vector/traits.rs`.  Findings →
   `lane-split-protocol.md` "Open findings".
R10 Don't touch `src/vector/{portable,avx2}.*` or
    `src/vector/{portable,avx2}/...` — those are Wave-A's surface.
    If a lane finds a below-trait bug, file as a Wave-A regression
    in lane-split-protocol.md and back-port via PR to `trait-opacify`.

═══════════════════════════════════════════════════════════════════
COORDINATION CONVENTIONS (within Wave-B)
═══════════════════════════════════════════════════════════════════

`Hacspec_ml_kem.Commute.Chunk.fst` is touched by A1, A3, A5.  Each
lane appends to its own section; never edits another lane's
additions.  When two lanes both extend the file, merge serially
(A3 then A5; A1 independent).

`Hacspec_ml_kem.Commute.Bridges.fst` is touched by A5 only within
Wave-B.  No conflicts.

═══════════════════════════════════════════════════════════════════
WAVE-B MERGE ORDER back to `trait-opacify`
═══════════════════════════════════════════════════════════════════

  1. A2 (independent; Phase 7n + USER-10).  Quick win.
  2. A1 (Phase 7c serialize; depends on B6, file-disjoint from rest).
  3. A3 (USER-7; sequential after B6 to serialize Chunk merges).
  4. A5 (USER-6; sequential after A3; CRITICAL PATH for Wave-C).
  5. A4 (opportunistic; OK to leave admitted).

═══════════════════════════════════════════════════════════════════
SPAWNING LANES — recommended kickoff
═══════════════════════════════════════════════════════════════════

Highest priority (start first):
  - A5 (USER-6 invert_ntt_montgomery; longest critical path).

Parallel kickoff:
  - A2 (Phase 7n sampling; independent).
  - A1 (Phase 7c serialize migration).
  - A3 (USER-7 subtract_reduce body discharge).

After A5 lands: hand off to Wave-C.

═══════════════════════════════════════════════════════════════════
WAVE-B DELIVERABLE
═══════════════════════════════════════════════════════════════════

  • All Wave-B lane commits merged on `trait-opacify`.
  • Updated MLKEM_STATUS.md with A1/A2/A3/A5 outcomes.
  • Updated proofs/agent-status/agent-trackA.md with Wave-B session log.
  • Final admit-count report (vs Wave-A baseline).
  • Updated proofs/agent-status/wave-C-prompt.md with Wave-B's final
    commit SHA, any scope adjustments learned in flight, and any new
    findings about A6/A7/A8 (e.g., if A4 was attempted and what was
    learned about the Z3 cost of `add_standard_error_reduce`).

REPORT one paragraph end-of-wave summary.  Specifically note
whether Wave-C should expect any scope changes given what Wave-B
learned about A3's Chunk.fst additions and A5's Bridges.fst
additions (these are inputs to A6).
```
