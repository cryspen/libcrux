# Next-session resume prompt — Post-Phase-1, ready to fan out Phase 2 + Phase 3

Phase 1 (trait pre/post fixes) is now substantially complete on
`trait-opacify`:

- Cluster 1 (output bounds + docs on add/sub/mul/negate posts) — ✅
  `05967b8fe`.
- Cluster 2 (from_bytes / to_bytes) — ⏸ deferred → USER-8.
- Cluster 3 (serialize_5/11, deserialize_5/11) — 🔶 PARTIAL: 4 portable
  BitVec lemmas landed at `a51ddbfc3`; trait wiring deferred → USER-9
  (gated on AVX2 SIMD↔BitVec bridge).
- Cluster 4 (rej_sample) — ⏸ deferred → USER-10.

The end-to-end sprint plan is at
`~/.claude/plans/immutable-snacking-dewdrop.md`.

The trait contract is now stable enough to fan out Phase 2 (below-trait
closure) and Phase 3 (above-trait closure) to parallel agents.

Paste the block below into a fresh Claude Code session opened in
`/Users/karthik/libcrux-trait-opacify/libcrux-ml-kem`.

---

```
You are picking up the libcrux-ml-kem F* verification sprint after
Phase 1 landed.  The trait contract on `trait-opacify` is FROZEN; you
are spawning Phase 2 (below-trait) and/or Phase 3 (above-trait) lanes.

═══════════════════════════════════════════════════════════════════
SPRINT STATUS
═══════════════════════════════════════════════════════════════════

✅ Phase 0 — canonical edit-check loop study; verdict
   `make check/<Mod>.fst` from `proofs/fstar/extraction/`.
✅ Phase H (2026-04-29) — opaque mod_q at trait boundary; commit
   `08dedde99`.  `Hacspec_ml_kem.ModQ.fst` defines `mod_q_eq`; trait
   posts use `mod_q_eq` form.
✅ Phase 1 (2026-04-29) — trait pre/post fixes, 2 of 4 clusters
   landed:
   - Cluster 1 (commit `05967b8fe`): output bounds + docs on
     add/sub/mul/negate.  Bundled forall pattern; impl wrapper
     alignment for multiply_by_constant.
   - Cluster 3 partial (commit `a51ddbfc3`): 4 portable BitVec lemmas
     for serialize_5/11 + deserialize_5/11.  Trait wiring deferred.

⏸ USER-8 — Cluster 2 deferred (from_bytes / to_bytes BitVec bridge,
   needs portable bit-shift→BitVec lemma + AVX2 intrinsic→BitVec
   bridge; ~90 min total).
⏸ USER-9 — Cluster 3 trait wiring deferred (gated on AVX2
   SIMD→BitVec bridge for serialize_5/11/deserialize_5/11).
⏸ USER-10 — Cluster 4 deferred (rej_sample post, combine with A2
   Phase 7n).

═══════════════════════════════════════════════════════════════════
ENVIRONMENT VERIFY (do this first)
═══════════════════════════════════════════════════════════════════

  cd /Users/karthik/libcrux-trait-opacify
  git log --oneline trait-opacify -6
  # Should show:
  #   a51ddbfc3 agent-trackA: Phase 1 Cluster 3 (partial) — portable serialize_5/11 + deserialize_5/11 BitVec lemmas
  #   05967b8fe agent-trackA: Phase 1 Cluster 1 — output bounds + docs on add/sub/mul/negate posts
  #   13d603c01 agent-trackA: handoff prompt — add Phase 2 + 3 parallel/sequential breakdown
  #   d0929f8a5 agent-trackA: handoff prompt for Phase 1 (post-Phase-H)
  #   08dedde99 agent-trackA: Phase H — opaque mod_q at trait boundary + lane-split protocol

═══════════════════════════════════════════════════════════════════
RESUME PROTOCOL — read these in order
═══════════════════════════════════════════════════════════════════

  1. ~/.claude/plans/immutable-snacking-dewdrop.md
     (consolidated sprint plan; Phase 2/3 details in §"Phase 2/3")
  2. proofs/agent-status/lane-split-protocol.md
     (worktree split, cherry-pick discipline, style rules SD1-SD3)
  3. proofs/agent-status/edit-check-loop-comparison.md
     (canonical inner loop verdict)
  4. MLKEM_STATUS.md
     (USER-1..USER-10 task list; USER-7 is the next user-track work,
      USER-8/9/10 are Phase-1-deferred items)
  5. proofs/agent-status/agent-trackA.md
     (recent-session log; 2026-04-29 entry covers Phase 1)

═══════════════════════════════════════════════════════════════════
PHASE 2 SCOPE — below-trait closure (7 lanes, parallel)
═══════════════════════════════════════════════════════════════════

  Each lane works on its own worktree off `trait-opacify` HEAD post-
  Phase-1 (`a51ddbfc3`).  Per-lane Makefile admits all OTHER lanes'
  modules — see lane-split-protocol.md.  Lanes touching
  `Commute.Chunk.fst` must serialize through B6 (sequential); the rest
  are file-disjoint.

  Lane | Files | Effort | Risk | Sequential constraint
  -----|-------|--------|------|---------------------
  B1   | src/vector/portable.rs (compress/decompress stale)  | 1 sess | low  | parallel (file-disjoint)
  B2   | src/vector/portable.rs, portable/ntt.rs (NTT layer 1) | 2 sess | med (Z3) | parallel (file-disjoint)
  B3   | src/vector/avx2.rs, libcrux-intrinsics/...Avx2_extract.fst | 2 sess | low-med | parallel (file-disjoint)
  B4   | src/vector/avx2.rs, vector/avx2/ntt.rs, Bridges.fst | 1 sess spike | high | serial after B6 if Bridges touched
  B5   | src/vector/{portable,avx2}.rs (drop ntt_multiply panic_free) | 1 sess | low | parallel (file-disjoint)
  B6   | Hacspec_ml_kem.Commute.Chunk.fst (USER-1 A8) | 1-2 sess | medium | LAND FIRST; gates A1, A3, A5
  B7   | DESCOPE — keep AVX2 SIMD lane lemmas as admit boundary | 0 sess | n/a | n/a

  Sequential within Phase 2: B6 → all others.
  Parallel: B1 ‖ B2 ‖ B3 ‖ B5 (no shared files).
  B4 is high-risk; 1-session spike then defer if blocked.

═══════════════════════════════════════════════════════════════════
PHASE 3 SCOPE — above-trait closure (8 lanes, parallel)
═══════════════════════════════════════════════════════════════════

  Lane | Files | Effort | Depends on | Critical path?
  -----|-------|--------|------------|---------------
  A1   | src/serialize.rs, Chunk.fst (Phase 7c migration) | 1-2 sess | B6 | no
  A2   | src/sampling.rs (Phase 7n migration; combine with USER-10) | 1 sess | none | no
  A3   | src/polynomial.rs, Chunk.fst (USER-7 + 2 add fns)| 2 sess | Phase 1 trait | no
  A4   | src/polynomial.rs (Phase 7.2 std_error_reduce)   | 1-2 sess | A3 templates | OFF (may stay admitted)
  A5   | src/invert_ntt.rs, Bridges.fst, Chunk.fst (USER-6) | 3 sess | Phase 2 trait stable | **YES**
  A6   | src/matrix.rs, Chunk.fst (compute_message etc.)   | 2 sess  | A3 + A5 | **YES**
  A7   | src/ind_cpa.rs, Makefile (unadmit Ind_cpa)        | 2 sess  | A1, A2, A6 | **YES**
  A8   | src/ind_cca.rs, src/matrix.rs, Makefile           | 2 sess  | A7 | **YES**

  Sequential: A5 → A6 → A7 → A8 (the critical path; ~9 sessions wall).
  Parallel with critical path: A1, A2, A3 can run alongside A5.
  Risk-tier: A4 may not converge — leave admitted if blocked, doesn't gate ind_cpa/ind_cca.

  Note: A2 should fold in USER-10 (rej_sample post wiring) since
  the sampling lane is already touching the impl-side rejection loop.

═══════════════════════════════════════════════════════════════════
USER-LANE WORK (parallel to all phases)
═══════════════════════════════════════════════════════════════════

USER-1 — `lemma_compress_ciphertext_coefficient_fe_commute` (a.k.a. A8)
  4-case Barrett-exactness enumeration; templated by USER-A5/A7 prior
  work.  Anytime; gates Phase 7c (lane A1).

USER-2 — `lemma_ntt_full_commute` (Tier-3 forward NTT composition)
  Depends on Wave 3 / Phase 7b lemmas.

USER-3 — `to_standard_domain` Montgomery inverse identity
  Standalone modular arithmetic; anytime.

USER-4 — AVX2 NTT-layer 1/2 SIMD bridges (Z3-blocked)
  Mitigation paths in MLKEM_STATUS.md; high risk.

USER-5 — `ntt_multiply` Tier-3 wrap (after USER-2).

USER-6 — `invert_ntt_montgomery` strengthened post (after USER-2;
  this is essentially lane A5).

USER-7 — `subtract_reduce` body discharge (post-loop record-equality
  bridge); 4 hypotheses (a)-(d) in MLKEM_STATUS.md; this is lane A3.

USER-8 — Cluster 2 from_bytes / to_bytes BitVec wire-up (Phase 1
  deferred; ~90 min).

USER-9 — Cluster 3 serialize_5/11 + deserialize_5/11 trait post wire-up
  (Phase 1 deferred; gated on AVX2 SIMD→BitVec bridge).
  The 4 portable lemmas already exist (`a51ddbfc3`).

USER-10 — Cluster 4 rej_sample post wire-up (Phase 1 deferred;
  combine with lane A2).

═══════════════════════════════════════════════════════════════════
COORDINATOR'S RESPONSIBILITY — overall proof status
═══════════════════════════════════════════════════════════════════

The coordinating session (whoever spawns the lane agents) must keep a
tight overview of OVERALL admit count, not per-lane "did the lane's
target compile" stats.  Use this rubric every time a lane reports back:

  • **PROGRESS**: an existing admit (`--admit_smt_queries true`,
    `panic_free`, `lax`, or `admit ()`) was REMOVED and the proof
    closes for real.  Net admit count goes DOWN.
  • **SIDEWAYS**: an admit was moved to a NEW admitted lemma (the
    lemma exists to delegate the admit further down).  Net admit
    count is unchanged or up.  This is sometimes the right move —
    e.g., factoring out a 4-case Barrett enumeration into a single
    admitted lemma the user can attack — but the coordinator must
    notice it isn't progress.
  • **FAIR GAME**: a NEW admit scoped to a small, well-defined
    arithmetic or bitvector property (≤10 lines of math).  Counts as
    sideways but cheap — file under USER-N for the user to close, do
    not block the lane on it.

After every lane merge: re-run `make` from `proofs/fstar/extraction/`
and grep for admits.  Track the running count in a coordinator note;
flag if the count is rising.

═══════════════════════════════════════════════════════════════════
F*/Z3 TIME BUDGET — when to step back
═══════════════════════════════════════════════════════════════════

Proof failures in F*/Z3 burn 5-30 min per attempt.  If a single
function or lemma is not closing after **20 minutes of strategy
iteration** (rlimit bumps, split_queries, opacity tweaks, lemma
factoring), STOP and audit:

  (a) **Is the property actually true?**  Counter-example check:
      pick concrete values, compute by hand, see if both sides agree.
      Many "Z3 walls" are actually subtle off-by-one or sign errors
      that no amount of rlimit will fix.
  (b) **Is the property truly needed?**  Often the post is stronger
      than the consumer requires; relaxing the post (or moving the
      strong form into a separate lemma the consumer cites only when
      it needs it) sidesteps the Z3 cost entirely.
  (c) **Is the user better placed to close it?**  Calc-style proofs,
      bit-vector bashes, and 4-case Barrett enumerations are often
      faster for a human with the smtprofiling skill than for an
      agent burning rlimit.  In that case: ADMIT, add a USER-N entry
      with the math + counter-example + best-strategy notes, MOVE ON.

Default to (c) when 20 min has passed.  Sunk-cost on a single Z3
wall is the largest source of session-wide slip; the sprint plan
budgets sessions per lane, not per lemma.

═══════════════════════════════════════════════════════════════════
HARD RULES (carried over from Phase 1)
═══════════════════════════════════════════════════════════════════

R1 Phases 2 and 3 fan out across worktrees per lane-split-protocol.
   Use `agent/<lane>` branch convention.
R2 Maintain SD1 (mod-q opacity), SD2 (forall<N> over generic forall),
   SD3 (opaque per-branch wrappers) per lane-split-protocol.md.
R3 No new admits anywhere — *unless* the admit is a small,
   well-scoped arithmetic / bitvector property handed off to a
   USER-N lane (per the coordinator's rubric above).  If a lane's
   discharge fails on the body of its assigned function, roll back
   the lane's commits and document — don't paper over with broad
   `panic_free`.
R4 ulimit -v 8388608, F* rlimit ≤ 800.
R5 Inner loop: plain `make check/<Mod>.fst` from
   `proofs/fstar/extraction/`.
R6 Hard cap 1 session per lane (B-lanes) / 2-3 sessions per A-lane
   (per the table above).  If a lane exceeds budget, STOP and document.
   Within a lane, hard cap 20 min per function/lemma before
   triggering the step-back audit (see "F*/Z3 TIME BUDGET" above).
R7 Don't bulk-delete `.checked` files — `make` handles staleness.
   Surgical `rm` only the target's `.checked` when iterating, and even
   then prefer `touch <file>.fst` to invalidate downstream.
R8 fstar-mcp is unreliable on this branch (per Phase 0 study); use
   plain `make` for the inner loop.

═══════════════════════════════════════════════════════════════════
COORDINATION CONVENTIONS
═══════════════════════════════════════════════════════════════════

`Hacspec_ml_kem.Commute.Chunk.fst` is the hot file (touched by B6,
A1, A3, A5, A6).  Each lane appends to a clearly-marked `(* Phase 7X
additions *)` section; never edit existing lemma bodies.

`Hacspec_ml_kem.Commute.Bridges.fst` is touched by A5 (and B4).
Sequence A5 after B4 if both run.

Makefile is edited by A7 then A8 sequentially.

Trait edits (`src/vector/traits.rs`) are FROZEN in Phase 2/3.  If you
discover a finding, log it in `proofs/agent-status/lane-split-protocol.md`
under "Open findings" — do NOT edit traits.rs.

═══════════════════════════════════════════════════════════════════
MERGE ORDER back to `trait-opacify`
═══════════════════════════════════════════════════════════════════

  1. B1, B5 (low-risk file-disjoint) — clear backlog
  2. B6 (Chunk.fst foundation; gates Phase 3)
  3. B3, B2 (medium effort, fan out)
  4. A2, A1 (Phase 3 disjoint pair; A2 absorbs USER-10)
  5. A3 (sequential after B6 to serialize Chunk merges)
  6. A5 (sequential after A3)
  7. A6 → A7 → A8 (strictly sequential consumer chain)
  8. B4 (or descoped) — last, lowest priority
  9. A4 — opportunistic; can land any time after A3 if it converges
  USER-8, USER-9 — anytime, low-priority cleanup.

CRITICAL PATH WALL TIME (max-parallel):
  Phase 1 (✅ done) → A5 (3) → A6 (2) → A7 (2) → A8 (2) ≈ 9 sessions
```

---

## Why this prompt is structured this way

- **Sprint state foreground**: every fresh agent needs Phase 1's
  partial outcome (what landed, what's deferred) up front.  Cluster 3's
  partial state is non-obvious — the 4 lemmas exist as preparation but
  the trait wiring is held.
- **USER-8 / USER-9 / USER-10 are NEW**: Phase 1 deferrals get explicit
  USER-N entries so they don't get lost in the agent-trackA log.
- **Trait is FROZEN**: Phase 2/3 lanes must NOT touch traits.rs; any
  trait gap they find goes to lane-split-protocol "Open findings" so
  the trait owner can decide.
- **Phase 2 ordering preserved**: B6 (Chunk.fst foundation) lands first
  — same gate as before; Phase 1 doesn't change the inter-lane
  ordering.
