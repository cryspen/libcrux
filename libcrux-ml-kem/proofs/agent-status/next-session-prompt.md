# Next-session resume prompt — Post-Phase H, ready for Phase 1

Phase H (opaque mod_q at trait boundary) committed at `08dedde99`.
The end-to-end sprint plan is consolidated at
`~/.claude/plans/immutable-snacking-dewdrop.md`.

Paste the block below into a fresh Claude Code session opened in
`/Users/karthik/libcrux-trait-opacify/libcrux-ml-kem`.

---

```
You are picking up the libcrux-ml-kem F* verification sprint after
Phase H landed (commit `08dedde99` on `trait-opacify`).

═══════════════════════════════════════════════════════════════════
SPRINT STATUS
═══════════════════════════════════════════════════════════════════

✅ Phase 0 (canonical edit-check loop empirical study) — verdict:
   plain `make check/<Mod>.fst` from `proofs/fstar/extraction/`.
   Report: `proofs/agent-status/edit-check-loop-comparison.md`.

✅ Phase H (opaque mod_q at trait boundary) — DONE 2026-04-29.
   `Hacspec_ml_kem.ModQ.fst` defines opaque `mod_q` and `mod_q_eq`.
   4 trait posts (barrett_reduce, mont_mul_by_constant, cond_subtract,
   to_unsigned_representative) now use `mod_q_eq` form.  Above-trait
   Z3 contexts no longer see raw `% 3329`.  All verifies clean:
   ModQ.fst (8s), Commute.Chunk.fst (70s), Vector.Portable.fst (59s),
   Vector.Avx2.fst (63s), Polynomial.fst, Invert_ntt.fst.

⏸ Phase 1 (trait pre/post fixes) — NEXT.  ~1 session, single-agent.
⏸ Phase 2 (below-trait closure, 7 lanes parallel) — gated on Phase 1.
⏸ Phase 3 (above-trait closure, 8 lanes parallel) — gated on Phase 2.

Critical path: Phase 1 → A5 (3 sess) → A6 (2) → A7 (2) → A8 (2)
≈ 10-11 total sessions.

═══════════════════════════════════════════════════════════════════
ENVIRONMENT VERIFY (do this first)
═══════════════════════════════════════════════════════════════════

  cd /Users/karthik/libcrux-trait-opacify
  git status              # clean on trait-opacify (mod unrelated diffs)
  git log --oneline trait-opacify -3
  # Should show:
  #   08dedde99 agent-trackA: Phase H — opaque mod_q at trait boundary + lane-split protocol
  #   a62dd9ce0 agent-trackA: USER-7 — handoff for subtract_reduce body discharge
  #   0a8c7289d agent-trackA: add per-poly commute lemma for subtract_reduce (mitigation b)

═══════════════════════════════════════════════════════════════════
RESUME PROTOCOL — read these in order
═══════════════════════════════════════════════════════════════════

  1. ~/.claude/plans/immutable-snacking-dewdrop.md
     (the consolidated sprint plan; Phase 1 details are in §"Phase 1")
  2. proofs/agent-status/lane-split-protocol.md
     (worktree split, cherry-pick discipline, style rules SD1-SD3)
  3. proofs/agent-status/edit-check-loop-comparison.md
     (canonical inner loop verdict)
  4. MLKEM_STATUS.md
     (USER-1 through USER-7 task list, especially USER-7 for the
      currently-admitted subtract_reduce body)
  5. proofs/agent-status/agent-trackA.md
     (recent-session log)

═══════════════════════════════════════════════════════════════════
PHASE 1 SCOPE — what this session does
═══════════════════════════════════════════════════════════════════

Modify `src/vector/traits.rs` and re-extract `Vector.Traits.Spec.fst`.
Batch into clusters; one trait commit per cluster.

CLUSTER 1 (low-risk, post-only conjuncts):
  • Add output bounds to `add_post`, `sub_post`, `multiply_by_constant_post`,
    `negate_post`.  Derivable from existing `is_intb` pre.
  • Documentation comments on `to_unsigned_representative` (kept algebraic-
    int intentionally), `montgomery_multiply_by_constant` pre asymmetry,
    `add`/`sub` pre on sums.

CLUSTER 2 (modest impl-side proof):
  • `from_bytes`, `to_bytes`: pull in existing `from_le_bytes_post_N` /
    `to_le_bytes_post_N` helpers.  Portable-side discharge via existing
    BitVecEq pattern; AVX2 may need an intrinsic↔BitVec bridge (defer
    if heavy).

CLUSTER 3 (gated on 30-min spike):
  • `serialize_5/11`, `deserialize_5/11`: replace TODO with existing
    pre/post helpers.  Requires 4 new lemmas in `src/vector/portable/
    serialize.rs` mirroring `serialize_10_lemma`.  SPIKE: write
    `serialize_5_int_lemma`. If closes <30 min, land all 4. Else defer.

CLUSTER 4 (defer):
  • `rej_sample`: leave weak with sharpened TODO.

Each cluster:
  1. Edit `traits.rs` (one cluster's worth).
  2. `python3 hax.py extract`.
  3. `make check/Libcrux_ml_kem.Vector.Traits.Spec.fst`.
  4. `make check/Libcrux_ml_kem.Vector.Portable.fst` — must pass.
  5. `make check/Libcrux_ml_kem.Vector.Avx2.fst` — must pass.
  6. Commit cluster (single commit per cluster — keep `git bisect`
     useful).

═══════════════════════════════════════════════════════════════════
HARD RULES
═══════════════════════════════════════════════════════════════════

R1 Phase 1 is single-agent serial.  Don't fan out to multiple lanes
   yet — Stage 2/3 fan out once trait is frozen.
R2 Maintain SD1 (mod-q opacity), SD2 (forall<N> over generic forall),
   SD3 (opaque per-branch wrappers) per lane-split-protocol.md.
R3 No new admits anywhere.  If Cluster N's impl-side discharge fails,
   roll back the cluster and document.
R4 ulimit -v 8388608, F* rlimit ≤ 800.
R5 Inner loop: plain `make check/<Mod>.fst`.  Don't reach for
   fstar-mcp or admit-everything-else (per Phase 0 verdict).
R6 Hard cap 90 min per cluster.  If a cluster doesn't close in 90,
   STOP, document the gap, hand off.

═══════════════════════════════════════════════════════════════════
DELIVERABLES (this session)
═══════════════════════════════════════════════════════════════════

  • 2-4 commits (one per cluster that lands).
  • Updated `MLKEM_STATUS.md` with new Phase 1 entries.
  • New entry in `proofs/agent-status/agent-trackA.md`.
  • If Cluster 4 (rej_sample) deferred: explicit USER-N entry added
    to MLKEM_STATUS.md.

REPORT one paragraph entry summary at end-of-session.

═══════════════════════════════════════════════════════════════════
AFTER PHASE 1 — Phase 2 + 3 parallel/sequential breakdown
═══════════════════════════════════════════════════════════════════

Once Phase 1 lands, the trait contract is FROZEN.  Phases 2 (below-trait
closure) and 3 (above-trait closure) fan out to parallel agents.

PHASE 2 (below-trait, 7 lanes, parallel after Phase 1):

  Each lane works in its own worktree off `trait-opacify` HEAD post-
  Phase-1.  Per-lane Makefile admits all OTHER lanes' modules — see
  lane-split-protocol.md.  Lanes touching `Commute.Chunk.fst` must
  serialize through B6 (sequential); the rest are file-disjoint.

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

PHASE 3 (above-trait, 8 lanes, parallel after Phase 2):

  Lane | Files | Effort | Depends on | Critical path?
  -----|-------|--------|------------|---------------
  A1   | src/serialize.rs, Chunk.fst (Phase 7c migration) | 1-2 sess | B6 | no
  A2   | src/sampling.rs (Phase 7n migration)             | 1 sess   | none | no
  A3   | src/polynomial.rs, Chunk.fst (USER-7 + 2 add fns)| 2 sess   | Phase 1 trait | no
  A4   | src/polynomial.rs (Phase 7.2 std_error_reduce)   | 1-2 sess | A3 templates | OFF (may stay admitted)
  A5   | src/invert_ntt.rs, Bridges.fst, Chunk.fst (USER-6) | 3 sess | Phase 2 trait stable | **YES**
  A6   | src/matrix.rs, Chunk.fst (compute_message etc.)   | 2 sess  | A3 + A5 | **YES**
  A7   | src/ind_cpa.rs, Makefile (unadmit Ind_cpa)        | 2 sess  | A1, A2, A6 | **YES**
  A8   | src/ind_cca.rs, src/matrix.rs, Makefile           | 2 sess  | A7 | **YES**

  Sequential: A5 → A6 → A7 → A8 (the critical path; ~9 sessions wall).
  Parallel with critical path: A1, A2, A3 can run alongside A5.
  Risk-tier: A4 may not converge — leave admitted if blocked, doesn't gate ind_cpa/ind_cca.
  Sequential within parallel: A1 depends on B6; A3 depends on Phase 1 trait stability.

COORDINATION:

  • `Hacspec_ml_kem.Commute.Chunk.fst` is the hot file (touched by B6,
    A1, A3, A5, A6).  Convention: each lane appends to a clearly-
    marked `(* Phase 7X additions *)` section.  Never edit existing
    lemma bodies.
  • `Hacspec_ml_kem.Commute.Bridges.fst` is touched by A5 (and B4).
    Sequence A5 after B4 if both run.
  • Makefile is edited by A7 then A8 sequentially.

MERGE ORDER back to `trait-opacify`:

  1. B1, B5 (low-risk file-disjoint) — clear backlog
  2. B6 (Chunk.fst foundation; gates Phase 3)
  3. B3, B2 (medium effort, fan out)
  4. A2, A1 (Phase 3 disjoint pair)
  5. A3 (sequential after B6 to serialize Chunk merges)
  6. A5 (sequential after A3)
  7. A6 → A7 → A8 (strictly sequential consumer chain)
  8. B4 (or descoped) — last, lowest priority
  9. A4 — opportunistic; can land any time after A3 if it converges

CRITICAL PATH WALL TIME (max-parallel):
  Phase 1 (1 sess) → A5 (3) → A6 (2) → A7 (2) → A8 (2) ≈ 10 sessions

For full lane briefs (40-word starter prompts), see
`~/.claude/plans/immutable-snacking-dewdrop.md` §"Phase 2/3".
```

---

## Why this prompt is structured this way

- **Sprint state foreground**: every fresh agent needs to know what
  phases are done and which is next.  Phase H is non-obvious (it's a
  hygiene phase, not a feature) so its verdict is summarized.
- **Resume protocol order matters**: plan file first (high-level), then
  protocol (rules), then experiment (canonical loop), then status, then
  log.  Each layer adds more detail.
- **Clusters are explicitly staged**: Cluster 1 is do-immediately,
  Cluster 3 is gated on a spike, Cluster 4 is "defer with intent".
  This prevents the agent from sinking session time into Cluster 3 if
  the spike fails.
- **Hard caps at 90 min/cluster**: Phase 1's whole budget is ~1 session;
  if a cluster runs over, the right move is to STOP rather than push
  through.  This protects critical-path time for Phases 2-3.
