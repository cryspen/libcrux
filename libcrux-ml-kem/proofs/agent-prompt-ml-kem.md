# Agent prompt — ML-KEM milestone push

Paste this into a fresh Claude Code session opened in
`~/libcrux-trait-opacify/libcrux-ml-kem` (auto mode recommended).

This prompt is informed by two prior audits whose synthesis is in
`proofs/agent-status/sprint-learnings.md` (commit it after writing).
Lead with **extraction**, then **VERIFIED_MODULES discipline**, then
**forward NTT trait opacification** — those three account for the
highest LOC-of-impact-per-hour in the entire backlog.

---

You are a single-lane agent for the libcrux-ml-kem F\* verification effort.
Branch: `trait-opacify` (current tip `4672cc005`). Goal: close named
milestones in `proofs/proof_milestones.md`, in priority order, until
the budget runs out.

## Priority order — REVISED per cross-audit synthesis

The first three items are **highest-leverage / lowest-risk** and should
go before any spec/proof work on bodies. They're "force multipliers" —
they unlock dozens of functions at a stroke.

  **0. mlkem.rs extraction** — currently filtered out of hax (`-i
     -libcrux_ml_kem::mlkem::**` in `hax.py` somewhere). Find the
     filter rule and remove it. Validates: `python3 hax.py extract`
     produces `Libcrux_ml_kem.Mlkem.fst`. Once extracted, the 36 fns
     in `src/mlkem.rs` move from Unverified to at-least-PF, and the
     KEM API milestones (rows 19-25 of milestone doc) become
     addressable. ~1 session.

  **1. `Ind_cpa.fst` admit-list audit** — currently in
     `proofs/fstar/extraction/Makefile` ADMIT_MODULES, so all 21 fns
     show as Lax. Per the cross-audit, ML-DSA gained −119 lax in one
     pass by tightening its VERIFIED_MODULES list — analogous discipline
     here. Read the actual fn-level ensures in `src/ind_cpa.rs`; if any
     fns already have proper ensures, take the module off the admit
     list and let per-fn counts surface the real proof state.
     Closes (or partially closes) milestone row 27. ~1-2 sessions.

  **2. Forward NTT trait-opacification (rows 1, 2, 8 of milestone
     doc)** — bounds-only ensures already exist; the hacspec ensures
     are commented out at `src/ntt.rs:277, 318`. Apply the SAME pattern
     that worked for inverse NTT layers 1 and 3 (commit `b7b49c358`):
       - Add `Hacspec_ml_kem.Ntt.ntt_at_layer_n` citations to per-layer
         ensures (mirror the `lemma_inv_ntt_layer_<N>_step_to_hacspec`
         family).
       - Per-branch `ntt_layer_*_step_branch_post` predicates already
         exist in `traits.rs:313-460` — so the trait posts are wired.
         The gap is at the IMPL function ensures.
       - Once the trait-level posts cite hacspec, the Portable and
         AVX2 backends propagate for free (same as the +27 / +23
         hacspec gain on the inverse direction). High leverage.
     ~1 sprint. Pick layers 1, 2, 7 first (most-used in callers).

  3. **USER-15 — `invert_ntt_montgomery` body** (row 7). Spec post is
     already in place; body has `--admit_smt_queries true`. Strategy:
     definitional unfolding lemma in `Bridges.fst` of shape
     `lemma_ntt_inverse_butterflies_unfold` chaining the 7 layer calls
     into `ntt_inverse_butterflies`. ~2-3 sessions.

  4. **USER-14 — `invert_ntt_at_layer_4_plus` body** (row 6). Spec
     post in place; body admitted. Strategy: per-chunk-pair bridge +
     post-loop `Classical.forall_intro` in `Bridges.fst`. Mirror today's
     layer_2 closure pattern (`4672cc005`). ~2-3 sessions.

  5. **USER-13's compress.rs portion** — 3 chunk wrappers (`compress_1`,
     `compress<D>`, `decompress_d`) walled at Z3 saturation. Apply Rule
     SD4 (no global `reveal_opaque` in loop bodies); today's
     `200b01f66` may unlock these. ~1-2 sessions.

## Anti-patterns to avoid (cross-audit lessons)

  **AP-1 Big-axiom-bridge designs** — the
     `Hacspec_ml_kem.Serialize.HacspecBridge` approach was abandoned
     after 11 commits on `agent/phase-7c-serialize`. Don't write a
     general bridge axiom that connects layer N+1 to layer N for all
     instances at once. Pick one width / one instantiation, prove it,
     generalize only after the second falls into the same shape.

  **AP-2 GLOBAL `reveal_opaque (\`%P) (P)` in loop bodies (Rule SD4)**
     — single line caused the 153 s top-1 wall; fix dropped to 2.1 s.
     Pre-flight grep: `grep -rn 'reveal_opaque.*%[^)]*) *([A-Z][A-Za-z_.]*) *)$' src/`
     Use targeted form: `reveal_opaque (\`%P) (P arg1 arg2)`.

  **AP-3 Bulk-deleting `.checked` files** — surgically remove only the
     module being iterated. Don't `rm` the whole cache.

  **AP-4 Trusting hint replay across ensures upgrades** — strengthening
     one fn's ensures shifts line numbers, breaks downstream replay
     (saw it on layer_3 + Vector.Avx2.impl_3 today). After every milestone
     closure that strengthens an ensures, re-record hints for the
     module + its consumers and commit them.

## Hard rules

  R1 Branch `trait-opacify` directly. User merges to origin manually.
  R2 No NEW broad admits. `--admit_smt_queries true` is OK as a
     temporary scaffold; remove before committing each closure.
  R3 No new axioms unless absolutely necessary. If you must, file as
     SIDEWAYS in `MLKEM_STATUS.md` + commit message.
  R4 `ulimit -v 8388608`. F\* `--z3rlimit ≤ 800`. Default tier:
     `--z3rlimit 200`. Bump only after profiling.
  R5 Inner edit-check: `make check/<Mod>.fst` from
     `proofs/fstar/extraction/`. Cap iteration at 20 min/attempt.
  R6 Always re-record hints AND touch unchanged `.checked` after
     `python3 hax.py extract` (per `feedback_touch_unchanged_checked`).
  R7 Trait FROZEN — DO NOT touch `src/vector/traits.rs` (the trait
     contract). Only impl-side bodies, Bridges/Chunk additions, and
     consumer-side strengthening.
  R8 No `fstar-mcp` (per `feedback_use_fstar_mcp` and
     `feedback_fstar_mcp_session_dies_after_make`).
  R9 After each milestone closure: regenerate
     `proofs/verification_status.md` and update `proof_milestones.md`
     status icon. Commit prefix: `agent-mlkem:`.

## Workflow

  1. Read `proofs/proof_milestones.md` (your TODO list) +
     `proofs/agent-status/sprint-learnings.md` (synthesis of both
     audits) + `proofs/agent-status/lane-split-protocol.md` (SD1/2/3/4).
  2. Pick the first milestone from the priority list (start with #0).
  3. Make the change. Iterate `make check/<Mod>.fst` until clean.
  4. `python3 proofs/generate_verification_status.py` to refresh report.
  5. Update `proof_milestones.md` row status + add commit SHA.
  6. Commit. Move to next.
  7. Cap: 4-5 milestones or 4 hours total.

## Per-build hygiene (paste-ready)

  ```bash
  cd ~/libcrux-trait-opacify/libcrux-ml-kem
  cd proofs/fstar/extraction
  find . -maxdepth 1 \( -name "Libcrux_ml_kem*.fst" -o -name "Libcrux_ml_kem*.fsti" \) | sort | xargs shasum > /tmp/pre.sha
  cd ../../..
  python3 hax.py extract
  cd proofs/fstar/extraction
  # Local fix for hax codegen bug — duplicate noeq on Neon Vector_type
  sed -i '' '7,8d' Libcrux_ml_kem.Vector.Neon.Vector_type.fsti 2>/dev/null
  find . -maxdepth 1 \( -name "Libcrux_ml_kem*.fst" -o -name "Libcrux_ml_kem*.fsti" \) | sort | xargs shasum > /tmp/post.sha
  diff /tmp/pre.sha /tmp/post.sha > /tmp/diff.sha
  for f in $(find . -maxdepth 1 \( -name "Libcrux_ml_kem*.fst" -o -name "Libcrux_ml_kem*.fsti" \)); do
    base=$(basename $f); chk=/Users/karthik/libcrux-trait-opacify/.fstar-cache/checked/$base.checked
    if ! grep -qF "$base" /tmp/diff.sha && [ -f "$chk" ]; then touch "$chk"; fi
  done
  ```

## Deliverable

End-of-session report (≤ 200 words):
  - Milestones closed (✅) with commit SHAs.
  - Milestones partially advanced (🔶 → improved).
  - Any new admits/axioms (R3).
  - F\* perf delta on affected modules vs `proofs/agent-status/fstar-perf-top20.md`.
  - Final commit SHA.
  - Next-priority recommendation for the FOLLOWING session.

DO NOT push to origin. DO NOT touch `~/libcrux-ml-dsa-proofs` or
`~/libcrux-sha3-focused`.
