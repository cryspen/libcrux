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

  **0. mlkem.rs extraction — DONE 2026-04-30 (commit `86c48def7`).**
     Was: filtered out via `mlkem.rs`'s `#![cfg(feature = "incremental")]`
     gate combined with hax.py only enabling `simd128,simd256`.
     Fix: added `incremental` to features + `-i` filters for the
     runtime-dispatch alloc submodules + post-extract delete of
     `.Alloc.fst` / `.Incremental.Rand.fst` files (Box<dyn Keys> and
     try_fill_bytes lack F* models).  Net: −57 Unv, +57 Lax (admitted
     pending row 19-25 PF work).  See commit message for details.

  **1. `Ind_cpa.fst` admit-list audit — ATTEMPTED 2026-04-30
     (commit `c04830b8a`).**  Bulk un-admit fails: `serialize_vector`
     (src/ind_cpa.rs:139, F* line 25-108) hits "incomplete quantifiers"
     at the line-105 assertion after 202 s with `--z3rlimit 1000`.
     Other 18 fns may verify; needs per-fn `verification_status(lax)`
     on serialize_vector then re-attempt the bulk un-admit.  Re-added
     to ADMIT_MODULES for now.  ~1-2 sessions remaining.

  **2. Forward NTT trait-opacification (rows 1, 2, 8 of milestone
     doc)** — bounds-only ensures already exist; the hacspec ensures
     are commented out at `src/ntt.rs:277, 318`.
     **Updated 2026-04-30**: layer 1 done in commit `c32653051`
     (mirror of inverse layer 1 commit `8358b1093`, verified 349 s).
     For layers 2, 3, 7 the per-vector Bridges lemma
     `lemma_ntt_layer_<N>_step_to_hacspec` does NOT exist — only
     chunk-level `lemma_ntt_layer_<N>_step_chunk_commutes` in
     `Hacspec_ml_kem.Commute.Chunk.fst`. **Spec-side authoring is the
     blocker**, not impl-side ensures wiring.
     Reference commits for the inverse-NTT pattern:
       - layer 1: `8358b1093` (impl ensures), Bridges lemma at
         `Hacspec_ml_kem.Commute.Bridges.fst:150`.
       - layer 2: `b7b49c358` (Bridges lemma) + `4672cc005`
         (impl ensures wiring).
       - layer 3: `fa2151ea8` (Bridges lemma) + `43c9d45d5`
         (impl ensures wiring).
     Workflow per layer:
       1. Author `lemma_ntt_layer_<N>_step_to_hacspec` in
          `Hacspec_ml_kem.Commute.Bridges.fst` (mirror inverse).
       2. Wire impl-side ensures in `src/ntt.rs::ntt_at_layer_<N>`
          via per-chunk loop invariant + post-loop
          `Classical.forall_intro` (Option B).
       3. Verify with `--z3rlimit 800 --split_queries always`.
     Per-branch `ntt_layer_*_step_branch_post` predicates already
     exist in `traits.rs:313-460` — trait posts wired for layers 1
     and 2.  Layer 7 has no branch_post and no chunk_commute (it's a
     between-chunk butterfly, structurally different — own design).
     ~1 sprint per layer (NOT 1 sprint total); layers 2, 3 first.

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
