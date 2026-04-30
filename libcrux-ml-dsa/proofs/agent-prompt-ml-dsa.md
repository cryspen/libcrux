# Agent prompt — ML-DSA milestone push

Paste this into a fresh Claude Code session opened in
`~/libcrux-ml-dsa-proofs/libcrux-ml-dsa` (auto mode recommended).

This prompt is informed by two prior audits whose synthesis is in
`proofs/sprint-learnings.md`. Per cross-audit consensus: ML-DSA's
biggest gap is **spec-module design, not proof effort.** Lead with
that.

---

You are a single-lane agent for the libcrux-ml-dsa F\* verification effort.
Branch: `ml-dsa-proofs` (current tip `f7d7f6c9f`). Goal: close named
milestones in `proofs/proof_milestones.md`.

## Priority order — front-loaded on spec design

  **0. `VERIFIED_MODULES` audit** — analogous to ML-KEM's `Ind_cpa.fst`
     gap. ml-dsa's Makefile uses an *inverted* admit pattern:
     `ADMIT_MODULES = $(filter-out VERIFIED_OR_SLOW_MODULES, $(wildcard *.fst))`.
     Many modules in extraction have proper ensures but are admitted
     because they aren't on the VERIFIED list. Scan
     `proofs/fstar/extraction/Makefile`'s VERIFIED_MODULES list against
     the actual extraction directory; for each module not on the list,
     check if its fns have proper ensures and (if so) add it. Per
     cross-audit, ML-DSA gained −119 lax this way in a prior pass —
     repeat the discipline. Cheapest move available. ~1-2 sessions.

  **1. Design `Hacspec_ml_dsa.Ntt.*` spec module** — *this gates every
     ml-dsa NTT correctness milestone* (rows 1-7 of milestone doc).
     Currently no `Hacspec_ml_dsa.*` references exist anywhere in
     `src/`. Mirror `Hacspec_ml_kem.{Invert_ntt, Ntt}` structure under
     `specs/ml-dsa/proofs/fstar/extraction/`:
       - `Hacspec_ml_dsa.Ntt.fst` — top-level forward `ntt` spec.
       - `Hacspec_ml_dsa.Invntt.fst` — inverse spec.
       - `Hacspec_ml_dsa.Commute.{Bridges, Chunk}.fst` (NEW directory) —
         the impl↔spec bridge layer (analogue of
         `specs/ml-kem/proofs/fstar/commute/`).
     Do NOT wire any ensures yet. ~1 sprint. The bounds-only ensures
     on `src/ntt.rs::{ntt, invert_ntt_montgomery, reduce,
     ntt_multiply_montgomery}` stay as-is until the spec lands.

  **2. Per-SIMD-unit NTT layer hacspec wiring (Portable, then AVX2)** —
     once (1) lands. Mirror ML-KEM's `lemma_inv_ntt_layer_<N>_step_to_hacspec`
     pattern. Trait posts at `src/simd/traits.rs` need per-branch
     `inv_ntt_layer_<N>_step_branch_post` opaque predicates (SD3
     pattern from ML-KEM). Below-trait propagates for free.
     ~2-3 sprints across all 7 layers + their inverses.

  **3. Top-level `ntt` / `invert_ntt_montgomery` correctness ensures
     (rows 1-3)** — once (1) and (2) land, these are mechanical
     compositions. ~1-2 sessions per fn.

  **4. Design `Hacspec_ml_dsa.Encoding.*` spec modules** (rows 9-15) —
     8 modules: T0, T1, gamma1, error, commitment, signature,
     signing_key, verification_key. Analogous to (1) but for
     encoding. ~1 sprint per encoding × 8 — front-loaded on the
     spec definitions, then per-fn ensures wiring.

  **5. Top-level API (sign, verify, generate_key_pair) correctness
     (rows 17-23)** — gated on (1)+(2)+(3)+(4). Many sprints.

## Anti-patterns to avoid (cross-audit lessons)

  **AP-1 Big-axiom-bridge designs** — don't write a general
     "axiom-bridge" connecting the impl to the spec layer in one
     theorem. Pick one width / one variant (e.g. ML-DSA-44 first),
     prove it, generalize after. Per cross-audit: ML-KEM's
     `Hacspec_ml_kem.Serialize.HacspecBridge` was abandoned after 11
     commits; the per-width `panic_free` strategy is what produced
     gains.

  **AP-2 Defining ensures without first defining the spec** — bounds-
     only ensures are not a "proof gap"; they're a "spec gap". Don't
     add `Hacspec_ml_dsa.Ntt.foo` citations to a function before
     `Hacspec_ml_dsa.Ntt.foo` exists. The path is: define spec →
     test spec is well-formed → wire ensures → prove.

  **AP-3 GLOBAL `reveal_opaque (\`%P) (P)` in loop bodies (Rule SD4)**
     — ML-KEM saw a 153 s top-1 wall caused by one such line; fix
     dropped to 2.1 s. Use targeted form `reveal_opaque (\`%P) (P
     arg1 arg2)` or just an `assert (P args)` first.

## Hard rules

  R1 Branch `ml-dsa-proofs` directly. User merges to origin manually.
  R2 No NEW broad admits.
  R3 No new axioms unless absolutely necessary. File as SIDEWAYS in
     `MLDSA_STATUS.md` + commit message.
  R4 `ulimit -v 8388608`. F\* `--z3rlimit ≤ 800`. Default `--z3rlimit 200`.
  R5 Inner edit-check: `make check/<Mod>.fst` from
     `proofs/fstar/extraction/`. Cap 20 min/attempt.
  R6 Re-record hints + touch unchanged `.checked` after extract.
  R7 SIMD trait FROZEN unless adding NEW posts (per cross-audit AP-2).
  R8 After each milestone: regenerate `proofs/verification_status.md`,
     update `proof_milestones.md` status, commit prefix `agent-mldsa:`.

## Workflow

  1. Read `proofs/proof_milestones.md` (TODO list) +
     `proofs/sprint-learnings.md` (cross-audit synthesis).
  2. Pick first milestone (start with #0 — VERIFIED_MODULES audit).
  3. Iterate `make check/<Mod>.fst` until clean.
  4. `python3 proofs/generate_verification_status.py` to refresh report.
  5. Update `proof_milestones.md` row status + commit SHA.
  6. Commit. Move to next.
  7. Cap: 3-4 milestones or 4 hours total.

## Per-build hygiene (paste-ready)

  ```bash
  cd ~/libcrux-ml-dsa-proofs/libcrux-ml-dsa
  cd proofs/fstar/extraction
  find . -maxdepth 1 \( -name "Libcrux_ml_dsa*.fst" -o -name "Libcrux_ml_dsa*.fsti" \) | sort | xargs shasum > /tmp/pre.sha
  cd ../../..
  python3 hax.py extract  # or hax.sh — check what's there
  cd proofs/fstar/extraction
  find . -maxdepth 1 \( -name "Libcrux_ml_dsa*.fst" -o -name "Libcrux_ml_dsa*.fsti" \) | sort | xargs shasum > /tmp/post.sha
  diff /tmp/pre.sha /tmp/post.sha > /tmp/diff.sha
  for f in $(find . -maxdepth 1 \( -name "Libcrux_ml_dsa*.fst" -o -name "Libcrux_ml_dsa*.fsti" \)); do
    base=$(basename $f); chk=$(realpath ../../../..)/.fstar-cache/checked/$base.checked
    if ! grep -qF "$base" /tmp/diff.sha && [ -f "$chk" ]; then touch "$chk"; fi
  done
  ```

## Deliverable

End-of-session report (≤ 200 words):
  - Milestones closed (✅) with commit SHAs.
  - VERIFIED_MODULES audit result: which modules were taken off the
    admit list and why.
  - Spec modules designed (or scaffolded) — file path + summary.
  - Final commit SHA on `ml-dsa-proofs`.
  - Next-priority recommendation.

DO NOT push to origin. DO NOT touch `~/libcrux-trait-opacify` or
`~/libcrux-sha3-focused`.
