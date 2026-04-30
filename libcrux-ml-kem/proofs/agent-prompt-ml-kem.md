# Agent prompt — ML-KEM continuation (post-2026-04-30 session)

Paste this into a fresh Claude Code session opened in
`~/libcrux-trait-opacify/libcrux-ml-kem` (auto mode recommended).

You are a single-lane agent for the libcrux-ml-kem F\* verification effort.
Branch: `trait-opacify` (current tip `c87d1072e`).

## Previous session deliverables (2026-04-30)

  - **Milestone #0 closed** (`86c48def7`) — mlkem.rs extraction. −57
    Unverified, +57 Lax (new `Mlkem*.Incremental.*` and
    `Ind_cca.Incremental.*` modules admitted in Makefile pending
    per-fn PF; PF work scoped to milestone rows 19-25).
  - **Milestone #2 forward NTT layers 1, 2, 3 closed** via inverse-
    pattern transfer: `c32653051` (layer 1), `744b15937` (layer 2,
    bridge 282 LoC + impl), `0ea02c19e` (layer 3, bridge 152 LoC +
    impl).  +4 Hacspec, −4 Bounds.
  - **Milestone #1 finding documented** (`c04830b8a`) — `Ind_cpa.fst`
    bulk un-admit fails on `serialize_vector` (`src/ind_cpa.rs:139`)
    at line-105 assertion, "incomplete quantifiers" after 202 s
    @ rlimit 1000.
  - **Sprint-learnings codified** (`c87d1072e`) — empirical
    "inverse → forward NTT pattern transfer is robust" finding;
    documents 3 invariants that hold across the transfer + 1
    material divergence (forward butterfly's `z*b` asymmetry needs
    `--z3rlimit 800 --split_queries always` on per-lane wrappers).

## DO NOT TOUCH

  - **USER-14** — `invert_ntt_at_layer_4_plus` body
    (`src/invert_ntt.rs:548`).  User is handling.

## Priority order

  **1. Forward NTT layer 7 bridge + impl** (~1 session).  Layer 7
     is structurally novel but contained:
     - No `f_ntt_layer_7_step` trait function exists; the impl
       (`src/ntt.rs:471 ntt_at_layer_7`) uses
       `multiply_by_constant_bounded(_, _, -1600)` directly with
       `add_bounded`/`sub_bounded`, skipping the trait.
     - Hacspec target: `N.ntt_layer_n 256 p 128 zetas` with
       `zetas` length 1, `zetas[0] == ζ(1)`.
     - First step: identify `mont_lift(-1600) == ζ(1)` (or its
       negation) — spec-side lemma, novel for layer 7.
     - Per-chunk-pair: `result[low_j] = re[j] + ζ * re[j+8]`,
       `result[high_(j+8)] = re[j] - ζ * re[j+8]` for j ∈ 0..8.
     - 8 chunk pairs × 2 lanes (low j, high j+8) → 16 chunk
       results → polynomial-level layer-7 claim.
     - File the bridge in `Hacspec_ml_kem.Commute.Bridges.fst`
       after the forward layer 3 section.

  **2. `Ind_cpa.fst` per-fn audit** (~1 session).  The 2026-04-30
     attempt found `serialize_vector` is the blocker.  Strategy:
     - Add `#[hax_lib::fstar::verification_status(lax)]` to
       `serialize_vector` as a per-fn admit.
     - Drop `Libcrux_ml_kem.Ind_cpa.fst` from
       `proofs/fstar/extraction/Makefile` ADMIT_MODULES.
     - Run `make check/Libcrux_ml_kem.Ind_cpa.fst`.  If other
       functions fail, mark them lax incrementally.
     - Goal: ≥18 of 21 fns flip from Lax → PF/Hacspec.  Closes
       part of milestone row 27.
     - Functions to watch (high z3rlimit annotations seen 2026-04-30):
       `serialize_vector` (1000), `compress_then_serialize_u` (1500),
       `encrypt_unpacked` (800), `deserialize_then_decompress_u` (800),
       `generate_keypair_unpacked` (500), `encrypt` (500).

  **3. Forward NTT top-level `ntt_vector_u`** (gated, NOT yet
     actionable).  Calls layers 4_plus (×4), 3, 2, 1,
     `poly_barrett_reduce`.  Layers 1/2/3 now cite hacspec.
     Forward layer 4_plus has bounds-only post — needs a forward
     analog of the "USER-14 work" before `ntt_vector_u` composes.
     **Not actionable until forward 4_plus is closed (separate
     work item, do not conflate with USER-14 which is the inverse
     direction).**

## Anti-patterns (still load-bearing)

  AP-1 Big-axiom-bridge designs (the Serialize.HacspecBridge
       abandonment lesson).  Pick one width, prove it, generalize
       only after the second falls into the same shape.

  AP-2 GLOBAL `reveal_opaque (\`%P) (P)` in loop bodies (Rule SD4)
       — single line caused the 153 s top-1 wall fix dropped to
       2.1 s.  Use targeted form: `reveal_opaque (\`%P) (P arg1 arg2)`.

  AP-3 Bulk-deleting `.checked` files.  Surgically remove only the
       module being iterated.

  AP-4 Trusting hint replay across ensures upgrades.  After every
       milestone closure that strengthens an ensures, re-record
       hints for the module + its consumers and commit them.

  AP-5 (cross-sprint, ml-dsa origin) `bits USIZE` opacity.  Z3
       cannot derive `v x < bits USIZE` from `v x < 64` under
       `fuel 0`; `assert_norm` does NOT unfold it either.  Tighten
       shift bounds rather than detour into proof-libs.

  AP-6 (cross-sprint, ml-dsa origin) `assert_norm` for arithmetic
       constant chains with subtraction.  Plain `assert
       (v $C == K)` fails under `fuel 0` even when Z3 can compute
       the value if the constant chain has a `-` step.

## Hard rules

  R1 Branch `trait-opacify` directly.  User merges to origin manually.
  R2 No NEW broad admits.  `--admit_smt_queries true` is OK as a
     temporary scaffold; remove before committing each closure.
  R3 No new axioms unless absolutely necessary.  If you must, file
     as SIDEWAYS in `MLKEM_STATUS.md` + commit message.
  R4 `ulimit -v 8388608`. F\* `--z3rlimit ≤ 800`. Default tier:
     `--z3rlimit 200`. Bump only after profiling.
  R5 Inner edit-check: `make check/<Mod>.fst` from
     `proofs/fstar/extraction/`. Cap iteration at 20 min/attempt.
  R6 Always re-record hints AND touch unchanged `.checked` after
     `python3 hax.py extract` (per `feedback_touch_unchanged_checked`).
  R7 Trait FROZEN — DO NOT touch `src/vector/traits.rs` (the trait
     contract).  Only impl-side bodies, Bridges/Chunk additions, and
     consumer-side strengthening.
  R8 No `fstar-mcp` (per `feedback_use_fstar_mcp` and
     `feedback_fstar_mcp_session_dies_after_make`).
  R9 After each milestone closure: regenerate
     `proofs/verification_status.md` and update `proof_milestones.md`
     status icon.  Commit prefix: `agent-mlkem:`.

## Workflow

  1. Read `proofs/agent-status/sprint-learnings.md` (particularly
     the "Cross-sprint deltas (appended 2026-04-30)", "ML-KEM-side
     learnings to mirror back", and "Inverse → forward NTT pattern
     transfer is empirically robust" sections — the latter has the
     forward-bridge recipe codified).
  2. Read `proofs/proof_milestones.md` for current row statuses.
  3. Pick the first priority that's actionable.  Make the change.
  4. Iterate `make check/<Mod>.fst` until clean.
  5. `python3 proofs/generate_verification_status.py` to refresh report.
  6. Update `proof_milestones.md` row status + add commit SHA.
  7. Commit with prefix `agent-mlkem:`.  Move to next.
  8. Cap: 4-5 milestones or 4 hours total.

## Layer 7 forward bridge — orientation pointers

  - Source: `src/ntt.rs:471 ntt_at_layer_7` body (lines 471-510).
    Skip-Mont path; constant `-1600` is the magic value.
  - Hacspec spec: `Hacspec_ml_kem.Ntt.ntt_layer_n` at
    `specs/ml-kem/proofs/fstar/extraction/Hacspec_ml_kem.Ntt.fst:280`.
  - For layer 7: `len = 128`, `groups = 1`, single zeta.
  - Polynomial level (256 coeffs) — different from layers 1-3
    which were per-vector (16 coeffs).  Bridge needs to operate
    poly-level, not chunk-level.
  - Reference for poly-level chain: see `to_spec_poly_mont` in
    `Hacspec_ml_kem.Commute.Chunk` and how
    `invert_ntt_at_layer_4_plus`'s ensures cites
    `IN.ntt_inverse_layer p layer` (impl-pattern, even if body is
    admitted).

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
  - F\* perf delta on affected modules vs
    `proofs/agent-status/fstar-perf-top20.md`.
  - Final commit SHA.
  - Next-priority recommendation for the FOLLOWING session.

DO NOT push to origin.  DO NOT touch `~/libcrux-ml-dsa-proofs` or
`~/libcrux-sha3-focused`.  DO NOT touch
`invert_ntt_at_layer_4_plus` (USER-14, user-handled).
