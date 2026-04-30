# Agent prompt — ML-KEM continuation (post-2026-04-30b session)

Paste this into a fresh Claude Code session opened in
`~/libcrux-trait-opacify/libcrux-ml-kem` (auto mode recommended).

You are a single-lane agent for the libcrux-ml-kem F\* verification
effort.  Branch: `trait-opacify` (current tip `3ab43b5f7`).

## Previous session deliverables (2026-04-30b)

  - **Spec bug fix** (`bbef9328b`) — `src/ind_cpa.rs:136`: changed
    `$out` to `${out}_future` in `serialize_vector`'s ensures.  Without
    `_future`, the post asserted the *input* slice equals
    `vector_encode_12(key)` (false in general).  Audit confirmed this
    was the **only** instance of the `$<param>` (no `_future`) anti-
    pattern across ml-kem, ml-dsa, and sha3.
  - **Row 4 closed** in `proof_milestones.md` — confirmed
    `invert_ntt_at_layer_2` already cites
    `Hacspec_ml_kem.Invert_ntt.ntt_inverse_layer_n` per chunk via
    post-loop `forall_intro` of `lemma_inv_ntt_layer_2_step_to_hacspec`
    (verified in extracted `Invert_ntt.fst{,i}.checked`).  The earlier
    "bounds-only" tracker entry was stale.
  - **Validation attempt** (`3ab43b5f7`) — re-extracted, dropped
    `Libcrux_ml_kem.Ind_cpa.fst` from `ADMIT_MODULES`, ran make at
    rlimit 800.  `serialize_vector` Q2 stalled 532 s before cancel;
    final error "Subtyping check failed" at line 93 (the `Seq.slice
    out` arg to per-iteration `lemma_aux`'s `eq_intro`).  Conclusion:
    **spec fix is necessary but not sufficient** — body needs
    structural work.  `Ind_cpa.fst` restored to `ADMIT_MODULES`.
  - **Audit: Spec.MLKEM dominates the codebase** — 867 refs total
    (324 Rust + 543 F\*); top files `src/ind_cca.rs` (145) and
    `src/ind_cpa.rs` (147).  `Hacspec_ml_kem.*` replacements exist
    for function symbols but `Hacspec_ml_kem.Parameters` lacks
    parameterized size constants (`v_CPA_PUBLIC_KEY_SIZE`-equivalent).
  - **Layer 7 forward bridge — design gap documented**.  Layer 7's
    impl uses plain int multiply by `-1600` (≡ 1729 = `v_ZETAS.[1]`
    mod q) on plain CBD inputs.  Under `mont_i16_to_spec_fe`,
    `mont_lift(-1600) = 2578 ≠ 1729`, so the natural layer-7 bridge
    wants `i16_to_spec_array` (plain), which doesn't compose with
    the existing forward 1/2/3 trait bridges.  Multi-session.

## DO NOT TOUCH

  - **USER-14** — `invert_ntt_at_layer_4_plus` body
    (`src/invert_ntt.rs:548`).  User is handling.

## Priority order

**1. `serialize_vector` body unblock (~1 session).**  Path of least
resistance is **(c) accept `verification_status(lax)` on
`serialize_vector` and un-lax the cascade**.  Likely flips ≥ 18/21
`Ind_cpa.fst` fns from Lax → PF/Hacspec.

  - Add `#[hax_lib::fstar::verification_status(lax)]` to
    `serialize_vector` in `src/ind_cpa.rs:139`.
  - Drop `Libcrux_ml_kem.Ind_cpa.fst` from
    `proofs/fstar/extraction/Makefile` `ADMIT_MODULES`.
  - `python3 hax.py extract` → touch unchanged `.checked` →
    `make check/Libcrux_ml_kem.Ind_cpa.fst`.
  - For each remaining failure, mark THAT function lax incrementally
    (e.g. `serialize_public_key_mut` if it can't compose without a
    real `serialize_vector` post).  Goal: ≥ 18 of 21 fns at PF/Hacspec.
  - Watch: high-rlimit annotations from previous attempt — likely
    blockers if their bodies are similarly Z3-walled:
    `compress_then_serialize_u` (1500), `encrypt_unpacked` (800),
    `deserialize_then_decompress_u` (800), `generate_keypair_unpacked`
    (500), `encrypt` (500).  **Lower rlimits to ≤ 800 (≤ 400 with
    split_queries) when you touch them; don't preserve legacy 1000+
    values** (memory rule `feedback_rlimit_cap_800`).
  - Alternative paths if (c) cascades poorly:
    (a) Factor `serialize_vector`'s `lemma_aux` to a module-scope
    helper that's called once per iteration (the slice-bound subtyping
    is what's heavy).
    (b) Strengthen the loop invariant with an opaque slice-bound
    predicate.

**2. `Spec.MLKEM` removal pass on `src/ind_cpa.rs` and `src/ind_cca.rs`
(~2-3 sessions).**  User mandate: no new `Spec.MLKEM.*` citations and
remove existing ones ASAP (`feedback_avoid_spec_mlkem`).  292 Rust
hits in these two files; the heaviest leverage move available.

  - **First deliverable: parameterized size constants**.  Add to
    `specs/ml-kem/proofs/fstar/extraction/Hacspec_ml_kem.Parameters.fst`
    parameterized versions of the top-5 Spec.MLKEM constants:
    `v_CPA_PUBLIC_KEY_SIZE`, `v_RANKED_BYTES_PER_RING_ELEMENT`,
    `v_ETA1_RANDOMNESS_SIZE`, `v_ETA1`, `v_CCA_PRIVATE_KEY_SIZE`.
    Prove equality to the Spec.MLKEM versions in a Bridges file (one
    lemma per shape).
  - Then per-function migration in `ind_cpa.rs` and `ind_cca.rs`.
    One commit per function or small group.  Watch transitive cites:
    `Libcrux_ml_kem.Vector.to_spec_vector_t` may hit `Spec.MLKEM`
    internally — trace one hop down before committing.

**3. Forward NTT layer 7 bridge** (gated, multi-session).  Lift-
convention design open.  Two candidate resolutions:
  (a) Add a `plain_to_mont_lift` transition lemma at the layer-7
      boundary (cheap, contained).
  (b) Re-state forward 1/2/3 ensures under the plain lift
      (`i16_to_spec_array`) so the chain is uniform (expensive,
      cascades through trait bridges).
  Don't start until the design choice is made.

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

  **AP-7 (NEW, this session)**: `$<param>` instead of
  `${<param>}_future` in `#[hax_lib::ensures(...)]` for `&mut`
  parameters.  Renders the post on the *input*, not the
  post-mutation result — usually false.  Audit confirms only one
  occurrence (now fixed); guard against re-introducing it.

  **AP-8 (NEW, this session, REINFORCED 2026-04-30 mid-session)**:
  bumping `--z3rlimit` past 800 to push through a Z3 wall — and any
  rlimit > 400 when `--split_queries always` is set.  Prohibited
  (`feedback_rlimit_cap_800`).  Z3 perf at high rlimit is
  non-monotone — proofs flip pass/fail across re-runs.  **High-rlimit
  proofs are flake debt.**  When you hit a wall, in order: (1)
  targeted `reveal_opaque (\`%P) (P args)` (Rule SD4); (2) factor a
  lemma to module scope; (3) `--split_queries always` + lower
  per-query rlimit; (4) drive-to-the-top spike; (5) accept
  `verification_status(lax)` and un-lax consumers.  Never bump.
  When TOUCHING legacy code with rlimit > 800 (or > 400 under split),
  REDUCE it in the same commit — don't preserve the flake.

## Hard rules

  R1 Branch `trait-opacify` directly.  User merges to origin manually.
  R2 No NEW broad admits.  `--admit_smt_queries true` is OK as a
     temporary scaffold; remove before committing each closure.
     Per-fn `verification_status(lax)` is the supported per-function
     admit form.
  R3 No new axioms unless absolutely necessary.  If you must, file
     as SIDEWAYS in `MLKEM_STATUS.md` + commit message.
  R4 `ulimit -v 8388608`.  **F\* `--z3rlimit ≤ 800` HARD CAP**;
     **`--split_queries always` cap is `≤ 400` per query** (memory
     rule `feedback_rlimit_cap_800`).  Default tier:
     `--z3rlimit 200`.  Bump only after profiling.  When touching
     legacy code with rlimit > 800, REDUCE it; don't preserve.
  R5 Inner edit-check: `make check/<Mod>.fst` from
     `proofs/fstar/extraction/`.  Cap iteration at 20 min/attempt.
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
  **R10 (NEW)**: NO new `Spec.MLKEM.*` citations.  Use
  `Hacspec_ml_kem.*` (`feedback_avoid_spec_mlkem`).  When touching
  existing Spec.MLKEM ensures opportunistically migrate them in the
  same commit.

## Workflow

  1. Read `proofs/agent-status/session-2026-04-30b.md` (the previous
     session's report, particularly the "Findings" section and the
     "Recommended next session" punch list).
  2. Read `proofs/proof_milestones.md` for current row statuses.
  3. Pick the first priority that's actionable.  Make the change.
  4. Iterate `make check/<Mod>.fst` until clean.
  5. `python3 proofs/generate_verification_status.py` to refresh report.
  6. Update `proof_milestones.md` row status + add commit SHA.
  7. Commit with prefix `agent-mlkem:`.  Move to next.
  8. Cap: 4-5 milestones or 4 hours total.

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
  ulimit -v 8388608
  ```

## Deliverable

End-of-session report (≤ 200 words) at
`proofs/agent-status/session-<date>.md`:
  - Milestones closed (✅) with commit SHAs.
  - Milestones partially advanced (🔶 → improved).
  - Any new admits/axioms (R3) or new lax markers (R2).
  - F\* perf delta on affected modules vs
    `proofs/agent-status/fstar-perf-top20.md`.
  - Final commit SHA.
  - Spec.MLKEM hit count delta if you touched the migration.
  - Next-priority recommendation for the FOLLOWING session.

DO NOT push to origin.  DO NOT touch `~/libcrux-ml-dsa-proofs` or
`~/libcrux-sha3-focused`.  DO NOT touch `invert_ntt_at_layer_4_plus`
(USER-14, user-handled).
