# Next-session resume prompt

Paste the block below into a fresh Claude Code session that opens
in `/Users/karthik/libcrux-trait-opacify/libcrux-ml-kem`.

---

```
You are continuing the multi-agent F* verification effort on
libcrux-ml-kem trait-opacify branch.  The prior session
(2026-04-28, ending tip ba8681b38) completed Phase 7a Step 1:

  * Built Hacspec_ml_kem.Commute.Bridges.fst — sibling module to
    Chunk.fst, containing the function-form per-vector hacspec
    bridges (the slow ones).  Now has BOTH directions:
    - lemma_ntt_layer_1_step_to_hacspec        (forward, agent F's, moved)
    - lemma_inv_ntt_layer_1_step_to_hacspec    (inverse, NEW track A)
    plus their per-lane bridges and helpers.  All verified.
    Bridges.fst is fast on iteration: 5.8s with hints / 98s cold.
  * Chunk.fst is byte-identical to its 2026-04-27 working state
    (8d92695bf).  Editing Bridges.fst doesn't invalidate
    Polynomial.fst.checked etc. — fast inner loop.
  * Step 9 doc comments landed in src/{invert_ntt,polynomial,
    ntt,sampling,serialize}.rs documenting the resolved Mont
    scaling chain (audit findings: ·R⁻¹ form everywhere downstream
    of ntt_multiply, mont_mul(_,1441) finalize collapses to plain).
  * Resolved a Polynomial.fst regression that turned out to be a
    stale .fst extraction (fsti was updated overnight, fst was not).
    Fix: python3 hax.py extract regenerated both consistently.

Your default-action lanes:

  (a) Step 4 (post-strengthen invert_ntt_at_layer_1) — write the
      strengthened ensures + body proof in src/invert_ntt.rs, body
      invokes Hacspec_ml_kem.Commute.Bridges.
        lemma_inv_ntt_layer_1_step_to_hacspec per loop iteration.
      Capture pre-state via `let _re_init = re.coefficients;`.
      Format: forall i. i < 16 ==> mont_i16_to_spec_array(future re
      coefficient i) == IN.ntt_inverse_layer_n 16
      (mont_i16_to_spec_array (re_init i)) 2 (zetas_4 ...zetas...).
      Use fstar-mcp for fast iteration.

  (b) Step 2 layer 2 + 3 inverse bridges in Bridges.fst — same
      pattern as layer 1, but layer 2 trait branch_post has nested
      if-ladder (b → (z, base, off)) that may need explicit
      enumeration of i ∈ {0..15} to avoid Z3 case-splits.  See
      deferred-work comment at end of Bridges.fst.

  (c) Step 3 cross-vector for invert_ntt_at_layer_4_plus — pairs
      of chunks + Barrett reduction (identity on mod-q values).

  (d) Step 7 (add_standard_error_reduce) — independent of the INTT
      track; uses to_standard_domain (mont_mul ×1353) instead of
      mont_mul ×1441.

Hard rules R1-R10 still apply.  Plus four NEW lessons from
last session, saved to memory at
~/.claude/projects/-Users-karthik-libcrux/memory/:

  * Don't bulk-nuke .fstar-cache/checked/*.checked.  make and
    hax.py prove handle stale incrementally.
  * "failed (with hint)" lines in verification_result.txt are
    NOT real failures — F* retries.  Only Error 19 after
    "make Error 1" is real.
  * Use fstar-mcp's typecheck_buffer for iteration (sub-second);
    reserve `make` and `hax.py prove` for end-of-chunk regression
    checks.  Skill at ~/.claude/skills/fstar-mcp/, port 3001.
  * If Polynomial.fst (or any .fst) regresses with "incomplete
    quantifiers" out of nowhere: check mtime against the .fsti.
    A mismatch (.fsti newer than .fst) means stale extraction —
    fix with `python3 hax.py extract`.

Resume protocol — load durable state in this order:

  1. proofs/agent-status/handoff-2026-04-28-trackA.md (THIS FILE'S sibling)
  2. proofs/agent-status/agent-trackA.md     (last session log)
  3. /Users/karthik/.claude/plans/replicated-beaming-pnueli.md  (the plan)
  4. proofs/proof-style-guide.md §12          (Mont-arithmetic-in-posts antipattern)
  5. proofs/agent-status/dashboard.md         (state table)
  6. MLKEM_STATUS.md                           (phase plan + USER tasks)

Verify environment with:
  cd /Users/karthik/libcrux-trait-opacify
  git status              # should be clean on trait-opacify
  git log --oneline trait-opacify -5
  pgrep -f fstar.exe      # should be 0 ml-kem-related (only fstar-mcp at 3001)

Report ONE PARAGRAPH state summary on entry, then ask the user
which lane to attack.  Recommend lane (a) Step 4 if no preference
— it's the natural next step in the plan and most directly
demonstrates the value of the verified Bridges.fst lemmas.
```
