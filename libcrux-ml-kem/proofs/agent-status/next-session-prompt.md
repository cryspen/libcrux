# Next-session resume prompt — Phase 7a Step 5 spike (drive-to-the-top)

Paste the block below into a fresh Claude Code session opened in
`/Users/karthik/libcrux-trait-opacify/libcrux-ml-kem`.

---

```
You are continuing the multi-agent F* verification effort on
libcrux-ml-kem trait-opacify branch.

═══════════════════════════════════════════════════════════════════
SPIKE GOAL — drive `invert_ntt_montgomery`'s strengthened post end-to-end
═══════════════════════════════════════════════════════════════════

**Why a spike, not bottom-up.**  We have layers 1, 3 strengthened
(Steps 4 layers 1+3) and step_reduce strengthened (Step 3.1).  Layer 2
(Step 4 layer 2) Z3-walled and is admitted; layer 4_plus's polynomial-
level strengthening (Step 3.3) needs new spec helpers and was deferred.
Before sinking time into discharging those, we want to know: does the
strengthened `invert_ntt_montgomery` post actually compose with what
the consumers in `matrix.rs` / `polynomial.rs` need?

This spike admits the missing pieces, drives the chain to the top, and
**validates the spec direction by rewiring at least one consumer post**
(probably `subtract_reduce` or `add_message_error_reduce`).  If the
shape is right, future bottom-up work has a definite target.  If the
shape is wrong, we discover it now — before paying the discharge cost.

═══════════════════════════════════════════════════════════════════
WHAT'S COMMITTED ENTERING THIS SESSION
═══════════════════════════════════════════════════════════════════

  Step 1:    layer-1 inverse hacspec bridge                     ✅
  Step 2:    layer 2 + layer 3 inverse bridges                  ✅
  Step 3.1:  strengthened `inv_ntt_layer_int_vec_step_reduce` post
                with per-lane FE equations                       ✅
  Step 3.2:  chunk-pair bridge
                `lemma_inv_ntt_layer_int_vec_step_reduce_to_hacspec` ✅
  Step 4:    layer 1 + layer 3 strengthening (Option B)          ✅
  Step 7.1 + closed-form lane lemma                              ✅
  Step 9:    scaling-chain doc comments                          ✅

CURRENTLY ADMITTED (TEMP, this session will NOT discharge — it will
ADD MORE in the same spirit so the spike runs):
  * `invert_ntt_at_layer_4_plus` (4 calls in `invert_ntt_montgomery`)
    — admitted by `--admit_smt_queries true` because Step 3.1's
    strengthened step_reduce post regresses its bounds proof.

WILL ALSO ADMIT in this spike:
  * `invert_ntt_at_layer_2` (Step 4 layer 2, Z3-walled previously).
  * Possibly `invert_ntt_montgomery` BODY (just the bound chain
    glue) if the strengthened post inflates Q-count.

═══════════════════════════════════════════════════════════════════
SPIKE PLAN — drive in this order, stop and report at any 60-min cap
═══════════════════════════════════════════════════════════════════

(α) **Read the consumer landscape** [~15 min].
    - `src/matrix.rs:135-225` — 3 callers of `invert_ntt_montgomery`.
    - `src/polynomial.rs:340-590` — `subtract_reduce`,
      `add_message_error_reduce`, `add_error_reduce`.  These do the
      fused `mont_mul(b, 1441) ≡ b · 1/128` finalize.
    - Question to answer: what polynomial-level claim does
      `subtract_reduce`'s post (or one of the others) want to be able
      to make?  Sketch it on paper before writing F*.

    The natural shape of `invert_ntt_montgomery`'s strengthened post:
    ```
    mont_to_spec_poly_256 (re_future) ==
      <7-layer-GS-chain> (mont_to_spec_poly_256 re_init)
    ```
    where `<7-layer-GS-chain>` is the COMPOSITION of layer-7 down to
    layer-1 inverse butterflies (no `· 128⁻¹` finalize — that lives
    in the consumer).  The consumer gets:
    ```
    result_lift == myself_lift - (1/128) * inv_butterflies_chain(b_lift)
    ```

(β) **Add poly-level lift + zetas helpers** [~30 min, new file].
    File: `specs/ml-kem/proofs/fstar/commute/Hacspec_ml_kem.Commute.Chunk.fst`
    (NOT a new file — this stays alongside existing helpers).

    (β1) `mont_to_spec_poly_256` — flatten
         `re : t_PolynomialRingElement vV`
         (with `re.coefficients : t_Array vV 16`) into
         `t_Array t_FieldElement 256`:
         ```
         createi 256 (fun k -> mont_i16_to_spec_fe
           (Seq.index (T.f_repr (re.coefficients.[k / 16])) (k % 16)))
         ```

    (β2) Three new zetas-N-inverse helpers analogous to `zetas_1`:
         - `zetas_8_inv` (layer 4: 8 zetas)
         - `zetas_4_inv` (layer 5: 4 zetas)
         - `zetas_2_inv` (layer 6: 2 zetas)
         (Layer 7: reuse existing `zetas_1`.)
         Each with `zs[r] = mont_i16_to_spec_fe (zeta(2*groups - 1 - r))`.

    (β3) (Optional, if time) per-lane unfold helpers analogous to
         `lemma_ntt_inverse_layer_n_16_2_lane`, but for length 256 and
         step ∈ {16, 32, 64, 128}.

(γ) **Add layer 4_plus + layer 2 strengthened posts (admitted body)**
    [~30 min, in `src/invert_ntt.rs`].

    Strengthen `invert_ntt_at_layer_4_plus`'s post to cite
    `IN.ntt_inverse_layer_n 256 (mont_to_spec_poly_256 re) step zs`
    where `step = 2^layer`, `zs = zetas_<groups>_inv (zeta(*zeta_i_init - 1)) ...`.
    Body: keep the existing `--admit_smt_queries true`.

    Strengthen `invert_ntt_at_layer_2`'s post analogously to layers 1
    and 3 (chunk-level), citing `IN.ntt_inverse_layer_n 16 ... 4 (zetas_2 ...)`.
    Body: also admit (this is the Z3-walled one; admit body to unblock).

(δ) **Strengthen `invert_ntt_montgomery`'s post** [~15 min].
    Chain the 7 layer citations into a polynomial-level claim.  This
    post is what the consumer sees.  Body proof: should follow from
    the 7 layer posts via simple sequential substitution; rlimit 200
    likely enough.  If not, admit body too — the SPIKE is about
    validating shape, not proving.

(ε) **Rewire one consumer** [~30 min].
    Pick `subtract_reduce` (smallest, cleanest finalize).  Strengthen
    its post to cite the polynomial-level identity:
    ```
    mont_to_spec_poly_256 result ==
      mont_to_spec_poly_256 myself - (1/128) * <inv_butterflies_chain>(mont_to_spec_poly_256 b)
    ```
    Body proof can be admitted for the spike — what we're testing is
    whether the post **types** at all, and whether the consumer
    callers in `matrix.rs` accept it without unification errors.

    Verify: `python3 hax.py extract && make check/Libcrux_ml_kem.Polynomial.fst`
    (then `Matrix.fst` if Polynomial passes).

═══════════════════════════════════════════════════════════════════
DECISION CRITERIA — what counts as SUCCESS for this spike
═══════════════════════════════════════════════════════════════════

  ✅ **Spec shape validated** — `invert_ntt_montgomery`'s strengthened
     post is well-typed AND `subtract_reduce`'s strengthened post
     uses it without F* unification errors.  `Polynomial.fst` and
     `Matrix.fst` extract + verify (with admits) clean.

  ⚠️ **Shape mismatch** — F* type-checks but the consumer's claim
     can't actually use the antecedent.  Document the exact gap and
     redesign.

  ❌ **Plumbing broken** — extraction or verification fails on
     trivial type / module / dep issues.  Fix and continue.

═══════════════════════════════════════════════════════════════════
HARD RULES
═══════════════════════════════════════════════════════════════════

  R1 SPIKE EXCEPTION: temp admits ARE allowed in this session for
     bodies whose POSTS are being validated.  Mark every admit with
     `// SPIKE TEMP — discharge after Step 5 spike` so they're
     trivially greppable.  EVERY admit MUST be explicitly listed in
     a "spike admits" section of agent-trackA.md before commit.
  R2 NO new admits in `Hacspec_ml_kem.Commute.*` — those are spec
     helpers; they must verify cleanly.
  R5 No body assumes (axioms).  Use admits with reason, not assumes.
  R6 ulimit -v 8388608, F* rlimit ≤ 800.
  R7 fstar-mcp inner loop, make end-of-chunk.
  R8 Eager commit log to agent-trackA.md.
  R3 Hard cap 90 min for this spike.  If shape mismatch found,
     STOP, document the gap, and hand off to a redesign session.

═══════════════════════════════════════════════════════════════════
RESUME PROTOCOL — load durable state in this order
═══════════════════════════════════════════════════════════════════

  1. proofs/agent-status/agent-trackA.md   (Step 3.1+3.2 + the
                                            layer 4_plus admit story)
  2. /Users/karthik/.claude/plans/replicated-beaming-pnueli.md
                                            (THE PLAN, esp. Step 5)
  3. proofs/agent-status/fstar-perf-top20.md (perf data)
  4. MLKEM_STATUS.md                         (phase tracker)
  5. src/invert_ntt.rs:498-559               (`invert_ntt_montgomery`
                                              source — chain of 7 calls)
  6. src/matrix.rs:130-225                   (3 callers of inv_ntt_mon)
  7. src/polynomial.rs:340-590               (3 INTT-track reduce fns)
  8. specs/ml-kem/proofs/fstar/commute/Hacspec_ml_kem.Commute.Chunk.fst
                                              (where new helpers go)
  9. specs/ml-kem/proofs/fstar/commute/Hacspec_ml_kem.Commute.Bridges.fst
                                              (existing bridges + Step 3.2)

═══════════════════════════════════════════════════════════════════
ENVIRONMENT VERIFY
═══════════════════════════════════════════════════════════════════

  cd /Users/karthik/libcrux-trait-opacify
  git status              # clean on trait-opacify
  git log --oneline trait-opacify -5  # latest is Step 3.1+3.2 commit
  pgrep -f fstar.exe      # ml-kem fstar-mcp at port 3001
                          # (recreate session as needed)

REPORT one paragraph spike entry summary, then dive into (α) — the
consumer landscape read.  Do NOT start writing F* until you've
sketched the polynomial-level identity on paper (in your message to
the user).  This is the most important part of the spike.
```

---

## Why this prompt is structured this way

- **Spike framing is foreground** — admits are allowed precisely
  because we're validating spec shape, not proving correctness.
- **Consumer landscape read FIRST** — sketching the identity before
  writing F* prevents the trap of "I built it but the caller can't
  use it".
- **Decision criteria explicit** — there's a defined ✅/⚠️/❌ outcome
  so the spike can be wrapped cleanly even on shape mismatch.
- **Step 3.3's deferred sub-pieces (β1/β2/β3) are reused** here as
  the "natural" infrastructure unit.  Doing them in a spike is
  cheaper than the full Step 3.3 because the loop-invariant work in
  3.3(C) is replaced by an admit.
