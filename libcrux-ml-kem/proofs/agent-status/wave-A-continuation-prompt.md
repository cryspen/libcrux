# Wave-A continuation prompt — close deferred lanes (B1, B3) — agent-tractable subset

Wave-A's first session (2026-04-29) landed B6 only.  Of the 5
deferred lanes, the user triaged 3 to USER-N (NTT-related Z3 walls
best handled by user with smtprofiling): **B2 → USER-12**, **B5 → USER-11**,
**B4 → USER-4** (already filed, descoped).  This continuation
prompt covers the 2 remaining agent-tractable lanes (B1, B3).

USER-8 and USER-9 are also agent-tractable (separate lanes, not
covered by this prompt — USER-9 is already in flight by another
agent per `serialize-prompt.md`; USER-8 is open for any agent).

Wave-B has launched in `~/libcrux-ml-kem-above-trait/`; this
continuation runs in parallel in the original below-trait worktree.

**Worktree:** `/Users/karthik/libcrux-trait-opacify/`
**Branch family:** `agent/lane-B<N>` per lane; merge to `trait-opacify`.
**Current trait-opacify tip:** `fa31480cd` (Wave-A handoff).
**Wave-A first session work:** B6 closed at `2f96abe99`.

Paste the block below into a fresh Claude Code session opened in
`/Users/karthik/libcrux-trait-opacify/libcrux-ml-kem`.

---

```
You are the Wave-A continuation coordinator.  The first Wave-A
session landed B6 (USER-1 / A8 4-case Barrett enumeration) at
commit `2f96abe99` and committed the handoff at `fa31480cd`.
Wave-B has launched in `~/libcrux-ml-kem-above-trait/`; it operates
on a separate clone with its own .fstar-cache and refetches
trait-opacify periodically.  This session runs in parallel in the
original below-trait worktree to close admit cleanup lanes that did
not fit in the first session.

═══════════════════════════════════════════════════════════════════
SCOPE — 2 agent-tractable deferred lanes
═══════════════════════════════════════════════════════════════════

  Lane | Files | Effort | Risk | Status
  -----|-------|--------|------|--------
  B1   | src/vector/portable/compress.rs (4 chunk wrappers + 1 primitive) | 2 sess | medium | not attempted
  B3   | src/vector/avx2.rs (7 admitted bridge lemmas), libcrux-intrinsics/...Avx2_extract.fst | 2 sess | low-med | not attempted

  Recommended order:  B1 → B3 (B1 has clearer cost-reward; B3 needs
  a new decomposition lemma in Avx2_extract.fsti that's more invasive).

  USER-LANE (excluded from this prompt; do NOT touch):
    B5  → USER-11 (op_ntt_multiply panic_free; Z3 wall documented)
    B2  → USER-12 (portable NTT layer 1 panic_free; 4-zeta wall)
    B4  → USER-4  (AVX2 NTT layer 1/2 bridges; Z3 wall, descoped)

  RELATED AGENT-LANE TASKS (separate prompts, not in scope here):
    USER-8 — trait from_bytes/to_bytes (separate prompt or this session
             can pick up after B1/B3).
    USER-9 — serialize_5/11 trait wire-up (in flight by independent
             agent per serialize-prompt.md).

═══════════════════════════════════════════════════════════════════
B5 FINDING (from 2026-04-29 spike) — REFERENCE ONLY (B5 → USER-11)
═══════════════════════════════════════════════════════════════════

B5 was spiked + reverted; it is now USER-11.  This section is kept
for cross-reference (especially the per-conjunct decomposition
strategy, which may be applicable if B1's chunk wrappers exhibit
similar Z3 saturation under split_queries).

The first Wave-A session spiked B5 with the structurally-correct body
proof and reverted at the 20-min cap.  The body proof shape that was
validated:

  reveal_opaque is_i16b_array_opaque 3328
  reveal_opaque ntt_multiply_branch_post
  let result = ntt_multiply(lhs, rhs, zeta0..zeta3)
  // forall8 ntt_multiply_binomials_post in scope from primitive's post
  let nzeta_i = mk_i16 0 -! zeta_i  for i ∈ {0..3}
  // 8 calls to lemma_base_case_mult_pair_commute (lhs rhs result z k)
  //   for (z, k) ∈ {(zeta0, 0), (nzeta0, 1), (zeta1, 2), (nzeta1, 3),
  //                 (zeta2, 4), (nzeta2, 5), (zeta3, 6), (nzeta3, 7)}
  let p_branch = fun (b: nat{b<4}) -> ntt_multiply_branch_post b ...
  assert (p_branch 0); assert (p_branch 1);
  assert (p_branch 2); assert (p_branch 3);
  assert (Spec.Utils.forall4 p_branch)

OUTCOME at rlimit 400 + --split_queries always:

  Q28 (assert p_branch 0 — sub-conjunct 1): 31s, used 126/400
  Q30 (assert p_branch 0 — sub-conjunct 2): 51s, used 192/400
  Q32 (assert p_branch 0 — sub-conjunct 3): 84s, used 279/400
  Q34 (assert p_branch 0 — sub-conjunct 4): FAILED canceled at 400/400 in 104s
  → "Error 19: Assertion failed" at line `assert (p_branch 0)`

The rlimit usage doubled per sub-conjunct (126 → 192 → 279 → 400+).
Z3 is accumulating context across the 8 lemma_base_case_mult_pair_commute
facts and the 4 conjuncts of branch_post.

WHY IT TIMED OUT, ROOT CAUSE HYPOTHESIS:
- branch_post's opaque body is a 4-conjunct claim (one per lane) with
  nested `if b = 0 then zeta0 else ...` ladders for `zp` (the chosen
  zeta) and `Spec.Utils.neg_i16 zp`.  Even though `b = 0` is concrete
  in `assert (p_branch 0)`, Z3 still propagates the if-ladder context
  through every conjunct.
- Combined with 8 binomial facts in scope (each a 2-conjunct fact),
  Z3's quantifier-instantiation context grows quadratically per
  sub-conjunct, eventually saturating rlimit 400.

PATH FORWARD (3 strategies, ordered by likelihood of success):

(1) Per-conjunct decomposition (RECOMMENDED).  Replace
    `assert (p_branch 0)` with 4 explicit lane-FE assertions:
        assert (mont_i16_to_spec_fe result[0] == ...);
        assert (mont_i16_to_spec_fe result[1] == ...);
        assert (mont_i16_to_spec_fe result[2] == ...);
        assert (mont_i16_to_spec_fe result[3] == ...);
        assert (p_branch 0)
    Each lane assertion has only ONE FE equation in scope, so Z3
    matches it directly to the relevant pair_commute output.  The
    final `assert (p_branch 0)` becomes a structural/conjunction
    fold which closes in <1s.

    Repeat for branches 1, 2, 3 — total +48 lines of body proof.

(2) Per-branch helper lemma (PARALLEL TO LAYER-2 FIX in `b7b49c358`).
    Define 4 private F* lemmas in
    `Hacspec_ml_kem.Commute.Chunk.fst` (B5 additions section), one
    per concrete `b ∈ {0..3}`:

      private let lemma_op_ntt_multiply_branch_b
        (b: nat{b<4}) (lhs rhs result: t_Array i16 16)
        (zeta_b: i16) :
        Lemma (requires <2 binomial facts for k=2b and k=2b+1>)
              (ensures ntt_multiply_branch_post b lhs rhs ... result)

    Each helper has a literal `b`, so the if-ladder collapses
    pre-SMT.  Wrapper body invokes 4 such lemmas + forall4.  This
    is the same pattern that closed inverse layer 2 (commit
    `b7b49c358`); see `agent-trackA.md` 2026-04-28 evening entry
    for the unlock detail.

(3) rlimit bump to 800 + intermediate hand-holding asserts.  Cheaper
    than (1)/(2) but less robust; if the 4th sub-conjunct still
    times out at 800, escalation chain repeats.

═══════════════════════════════════════════════════════════════════
B1 SCOPE CLARIFICATION (from 2026-04-29 inspection)
═══════════════════════════════════════════════════════════════════

The wave-A-prompt described "5 stale `panic_free` in
`src/vector/portable.rs`" but the actual annotations are in
`src/vector/portable/compress.rs` (different file):

  Line 27:  compress_message_coefficient PRIMITIVE        — 3-case enum body proof, tractable
  Line 113: compress_ciphertext_coefficient PRIMITIVE     — Barrett exactness, **HARD MATH** (USER-N)
  Line 170: compress_1 chunk wrapper                      — chains primitive post per-lane
  Line 222: compress<D> chunk wrapper                     — depends on Barrett primitive, blocked
  Line 289: decompress_1 chunk wrapper                    — chains primitive post per-lane
  Line 347: decompress_d chunk wrapper                    — chains primitive post per-lane

B1 PRACTICAL SCOPE (after subtracting blocked work):
  - Drop panic_free on compress_message_coefficient (line 27): write
    the 3-case integer enum (`fe ∈ [0, 832] ∪ [833, 2496] ∪ [2497, 3328]`)
    body proof.  Comment at line 107-109 has the math template.
  - Drop panic_free on compress_1 chunk (line 170): mechanical, just
    chain the primitive's strengthened post forall.
  - Drop panic_free on decompress_1 chunk (line 289): same shape.
  - Drop panic_free on decompress_d chunk (line 347): same shape.

  TOTAL: 4 panic_free drops removable.  Leave compress_ciphertext_coefficient
  (line 113) admitted as USER-N "Barrett primitive exactness" — file
  it explicitly in MLKEM_STATUS.md.  compress<D> chunk wrapper
  (line 222) stays admitted because it depends on the Barrett primitive.

═══════════════════════════════════════════════════════════════════
B3 SCOPE (AVX2 serialize/deserialize bridges)
═══════════════════════════════════════════════════════════════════

7 admitted bridge lemmas in `src/vector/avx2.rs`:
  op_serialize_N_post_bridge for N ∈ {4, 10, 12} (3 lemmas)
  op_serialize_N_pre_bridge for N ∈ {4, 10, 12} (3 lemmas — one less, depending; verify)
  op_deserialize_N_post_bridge for N ∈ {1, 4, 10, 12} (4 lemmas)

Discharge via:
  - `Tactics.GetBit.prove_bit_vector_equality' ()` — same tactic that
    closed serialize_5/11_lemma in Phase 1 Cluster 3 (commit `a51ddbfc3`).
  - `bit_vec_of_int_t_array` decomposition lemma to be added in
    `libcrux-intrinsics/proofs/fstar/extraction/Libcrux_intrinsics.Avx2_extract.fst`
    (or its `.fsti`).

Pattern: each bridge connects the AVX2 primitive's BitVec lane post
(`bit_vec_of_int_t_array r 8 i == vector ((i/N)*16 + i%N)`) to the
trait's array-form post (`BitVecEq.int_t_array_bitwise_eq` at depth N).

═══════════════════════════════════════════════════════════════════
HARD RULES (carried over from wave-A-prompt)
═══════════════════════════════════════════════════════════════════

R1  Spawn lane agents in branches `agent/lane-B<N>` off `trait-opacify`.
R2  Maintain SD1 / SD2 / SD3 per lane-split-protocol.md.
R3  No new admits in lane bodies — *unless* small scoped
    arithmetic/bitvec property to USER-N.  No broad `panic_free`.
R4  ulimit -v 8388608, F* rlimit ≤ 800 (one-off ≤ 1200 only with
    smtprofiling justification).
R5  Inner loop: plain `make check/<Mod>.fst`.
R6  20-min cap per function/lemma; step-back audit (a/b/c) above
    that.  Default to (c) — admit + USER-N.
R7  Don't bulk-delete `.checked` files.
R8  fstar-mcp unreliable; use plain `make`.
R9  Trait FROZEN at `2f96abe99`.  Don't touch `src/vector/traits.rs`.
R10 Don't touch trait files; below-trait surface only.
R11 hax extract is safe in this worktree (validated 2026-04-29):
    runs in 15 s; doesn't collide with Wave-B's separate clone or
    user IDE sessions.

═══════════════════════════════════════════════════════════════════
SESSION DELIVERABLE
═══════════════════════════════════════════════════════════════════

  - All landed lanes merged on `trait-opacify` (FF preferred; rebase
    on incoming Wave-B commits as they merge).
  - Updated MLKEM_STATUS.md per-lane status.
  - Updated agent-trackA.md with continuation session log.
  - Final admit-count delta vs Wave-A's `fa31480cd` baseline.
  - One-paragraph end-of-session summary.

REPORT one paragraph.
```
