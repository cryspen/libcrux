# USER-8 agent prompt — trait `from_bytes` / `to_bytes` post wiring

USER-8 was filed in MLKEM_STATUS as Phase 1 Cluster 2 deferred when
the dual-discharge (portable + AVX2) was estimated at >90 min total.
With Wave-A's main session done and B6 closed, this is now agent-tractable.

**Worktree:** `/Users/karthik/libcrux-trait-opacify/`
(below-trait; trait edits canonical here, Wave-B/C cherry-pick later)
**Branch:** `agent/user-8` off `trait-opacify` HEAD.

Paste the block below into a fresh Claude Code session opened in
`/Users/karthik/libcrux-trait-opacify/libcrux-ml-kem`.

---

```
You are the USER-8 lane agent.  Goal: strengthen the trait
`Operations::from_bytes` and `Operations::to_bytes` posts to cite
the existing helpers `from_le_bytes_post_N` / `to_le_bytes_post_N`
(both defined in `src/vector/traits.rs:234-246`), and discharge the
strengthened posts on both portable and AVX2 backends.

═══════════════════════════════════════════════════════════════════
CURRENT STATE
═══════════════════════════════════════════════════════════════════

  - Trait declarations: `src/vector/traits.rs:1253-1260` carry
    `// TODO(C4)` markers; method declarations have NO post.
  - Helpers: `from_le_bytes_post_N` (line 234) / `to_le_bytes_post_N`
    (line 241) are defined in the `spec` submodule, citing
    `BitVecEq.int_t_array_bitwise_eq` at depth 8 / 16.
  - Trait wrapper posts: `from_bytes_post` (line 1204) / `to_bytes_post`
    (line 1212) are also defined.  They do the slice-length coercion
    + delegate to `from_le_bytes_post_N` / `to_le_bytes_post_N`.
  - Portable impl:
    `src/vector/portable/vector_type.rs:42-62` — raw bit-shift body:
    `elements[i] = (array[2*i+1].as_i16()) << 8 | array[2*i].as_i16();`
    No post discharge yet; needs `from_bytes_lemma` mirroring
    `serialize_4_lemma`'s BitVec pattern.
  - AVX2 impl: `src/vector/avx2.rs:53-70` — `to_bytes` is currently
    `lax`.  `from_bytes` is unannotated.  Strengthening forces
    discharge of an `mm256_loadu_si256` / `mm256_storeu_si256`
    SIMD↔BitVec bridge.  This is the heavy half of USER-8.

═══════════════════════════════════════════════════════════════════
SCOPE — sequential subtasks
═══════════════════════════════════════════════════════════════════

S1. Wire trait posts (no discharge yet):
    - Edit `src/vector/traits.rs:1253-1260` to add post conjuncts
      `${spec::from_bytes_post}` / `${spec::to_bytes_post}`.
    - Run `python3 hax.py extract` (~15s).
    - Run `make check/Libcrux_ml_kem.Vector.Traits.Spec.fst` to
      verify the trait spec extracts cleanly.

S2. Portable discharge (60 min target):
    - Add `from_bytes_lemma` to `src/vector/portable/vector_type.rs`
      mirroring `serialize_4_lemma` (in src/vector/portable/serialize.rs)
      via `Tactics.GetBit.prove_bit_vector_equality' ()`.  16 lanes
      × 16 bits = 256-bit equality, structurally same as the
      serialize_5/11 lemmas (commit `a51ddbfc3`).
    - Same for `to_bytes_lemma`.
    - Body proofs of `from_bytes`/`to_bytes` invoke these lemmas to
      discharge the strengthened posts.
    - Verify: `make check/Libcrux_ml_kem.Vector.Portable.Vector_type.fst`,
      `make check/Libcrux_ml_kem.Vector.Portable.fst`.
    - 20-min cap per lemma per R6; if `from_bytes_lemma` doesn't
      close, factor the BitVec equality into per-byte sub-lemmas or
      file a USER-N for the SIMD-side primitive.

S3. AVX2 discharge (90 min target):
    - Drop `lax` on AVX2 `to_bytes` (line 53-70).
    - Add SIMD↔BitVec bridge admit in
      `libcrux-intrinsics/proofs/fstar/extraction/Libcrux_intrinsics.Avx2_extract.fst`
      (or .fsti) — analogous to the existing `bit_vec_of_int_t_array`
      decomposition pattern that B3 uses.  If the bridge is non-
      trivial (>2 hr to write), file as a focused USER-N (e.g.
      "USER-13 — AVX2 mm256_loadu/storeu BitVec bridge") and STOP.
    - Wrapper body invokes the bridge to discharge `to_bytes_post`.
    - Verify: `make check/Libcrux_ml_kem.Vector.Avx2.fst`.
    - If S3 stalls, S1+S2 can still land — partial USER-8 closure
      (portable side only) is acceptable provided the trait post is
      satisfied by AVX2 via a `panic_free` fallback (file as USER-N).

═══════════════════════════════════════════════════════════════════
RESUME PROTOCOL — read these in order
═══════════════════════════════════════════════════════════════════

  1. proofs/agent-status/lane-split-protocol.md (worktrees, SD1-3)
  2. proofs/agent-status/inter-wave-protocol.md (Wave-A/B/C handoff)
  3. proofs/agent-status/edit-check-loop-comparison.md
  4. MLKEM_STATUS.md USER-8 entry (current state details)
  5. proofs/agent-status/agent-trackA.md most recent entries
     (B6 closure detail, B5 spike finding, Wave-B setup notes)
  6. src/vector/portable/serialize.rs:serialize_4_lemma (template)
  7. src/vector/traits.rs:234-246 (helper post definitions)

═══════════════════════════════════════════════════════════════════
HARD RULES
═══════════════════════════════════════════════════════════════════

R1  Branch `agent/user-8` off `trait-opacify`.  Merge back via FF.
R2  Maintain SD1 (mod-q opacity) / SD2 (Spec.Utils.forall<N>) / SD3
    per lane-split-protocol.md.
R3  No new admits in lane bodies — *unless* small scoped
    arithmetic/bitvec property to a NEW USER-N filing.  No broad
    `panic_free` / `lax` fallbacks without a tracked USER-N.
R4  ulimit -v 8388608, F* rlimit ≤ 800.
R5  Inner loop: plain `make check/<Mod>.fst`.
R6  20-min cap per function/lemma; step-back audit at the cap.
R7  Don't bulk-delete `.checked` files.
R8  fstar-mcp unreliable; use plain `make`.
R9  Trait edit IS allowed for this lane (S1) — that's the whole point.
    But ONLY add post conjuncts; do NOT change pre conditions or
    method signatures.
R10 Don't touch:
    - src/vector/portable/serialize.rs (independent agent — see
      proofs/agent-status/serialize-prompt.md)
    - src/vector/portable/compress.rs, src/vector/avx2.rs op_serialize_*
      / op_deserialize_* (Wave-A continuation agent — agent/lane-B1,
      agent/lane-B3)
    - src/serialize.rs / src/sampling.rs / src/polynomial.rs /
      src/invert_ntt.rs / src/matrix.rs / src/ind_cpa.rs /
      src/ind_cca.rs (Wave-B/C surface)
R11 hax extract is safe in this worktree but `pgrep -fl "hax\|cargo hax"`
    first.  If the Wave-A continuation agent or serialize agent is
    extracting, wait.
R12 Track admit-count delta per subtask.

═══════════════════════════════════════════════════════════════════
DELIVERABLE
═══════════════════════════════════════════════════════════════════

  - All landed work merged on trait-opacify (FF preferred).
  - Updated MLKEM_STATUS.md USER-8 status (✅ closed / 🔶 partial /
    ⏸ deferred + new USER-N filings).
  - Updated proofs/agent-status/agent-trackA.md with USER-8 session
    log (S1/S2/S3 outcomes, Z3 timings if walls hit, any new USER-N
    filings with reproducer detail).
  - Final admit-count delta vs trait-opacify HEAD baseline at
    session start.
  - One-paragraph end-of-session summary.

REPORT a one-paragraph summary at the end: subtasks closed,
subtasks deferred, net admit delta, any new USER-N filings.
```
