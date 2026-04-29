# Serialize agent prompt — Cluster 3 lemma scale-up + USER-9 path

Independent agent.  Operates concurrently with Wave-A in the SAME
worktree (`/Users/karthik/libcrux-trait-opacify/`) but on a
**file-disjoint surface**: only
`libcrux-ml-kem/src/vector/portable/serialize.rs` and the F* lemmas
extracted from it.  Does NOT touch any Wave-A B-lane surface
(`src/vector/portable.rs`, `src/vector/avx2.rs`,
`Hacspec_ml_kem.Commute.Chunk.fst`).

Paste the block below into a fresh Claude Code session opened in
`/Users/karthik/libcrux-trait-opacify/libcrux-ml-kem`.

---

```
You are the serialize agent.  Your job is to scale up the four BitVec
lemmas committed to `src/vector/portable/serialize.rs` at
`a51ddbfc3` (Phase 1 Cluster 3 partial), confirm they verify cleanly
with `VERIFY_SLOW_MODULES=yes`, and then propose the path forward for
USER-9 (trait `serialize_5/11` / `deserialize_5/11` post wire-up).

═══════════════════════════════════════════════════════════════════
CONTEXT — what's already there
═══════════════════════════════════════════════════════════════════

Commit `a51ddbfc3` added 4 lemmas to
`src/vector/portable/serialize.rs`, mirroring the existing
`serialize_4_lemma` / `serialize_10_lemma` / `deserialize_4_lemma` /
`deserialize_10_lemma` patterns:

  - `serialize_5_bit_vec_lemma` + `serialize_5_lemma` (80 bits)
  - `serialize_11_bit_vec_lemma` + `serialize_11_lemma` (176 bits)
  - `deserialize_5_bit_vec_lemma` + `_bounded` + `deserialize_5_lemma` (80 bits)
  - `deserialize_11_bit_vec_lemma` + `_bounded` + `deserialize_11_lemma` (176 bits)

All discharged via `Tactics.GetBit.prove_bit_vector_equality' ()`,
under `#push-options "--compat_pre_core 2 --z3rlimit 300 --z3refresh"`
for the bit_vec lemmas and `--z3rlimit 300` for the wrapper lemmas.

The 80-bit `serialize_5_bit_vec_lemma` SPIKE closed in **744 ms cold,
no hints** when run alone — that's why the lemmas were committed.
But the full-file verification of all 4 lemmas (with
`VERIFY_SLOW_MODULES=yes`) was started in the parent session and
**hung for 50+ min with no fstar.exe child**, suggesting either a
make-jobserver deadlock from concurrent invocations or that the
176-bit lemmas (`serialize_11`, `deserialize_11`) wall at rlimit 300.

The file `proofs/fstar/extraction/Libcrux_ml_kem.Vector.Portable.Serialize.fst`
is in `SLOW_MODULES` (auto-admitted by default in `Makefile`).  Use
`VERIFY_SLOW_MODULES=yes` to actually verify the lemma bodies.

═══════════════════════════════════════════════════════════════════
SCOPE — file-disjoint with Wave-A
═══════════════════════════════════════════════════════════════════

You may touch ONLY:
  - `libcrux-ml-kem/src/vector/portable/serialize.rs`
  - the four lemmas you're verifying (their `hax_lib::fstar::after`
    push_options blocks).

You may NOT touch:
  - `src/vector/portable.rs` (Wave-A B1, B5)
  - `src/vector/avx2.rs` (Wave-A B3, B5)
  - `Hacspec_ml_kem.Commute.Chunk.fst` (Wave-A B6 + later waves)
  - `Hacspec_ml_kem.Commute.Bridges.fst`
  - `src/vector/traits.rs` (FROZEN since Phase 1)

If you need a `make` lock, prefer:
  - `make check/Libcrux_ml_kem.Vector.Portable.Serialize.fst`
    with `VERIFY_SLOW_MODULES=yes`.
  - Single make invocation at a time.  If a previous make is still
    running, wait or coordinate with the user — don't kick off a
    second concurrent make on the same target.

═══════════════════════════════════════════════════════════════════
OBJECTIVE — scale the proof
═══════════════════════════════════════════════════════════════════

PRIMARY: get `VERIFY_SLOW_MODULES=yes
make check/Libcrux_ml_kem.Vector.Portable.Serialize.fst` to exit 0
with all four new lemmas discharged for real (not via `--admit_smt_queries`).

SCALING STRATEGIES — apply in order, escalating only if needed:

  1. **Baseline check.**  First confirm the file builds (with
     SLOW admits) at all, to rule out a syntax error from the
     hax extraction.  Run plain
     `make check/Libcrux_ml_kem.Vector.Portable.Serialize.fst`
     (no SLOW flag) — should exit 0 in <30 s.

  2. **Tactic-only verification.**  Run with
     `VERIFY_SLOW_MODULES=yes`.  If all 4 lemmas close, you're done.
     Time-box: **15 minutes wall**.  If still running past 15 min
     with no completion signal, see strategy 3.

  3. **Per-lemma isolation.**  If the file-level VERIFY_SLOW run is
     slow or stuck, isolate each lemma by adding
     `#[hax_lib::fstar::verification_status(panic_free)]`
     **TEMPORARILY** to all OTHER lemmas in the file (including the
     existing serialize_4/serialize_10/deserialize_4/deserialize_10
     ones), so only one of your new lemmas verifies per run.  This
     identifies whether the wall is on `serialize_5`, `serialize_11`,
     `deserialize_5`, or `deserialize_11`.  REVERT the panic_free
     before committing.  (R3 says no new admits in committed code,
     but this is local debugging — do NOT commit.)

  4. **rlimit escalation.**  If a specific lemma walls under
     `prove_bit_vector_equality' ()` at rlimit 300, bump the
     `#push-options` rlimit to 600 → 800.  Cap at 800 per the sprint
     hard rule R4.  Track whether the tactic itself is slow vs Z3.

  5. **--z3refresh on the wrapper lemma.**  The bit_vec lemmas use
     `--z3refresh`; the wrapper lemmas (`serialize_5_lemma` etc.) do
     not.  If a wrapper wall happens, add `--z3refresh` to its
     push_options.

  6. **Tactic fallback.**  If `prove_bit_vector_equality' ()`
     doesn't generalize to 176-bit equalities (`serialize_11`,
     `deserialize_11`), try splitting the lemma into 2 × 88-bit
     halves — pre-state the equation per chunk, then concatenate.
     `bit_vec_of_int_t_array` decomposes by length; you can split
     the input slice in half and prove each half separately.
     This mirrors how `serialize_10` handles 160-bit equalities
     (it tactic-discharges as a single 160-bit; only fall back to
     the split if the single-shot approach walls).

  7. **Per-`<width>_int` integer lemma.**  If the bit-vector tactic
     genuinely fails to handle 5-bit / 11-bit packing, fall back to
     proving an integer-level lemma about `serialize_5_int` /
     `serialize_11_int` (the inner 8-element-batch helper) using
     `Math.Lemmas` / `FStar.UInt` integer reasoning, then chain two
     batches.  This is the same approach the `compress` /
     `decompress` chain uses where the bit-vector tactic doesn't
     reach.  Document the per-batch lemma signatures clearly so
     future maintenance is mechanical.

═══════════════════════════════════════════════════════════════════
TIME BUDGET
═══════════════════════════════════════════════════════════════════

Apply the standard 20-minute-per-lemma cap from the wave prompts.
If a single lemma is not closing after 20 min of strategy iteration:

  (a) Audit the property — counter-example check on concrete
      bit-pattern values.  serialize_5/11 are well-known to be
      bijective (the int-level helpers were validated in C4f); if
      your proof attempt isn't closing, it's almost certainly a
      proof-strategy issue, not a property bug.
  (b) Audit "is this needed?" — the answer is YES (USER-9 needs
      these to wire trait posts), but the format may be flexible.
      Maybe a weaker post on the lemma (e.g., `Seq.length result == 10`
      only, no BitVecEq) would suffice for the TRAIT post, even if
      it doesn't suffice for above-trait Serialize.fst migration.
  (c) Default to admitting + USER-9-extension at 20 min.  File a
      detailed note: which lemma walled, at what rlimit, with which
      strategy attempts, what counter-example values were checked.
      USER-9 absorbs the residual.

═══════════════════════════════════════════════════════════════════
USER-9 PATH FORWARD — what to do AFTER lemmas verify
═══════════════════════════════════════════════════════════════════

Once all 4 portable lemmas verify cleanly with VERIFY_SLOW_MODULES=yes,
**stop and report**.  Do NOT touch the trait declarations
(`src/vector/traits.rs:1320-1342`) or the AVX2 wrappers
(`src/vector/avx2.rs:996-1035`).  Trait wire-up is gated on the
AVX2 SIMD↔BitVec bridge, which is OUT OF SCOPE for this agent.

Your USER-9 forward-path report should answer:

  1. **Did all 4 portable lemmas verify cleanly?**  Yes / no per
     lemma; if no, which strategy walls.
  2. **Time per lemma** (cold, no hints): records the cost so
     future re-verification has a baseline.
  3. **Recommended next step for USER-9.**  Three options:
     - **(a) Defer indefinitely**: if the AVX2 SIMD↔BitVec bridge
       is too heavy, document and leave USER-9 as a long-term task.
     - **(b) Spike the AVX2 bridge**: list the 4-6 admitted bridge
       lemmas needed (mirror of the existing
       `op_serialize_4_post_bridge` etc. in `src/vector/avx2.rs`),
       estimate effort.  Recommend whether to take it on as a
       dedicated USER-9 lane or fold into Wave-B's A1
       (Phase 7c serialize migration), since A1 already touches
       Serialize.fst.
     - **(c) Strict portable-only path**: explore whether the
       trait could be SPLIT into `Operations` (current) and
       `OperationsSerial5` (NEW, with strong serialize_5/11 posts)
       so the portable backend can implement both but the AVX2
       backend only implements `Operations`.  Above-trait code
       that needs the strong posts uses the new trait; rest stays
       on the current trait.  This sidesteps the AVX2 bridge
       entirely but is a structural change worth user discussion.
  4. **Net admit count delta** for this agent's session.

═══════════════════════════════════════════════════════════════════
HARD RULES
═══════════════════════════════════════════════════════════════════

R1 File-disjoint with Wave-A.  Do NOT touch their surface.
R2 No commits unless all 4 lemmas verify.  If only some verify,
   document and ask the user before committing partial work.
R3 No `panic_free` / `--admit_smt_queries` / `lax` in committed
   code.  Local-only for debugging; revert before committing.
R4 ulimit -v 8388608, F* rlimit ≤ 800.
R5 Inner loop: `make check/...` from
   `proofs/fstar/extraction/`.  ALWAYS wait for one make to finish
   before starting another against the same target.
R6 If the make hangs >15 min with no fstar.exe child running, ASK
   the user before killing — there may be cross-session contention.
R7 Don't bulk-delete `.checked` files.  Surgical `rm` of the
   target's `.checked` only when iterating; prefer
   `touch <file>.fst` to invalidate.
R8 Don't touch `src/vector/traits.rs`.  Trait FROZEN.
R9 Don't touch any module owned by Wave-A or Wave-B per the
   inter-wave protocol.

═══════════════════════════════════════════════════════════════════
DELIVERABLE
═══════════════════════════════════════════════════════════════════

  • If all 4 lemmas verify: single commit on `agent/serialize-scaleup`
    branch (or `trait-opacify` directly if the user prefers, since
    this is a pure improvement — but prefer a separate branch and
    let the user merge).  Commit message documents:
      - Which strategies were tried.
      - Final rlimit / push-options per lemma.
      - Time per lemma.
      - Status of USER-9 forward-path recommendation.
  • If some lemmas don't verify: NO commit; report findings.
  • Status snapshot in `proofs/agent-status/serialize-status.md`
    (NEW file): time per lemma, strategy used, residual admits if
    any, USER-9 path recommendation.

REPORT one paragraph end-of-session summary.
```
