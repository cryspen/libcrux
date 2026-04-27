# Focused next-session prompt — paste into a new Claude Code session

Open a fresh Claude Code session at
`/Users/karthik/libcrux-trait-opacify/libcrux-ml-kem` and paste the
block below.  This prompt is more focused than a generic handoff —
it loads durable state, internalizes hard rules from the prior
session, and tells the new session what NOT to repeat.

---

```
You are continuing a multi-agent F* verification effort on
libcrux-ml-kem trait-opacify branch.  The previous session:

  * Landed Phase 6 (4/6 portable NTT admits proven, merged 6f41ec5bc)
  * Landed Phase 6c (4/5 AVX2 helper admits proven + 2 SIMD intrinsic
    axioms in Avx2_extract, merged 2953fbf9c)
  * HELD agent/phase-7c-serialize (B+B') — admit-driven bridge
    scaffolding, unacceptable, see held-work-Bprime-L123.md
  * HELD agent/phase-7a-polynomial (E) — admit-driven Tier-1 lemma
    scaffolding + body assumes, unacceptable, see held-work-E-Phase7a.md

trait-opacify tip: see `git log --oneline trait-opacify -5`.  Should
be at-or-after 3709dcc4e.

Resume protocol — load durable state by reading these in order, then
report ONE PARAGRAPH of state summary:

  1. libcrux-ml-kem/proofs/agent-status/handoff-2026-04-27.md
  2. libcrux-ml-kem/proofs/agent-status/dashboard.md
  3. libcrux-ml-kem/MLKEM_STATUS.md (skim Phase 7 table + USER tasks)
  4. libcrux-ml-kem/proofs/proof-style-guide.md (skim §3.4–§3.7)
  5. libcrux-ml-kem/proofs/agent-status/held-work-E-Phase7a.md
  6. libcrux-ml-kem/proofs/agent-status/held-work-Bprime-L123.md

============== HARD RULES (do not relearn) ==============

R1.  Admit-driven scaffolding is UNACCEPTABLE.  An agent run that
     adds hacspec citations but discharges them via admitted bridge
     axioms, admitted Tier-N lemmas, or body `assume`s about loop
     invariants is treated as a HELD branch, not merged.  Two such
     runs (B+B' and E) already produced ~2 hours of compute for zero
     verification content; do not commission a third.

R2.  The trait-opacify design (Phases 1–5, already landed) makes
     above-trait proofs MECHANICAL.  The trait posts in
     src/vector/traits.rs::spec deliver per-lane / per-branch FE
     equations via opaque predicates.  Tier-N commute lemmas in
     specs/ml-kem/proofs/fstar/commute/Hacspec_ml_kem.Commute.Chunk.fst
     are Classical.forall_intro compositions over EXISTING per-vector
     chunk-commute lemmas (e.g., lemma_barrett_reduce_chunk_commutes,
     lemma_add_chunk_commutes_plain).  No new arithmetic is needed.

R3.  Future agent briefs MUST require: close target #1 with a real
     proof body before any admits.  If target #1 doesn't close in
     ~30 min, ABORT and report what's missing in trait-opacity.  Do
     NOT pivot to admit scaffolding.  Provide a concrete first-target
     recipe in the brief (loop invariant + reveal_opaque + Tier-1
     lemma call).

R4.  EXISTING proofs in modules being post-strengthened (e.g.,
     Libcrux_ml_kem.Polynomial.fst's existing impl→Spec.MLKEM body
     proofs) are REFERENCE ONLY.  They use pre-trait-opacify patterns
     (manual loop-invariant strengthening with Spec.MLKEM lemma
     chains).  Do NOT mimic, extend, or chain off them.

R4a. REPLACE, don't ADD.  Old policy was "additive — keep Spec.MLKEM
     cites alongside new Hacspec_ml_kem cites for Phase 7c-7k transition".
     NEW policy (2026-04-27 evening): switch each module to hacspec
     citations IN-PLACE, dropping the Spec.MLKEM citation as you go,
     so long as you preserve any bounds precondition the Spec.MLKEM
     citation carried.  Bounds preconditions are load-bearing for
     downstream call sites; the citation form is not.  This makes
     Bridge files (B+B' approach) UNNECESSARY — there's no need to
     bridge two specs that don't need to coexist.

R5.  Body `assume`s about loop invariants are UNACCEPTABLE.  If the
     loop invariant doesn't carry the needed fact, FIRST check
     whether the trait post does (it usually does post-trait-opacify).
     Body assumes silently misuse the trait-opacity guarantees.

R6.  Resource budget: ≤4 concurrent F* processes (8 brief), 8 GB each;
     total < 32 GB on this 48 GB box.  Past OOMs crashed the system.
     `ulimit -v 8388608` + `--z3cliopt smt.memory_max_size=8000` per
     agent.  F* rlimit ≤ 800.

R7.  Default to plain `make` for verification.  fstar-mcp only when
     iterating ≥5 times on the SAME hand-written F* file content.

R8.  Agents work in isolated worktrees on dedicated branches; eager-
     commit logs to proofs/agent-status/agent-X.md on the branch.

R9.  Rust function bodies: don't touch algorithmically (loop-invariant
     strengthening should rarely be needed post-trait-opacify).
     traits.rs::spec opaque per-branch predicates: don't redesign.

============== NEXT-ACTION OPTIONS ==============

Pick ONE based on user direction and the loaded state:

(a) Real-proof specialist for Phase 7a (Polynomial 7 fns).  Use the
    held E branch's structural choices as reference.  Brief in
    held-work-E-Phase7a.md.  First target: poly_barrett_reduce.
    Hard rules R1-R5 above.

(b) Wave 3 fan-out (Phases 7b NTT layers, 7d Matrix, 7n Sampling).
    Per the parallelism plan in MLKEM_STATUS.md.  These can run
    concurrent with (a) since they touch different files.  Each
    needs a trait-opacity-aware first-target recipe in its brief.

(c) L1/L2/L3 specialist for the B+B' bit-vector chain.  Brief in
    held-work-Bprime-L123.md.  Independent of (a) and (b).

(d) Other USER-lane work (USER-1..7 in MLKEM_STATUS.md).

Default if user is silent: ask them which lane to attack, summarizing
load and noting that (a) and (c) require focused real-proof work
while (b) is more parallelizable.

Be terse in your initial state report — one paragraph or short
table.  Don't replay durable docs back to the user.
```

---

## Why this prompt is more focused than a generic handoff

The earlier `handoff-2026-04-27.md` is a comprehensive state doc.  This
prompt is the user-facing instruction that:

1. Names the prior session's failures (B+B', E held — admit scaffolding)
   so the new session understands the policy reaction concretely.
2. Distills 9 hard rules (R1–R9) so policy is loaded immediately.
3. Specifies four next-action options ordered by likely user
   priority, so the new session can act after one read of the state.
4. Forbids the specific anti-patterns (admit scaffolding, body
   `assume`s, mimicking pre-trait-opacity proofs) that wasted the
   prior session's runtime.
