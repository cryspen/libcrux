# Next-session resume prompt — push Phase 7a Step 4/5 (after layer-2 Z3 unlock)

Paste the block below into a fresh Claude Code session opened in
`/Users/karthik/libcrux-trait-opacify/libcrux-ml-kem`.

---

```
You are continuing the multi-agent F* verification effort on
libcrux-ml-kem trait-opacify branch.  Branch tip: `43c9d45d5`
(2026-04-28 evening — Step 2 layers 2 & 3 bridges + Step 4 layer 3
strengthening landed).

WHAT'S DONE (Phase 7a, this session and earlier):
  * Step 1: layer-1 inverse hacspec bridge (Bridges.fst)         ✅
  * Step 2 layer 3 inverse bridge                                ✅ fa2151ea8
  * Step 2 layer 2 inverse bridge (the Z3 trap, unlocked!)       ✅ b7b49c358
  * Step 4 layer 1 strengthening (Option B template)             ✅ 8358b1093
  * Step 4 layer 3 strengthening (Option B applied)              ✅ 43c9d45d5
  * Step 7.1 + closed-form lane lemma (to_standard_domain)       ✅
  * Step 9: scaling-chain doc comments                           ✅
  * F* perf top-20 instrumentation seeded                        ✅

WHAT'S HELD / DEFERRED:
  * Step 4 layer 2 strengthening — first attempt this session failed
    with 6 Z3 errors at rlimit 800 (subtyping + assertion).  REVERTED
    to baseline.  Needs structured iteration.  See "Step 4 layer 2 —
    failure trace" below.
  * Step 7.2 (Rust integration for add_standard_error_reduce) — Z3
    saturated rlimit 800 on 2 invariant approaches.  TODO at
    src/polynomial.rs:567.

YOUR GOAL THIS SESSION: complete the critical path to **Step 5 —
invert_ntt_montgomery's strengthened post**.  Dependency chain:

  Step 4 layer 2 (held — diagnose the body Z3 failure)  ───┐
  Step 4 layer 4_plus (after Step 3 lands)                 ─┤
  Step 3 layer 4_plus cross-vector bridge (Bridges.fst)    ─┤
                                                            ▼
                                                          Step 5

The Step 4 strengthenings each follow the **Option B pattern**:
impl-level loop invariant only (`re.coef[j] == f_inv_ntt_layer_N_step
_re_init[j] (zeta(...))`), post-loop `Classical.forall_intro` invoking
the Bridges lemma 16 times per chunk.  Layer 1 + 3 are landed
templates.  See `src/invert_ntt.rs:13-139` (layer 1) and `:165-304`
(layer 3) for working examples.

═══════════════════════════════════════════════════════════════════
KEY UNLOCK FROM THIS SESSION — propagate to similar walls
═══════════════════════════════════════════════════════════════════

The layer 2 inverse Bridges.fst trait-post wall (3-way nested
if-ladder for `z`/`base`/`off`) was unlocked with this combination:

  1. **Per-branch decomposition with concrete `b`**: write 4 helper
     lemmas (`_branch_0_lane_bridge`, …, `_branch_3_lane_bridge`),
     each at a literal `b` so the trait branch_post's nested if-ladder
     collapses pre-SMT.
  2. **Per-lane wrapper** that dispatches lane `i` to the appropriate
     per-branch helper.  Each call site has only ~4 in-scope facts.
  3. **`--split_queries always`** on the per-vector composition lemma.
     Z3 splits the `forall j ∈ [0,16). r_fe[j] == rhs[j]` into 16
     cheap sub-queries (each <100 ms).

Failed approaches (do NOT retry):
  * Symbolic-b lane bridge (predicted Z3-trap from layer-2-forward).
  * 4 per-branch + aux body 4-way disjunction case-split: rlimit 400
    saturated in 11 min.
  * 4 per-branch + 16 explicit `assert (Seq.index r_fe j == ...)` +
    `Seq.lemma_eq_intro`: asserts pass; the lemma_eq_intro forall
    saturated 400 rlimit in 4 min.

Apply this pattern to layer 2 forward (USER-deferred), AVX2 layer 1/2
bridges (USER-4), and any future trait branch_post with a 3-way ladder.

═══════════════════════════════════════════════════════════════════
STEP 4 LAYER 2 — failure trace (start here)
═══════════════════════════════════════════════════════════════════

Attempted: same Option B template as layer 1/3.  Strengthened post:
```
forall (i: usize). i <. mk_usize 16 ==>
  mont_i16_to_spec_array (f_repr re_future.coefs[i]) ==
  IN.ntt_inverse_layer_n 16
    (mont_i16_to_spec_array (f_repr re.coefs[i]))
    4
    (Rust_primitives.unsize (zetas_2 (zeta(63 - 2*i)) (zeta(62 - 2*i))))
```

Errors at extracted Invert_ntt.fst:
  * **Line 183**: Assertion failed — the hand-holding assert
    `zeta_i == mk_usize 63 -! mk_usize 2 *! round` did not discharge.
    Layer 1's analog asserts succeeded; investigate why layer 2 differs.
  * **Line 184**: Subtyping — `zeta_i - 1` needs to fit in usize.
    Layer 1's hand-holding assert chain (4 asserts) gives Z3 the bound.
    Layer 2's chain (2 asserts) may be insufficient.
  * **Line 206 (×3)**: Loop-invariant non-preservation across body.
    Subtyping checks failed against the strengthened invariant.
  * **Line 140-235**: outer body assertion failed (the loop body's
    overall VC).

Hypotheses to investigate:
  * Layer 2's zeta_i decrement pattern is `(-= 1; ...; -= 1)` (two
    decrements) versus layer 1's `(-= 1; ...; -= 3)`.  Both decrement
    by the same total per round but at different points.  May need
    different hand-holding asserts.
  * Layer 2's strengthening references `Vector::f_inv_ntt_layer_2_step
    (Seq.index _re_init i) (zeta(63 - 2i)) (zeta(62 - 2i))`.  The
    second zeta arg uses `zeta_i - 1` — F* needs to see that
    `(63 - 2*round) - 1 = 62 - 2*round` is a valid usize.
  * The `_re_init` vs `re.coefficients` invariant — for unprocessed
    chunks, the layer 1 invariant says `Seq.index re.f_coefs i ==
    Seq.index _re_init i` AND `is_bounded_vector(...)`.  Did I have
    both conjuncts in layer 2's invariant?  Check the diff.

The reverted layer 2 strengthening attempt is **NOT in the git history
for this branch**.  It was discarded via `git checkout
libcrux-ml-kem/src/invert_ntt.rs` after the failed make.

To re-attempt: copy the layer 1 template structure exactly (using
`src/invert_ntt.rs:13-139` as the model), substituting layer-2 specifics
(bound trace 3328 → 2*3328, 2 zetas via zetas_2, post stride 4).  Use
fstar-mcp `typecheck_buffer` for sub-second iteration on the strengthened
invariant (after `python3 hax.py extract` to refresh the .fst).

═══════════════════════════════════════════════════════════════════

DEPENDENCY ORDER FOR THIS SESSION:

  1. **Step 4 layer 2** (held).  Hard cap 60 min.  If still blocked
     after 60 min: escalate, document the wall like Step 7.2, move on.
  2. **Step 3 layer 4_plus cross-vector bridge** (Bridges.fst).
     Hardest of bridges — 2 chunks at once + Barrett in step_reduce.
     Two variants per the plan.  May Z3-trap; mitigation per the
     layer-2 unlock if needed.
  3. **Step 4 layer 4_plus** (after Step 3).  Mechanical via Option B.
  4. **Step 5 invert_ntt_montgomery** post.  Highest Z3 risk.  If
     blocks: hand-decompose into 7 explicit `let`-bindings, one per
     layer post.

F* ITER-LOOP DISCIPLINE:

  α. **fstar-mcp typecheck_buffer** for inner-loop iteration on
     Bridges.fst — sub-second feedback.  Server already at port 3001.
     **Note**: the session dies if `make` runs concurrently.  Re-create
     after each `make`.

  β. When iterating Step 4 on layer N, **temporarily admit the OTHER
     layers** in src/invert_ntt.rs via:
       #[hax_lib::fstar::options("--admit_smt_queries true")] // TEMP
     Apply specifically to invert_ntt_at_layer_4_plus (saves 222 s
     per Invert_ntt rebuild).  **REMOVE before commit; re-extract;
     full make to confirm.**

  γ. Don't bulk-nuke .checked files.  hax.py prove + make handle stale
     incrementally.

VERIFICATION DISCIPLINE:

  * After each Bridges.fst lemma lands: fstar-mcp on Bridges.fst,
    then `make check/Hacspec_ml_kem.Commute.Bridges.fst` (~50s with
    fresh hints, ~5s with cached hints).
  * After each Step 4 layer Rust edit: `python3 hax.py extract`; then
    `make check/Libcrux_ml_kem.Invert_ntt.fst`.  Use the per-fn admit
    discipline (β) to keep iterations fast.
  * After Step 5 lands: `python3 hax.py prove` for full regression.
  * After all of Steps 2-5 land: refresh
    `proofs/agent-status/fstar-perf-top20.md` with a new snapshot.

HARD RULES R1-R10:
  R1 No admits or admit-driven scaffolding (except β temp-iter admits
     that revert before commit).  R5 No body assumes.  R6 ulimit -v
     8388608, F* rlimit ≤ 800.  R7 fstar-mcp for inner loop, make for
     end-of-chunk.  R8 Eager commit log to agent-trackA.md.

Resume protocol — load durable state in this order:

  1. proofs/agent-status/fstar-perf-top20.md  (perf data + admit guide)
  2. proofs/agent-status/agent-trackA.md      (latest session log)
  3. /Users/karthik/.claude/plans/replicated-beaming-pnueli.md (THE PLAN)
  4. proofs/proof-style-guide.md §12          (Mont-arith antipattern)
  5. proofs/agent-status/dashboard.md         (state table)
  6. MLKEM_STATUS.md                          (phase plan)

ENVIRONMENT VERIFY:
  cd /Users/karthik/libcrux-trait-opacify
  git status              # should be clean on trait-opacify
  git log --oneline trait-opacify -7
  pgrep -f fstar.exe      # ml-kem fstar-mcp at port 3001 (may need restart)

REPORT one paragraph state summary on entry, then:
  * Re-attempt Step 4 layer 2 (study layer 1 template carefully).
  * Or, if user chooses, jump to Step 3 layer 4_plus cross-vector
    bridge (defer Step 4 layer 2 to user lane).

If Step 4 layer 2 hits a Z3 wall: document and escalate per Step 7.2
held-work pattern — preserve infrastructure, document the wall, move on.
```

---

## Why this prompt is structured this way

- **Z3 unlock prominent at top** — the layer 2 Bridges trick (per-branch
  + per-lane wrapper + `--split_queries always`) is the key
  transferable lesson from this session.  Apply to similar walls.
- **Step 4 layer 2 failure trace** — captures the 6 errors with line
  numbers + hypotheses so the next agent can start debugging
  immediately, not rediscover.
- **Failed approaches list** — explicit "do NOT retry" prevents
  rediscovery of the 11-min and 4-min Z3 traps.
- **Dependency graph + time estimates** — guides session pacing.
