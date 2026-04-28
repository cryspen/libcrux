# Next-session resume prompt — push to invert_ntt_montgomery

Paste the block below into a fresh Claude Code session opened in
`/Users/karthik/libcrux-trait-opacify/libcrux-ml-kem`.

---

```
You are continuing the multi-agent F* verification effort on
libcrux-ml-kem trait-opacify branch.  Branch tip: `5baa974c4`
(2026-04-28 afternoon, end of trackA + lane-d sub-agent merge).

WHAT'S DONE (Phase 7a):
  * Step 1: inverse NTT layer-1 hacspec bridge in Bridges.fst    ✅
  * Step 4 layer 1: invert_ntt_at_layer_1 strengthened post     ✅ 8358b1093
  * Step 7.1: F* infra for to_standard_domain track (Chunk.fst)  ✅ c07feb91c
  * Step 7.1+: closed-form lane lemma                            ✅ 8ff3ac14c
  * Step 9: scaling-chain doc comments                           ✅
  * F* perf top-20 instrumentation seeded                        ✅

WHAT'S HELD:
  * Step 7.2 (Rust integration for add_standard_error_reduce) —
    Z3 saturated rlimit 800 on 2 invariant approaches (nested-forall
    @85s/q and closed-form @230-380s/q).  TODO at src/polynomial.rs:567.
    Suggested fix: explicit ghost ntt_product Rust parameter.

YOUR GOAL THIS SESSION: push down the critical path to
**invert_ntt_montgomery's strengthened post** (Phase 7a Step 5).
Dependency chain:

  Step 2 layer 3 bridge (Bridges.fst)  ──┐
  Step 2 layer 2 bridge (Bridges.fst)  ──┤
  Step 3 layer 4_plus bridge (Bridges.fst, cross-vector + barrett) ──┤
                                                                    ▼
  Step 4 layer 2 (src/invert_ntt.rs)                              Step 5
  Step 4 layer 3                                                  invert_ntt_
  Step 4 layer 4_plus                                              montgomery

The Step 4 strengthenings each follow the **Option B pattern proven on
layer 1 this session**: impl-level loop invariant only (just
`re.coef[j] == f_inv_ntt_layer_N_step _re_init[j] (zeta(...)) ...`),
post-loop `Classical.forall_intro` invoking the Bridges lemma 16 times
per chunk.  See src/invert_ntt.rs:13-115 for the layer-1 template.

KEY LANDING PROBLEMS (pre-empt):

  * Layer 2's Bridges lemma — the trait branch_post for layer 2 has
    a NESTED if-ladder (b → (z, base, off)) that previously caused
    Z3 timeouts >2.7 min on a single sub-query.  Mitigation noted in
    Bridges.fst's deferred-work comment: explicitly enumerate
    i ∈ {0..15} to remove the symbolic b — write 16 per-lane sub-cases.

  * Layer 4_plus is harder than 1/2/3 (cross-vector, chunk pairs +
    Barrett).  Two variants per the plan.

  * Step 5 (invert_ntt_montgomery) is the highest Z3 risk.  If it
    blocks: hand-decompose into 7 explicit `let`-bindings, one per
    layer post.

F* ITER-LOOP DISCIPLINE (per fstar-perf-top20.md §"Reducing F*
roundtrip"):

  α. **fstar-mcp typecheck_buffer** for inner-loop iteration on
     Bridges.fst / Chunk.fst — sub-second feedback.  Server already at
     port 3001.  Skill: ~/.claude/skills/fstar-mcp/.

  β. When iterating Step 4 on layer N, **temporarily admit the OTHER
     layer fns** in src/invert_ntt.rs via:
       #[hax_lib::fstar::options("--admit_smt_queries true")] // TEMP
     Apply specifically to invert_ntt_at_layer_4_plus first — it
     dominates Invert_ntt rebuilds (~222 s / 8.8 min wall).  Saves
     half the make cost.  REMOVE all such temp admits at end of step.

  γ. Don't bulk-nuke .checked files (per memory).  hax.py prove + make
     handle stale incrementally.

VERIFICATION DISCIPLINE:

  * After each Bridges.fst lemma lands: fstar-mcp on Bridges.fst,
    then quick make Hacspec_ml_kem.Commute.Bridges.fst.checked
    (~6s with hints).
  * After each Step 4 layer Rust edit: python3 hax.py extract; then
    make Libcrux_ml_kem.Invert_ntt.fst.checked.  Use the per-fn admit
    discipline above to keep iterations fast.
  * After Step 5 lands: full python3 hax.py prove for regression.
  * After all of Steps 2-5 land: refresh
    proofs/agent-status/fstar-perf-top20.md with a new snapshot.

HARD RULES R1-R10 (still apply, see proofs/agent-status/agent-F-brief.md):
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
  git log --oneline trait-opacify -5
  pgrep -f fstar.exe      # ml-dsa worktree may have one; ml-kem
                          #  fstar-mcp at port 3001

REPORT one paragraph state summary on entry, then dive into Step 2
layer 3 (the easiest of the remaining bridges; should close in ~1h
with fstar-mcp).  Then layer 2 (the Z3-trap; budget ~2h with
i-enumeration mitigation).  Then layer 4_plus.  Then Step 4 ×3 layer
strengthenings (mechanical, ~30 min each via Option B pattern).
Then Step 5.

If Step 5 hits a Z3 wall: hand-decompose; if still blocked, escalate
with the empirical timing data and the same kind of held-work
pattern as Step 7.2 — preserve infrastructure, document the wall,
move on.
```

---

## Why this prompt is structured this way

- **Single-paragraph state summary** at the top so a fresh agent
  has the prior-art context without grinding through commit logs.
- **Dependency graph upfront** — most-impactful instruction; tells the
  agent what unblocks what.
- **Z3 trap pre-emption** — layer 2's nested if-ladder is the known
  trap; the agent shouldn't rediscover it.
- **Iter discipline** — fstar-mcp + per-fn admits.  Both new lessons
  from this session that need to propagate.
- **Hard cap on each step** — implicit via the time estimates; the
  agent's brief should fail fast and escalate per R3 (30-min cap on
  target #1).
