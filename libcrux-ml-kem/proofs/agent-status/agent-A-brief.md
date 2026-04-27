# Agent A — Phase 6: drop 6 portable NTT-layer admits

This is the brief originally given to agent A.  The agent's progress log
lives at `proofs/agent-status/agent-A.md` on branch
`agent/phase-6-portable-ntt`.

## Mission

Close the F\* proofs of 6 `op_*` functions in
`libcrux-ml-kem/src/vector/portable.rs` so each can drop its
`#[hax_lib::fstar::options("--admit_smt_queries true")]` annotation.  The
proof scaffold (`reveal_opaque (\`%X_step_branch_post)` + 8
`butterfly_pair_commute` calls + `forall4 p_layer_X` assert) is reportedly
already in place behind each admit; the work is to make it actually verify.

## Targets (current line numbers on `trait-opacify`)

| Order | Function | Line | Zetas |
|---|---|---|---|
| 1 (start here, simplest) | `op_ntt_layer_3_step` | 488 | 1 |
| 2 | `op_inv_ntt_layer_3_step` | 718 | 1 |
| 3 | `op_ntt_layer_2_step` | 410 | 2 |
| 4 | `op_inv_ntt_layer_2_step` | 641 | 2 |
| 5 | `op_ntt_layer_1_step` | 331 | 4 |
| 6 | `op_inv_ntt_layer_1_step` | 563 | 4 |

## Required reading (in order)

1. `libcrux-ml-kem/MLKEM_STATUS.md` — top-level state, esp. AGENT TASKS / Phase 6 sections
2. `libcrux-ml-kem/proofs/session-handoff.md` — resume-ready short list
3. `libcrux-ml-kem/proofs/proof-style-guide.md` — patterns + cut-off rules
4. AVX2 in-tree templates: `src/vector/avx2/ntt.rs::ntt_layer_3_step` and `src/vector/avx2.rs::op_ntt_layer_3_step` are the closest already-proven analogues; mirror their shape

## Operating constraints

- **Wall clock budget**: 90 min total.  Hard stop and finalize at 90 min.
- **Per-admit budget**: ~20 min.  If an admit doesn't close in 20 min using
  standard tweaks (rlimit ≤ 800, `--split_queries always`, reveal-scope
  fixes), STOP on that admit and:
  - Restore `--admit_smt_queries true`
  - Add an English comment immediately above the function describing
    (a) what was tried, (b) hypothesis for why the proof should work, (c)
    next step for the user
  - Commit and move on
- **Memory**: prefix any shell that spawns F\* with `ulimit -v 8388608`.
  Pass `--z3cliopt smt.memory_max_size=8000` in F\* options.
- **F\* concurrency**: at most 1 fstar-mcp session.  Use port **3002**.
- **F\* rlimit**: never exceed 800.  If a query needs more, that's a
  signal to refactor or admit.

## Code change policy

- Rust function bodies of `op_ntt_layer_*_step`: **DO NOT TOUCH**.
- F\* annotations on the Rust functions (`fstar::options`, `fstar::before`,
  inline `fstar!(...)` proof blocks): editable.
- F\* spec / lemma files (`*.fsti`, `*.fst` under `proofs/fstar/`,
  `Hacspec_ml_kem.Commute.Chunk.fst`, `traits.rs::spec` block): editable
  with the post-only invariant — only conjunctive additions to public
  posts; new helper / commute lemmas welcome.
- Opaque predicates in `traits.rs::spec` (the per-branch
  `*_step_branch_post`): do NOT redesign.  Re-use as-is.

## fstar-mcp setup

```bash
ulimit -v 8388608
FSTAR_MCP_PORT=3002 /Users/karthik/fstar-mcp/target/release/fstar-mcp \
    > /tmp/fstar-mcp-agent-A.log 2>&1 &

# Probe:
curl -s -X POST http://localhost:3002/ \
  -H 'Content-Type: application/json' \
  -H 'Accept: application/json, text/event-stream' \
  -d '{"jsonrpc":"2.0","id":1,"method":"tools/list"}'
```

Include directories for `Libcrux_ml_kem.Vector.Portable.fst` (extract from
`make -n Libcrux_ml_kem.Vector.Portable.fst.checked` if unsure):

```
../spec
/Users/karthik/.cargo/git/checkouts/hax-580ebeee043cdea1/492a34e/hax-lib/proof-libs/fstar/core
/Users/karthik/.cargo/git/checkouts/hax-580ebeee043cdea1/492a34e/hax-lib/proof-libs/fstar/rust_primitives
/Users/karthik/.cargo/git/checkouts/hax-580ebeee043cdea1/492a34e/hax-lib/proofs/fstar/extraction
/Users/karthik/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/core-models-0.0.5/proofs/fstar/extraction
<all the workspace `proofs/fstar/extraction` dirs — see Makefile.generic dry-run>
```

Cache: `/Users/karthik/libcrux-trait-opacify/.fstar-cache/checked` (shared
across worktrees).  Hints: `--use_hints --record_hints`.

## Recommended approach per admit

1. Open `Libcrux_ml_kem.Vector.Portable.fst` in fstar-mcp.
2. In `src/vector/portable.rs`, remove `--admit_smt_queries true` from one
   target.  Re-extract: `cd libcrux-ml-kem && python3 hax.py extract`
   (this is the slow step; minimize re-extracts by batching small Rust
   annotation edits).
3. `typecheck_buffer` on the regenerated F\* file.  Use `lax: true` for
   structural checks; `kind: full` for SMT.
4. If the failed query is in the target function, try in order:
   - Add `reveal_opaque` of the relevant `*_step_branch_post` at the
     correct scope
   - Bump rlimit (200 → 400 → 800; never higher)
   - `--split_queries always`
   - Refactor: replace 8 manual `aux` calls with
     `Classical.forall_intro` over a per-branch lemma (pattern from
     `op_compress_*` in §3.4 of proof-style-guide)
5. If still fails after 20 min on this target → admit-with-comment, commit,
   move on.

## Status logging — DO THIS EAGERLY

Maintain `libcrux-ml-kem/proofs/agent-status/agent-A.md` on your branch
`agent/phase-6-portable-ntt`.  After every meaningful step:
1. Append a timestamped entry to the log
2. Stage the log + any code/proof changes
3. `git commit -m "agent-A: status — <one-line>"` (or
   `agent-A: phase-6 — <function>: proven` / `admitted-with-comment` etc.
   for substantive commits)

Eager commits are CRITICAL.  This session or your machine may crash; the
commit graph is the only durable resume point.

Initial log skeleton:

```markdown
# Agent A — Phase 6 portable NTT admit drops

**Branch**: agent/phase-6-portable-ntt
**Brief**: see proofs/agent-status/agent-A-brief.md on trait-opacify

## Targets
- [ ] op_ntt_layer_3_step  (start here)
- [ ] op_inv_ntt_layer_3_step
- [ ] op_ntt_layer_2_step
- [ ] op_inv_ntt_layer_2_step
- [ ] op_ntt_layer_1_step
- [ ] op_inv_ntt_layer_1_step

## Progress (append-only, newest at bottom)

### YYYY-MM-DD HH:MM:SS UTC — Started
...
```

Use `[x]` (proven), `[~]` (admitted with English comment), `[!]` (blocker).

## Stop conditions / escalate (do NOT continue)

- Z3 OOM kill (memory cap hit) on the same target twice
- F\* segfault on the same target twice (known on this machine at high rlimit)
- 90 min wall clock exceeded
- All 6 admits handled (proven, admitted-with-comment, or blocker-escalated)

When stopping, ensure:
1. Final status commit on `agent-A.md` summarizing outcome
2. Run `make Libcrux_ml_kem.Vector.Portable.fst.checked` once and record
   pass / fail / time in the log
3. Tear down your fstar-mcp server

## Final deliverable

A short summary back to the parent including:
- Number of admits proven / admitted-with-comment / blocker
- Last commit hash on `agent/phase-6-portable-ntt`
- Verification state of `Libcrux_ml_kem.Vector.Portable.fst`
- Any escalations needed

## Hard rules

- DO NOT push to origin.
- DO NOT merge to `trait-opacify`.
- DO NOT touch other agents' branches or files outside the scope above.
- DO NOT exceed F\* rlimit 800.
- DO NOT alter Rust function bodies of `op_*` (only the F\* annotations
  attached to them).
