# Agent dashboard — trait-opacify branch

Updated: 2026-04-27 (parent session, pre-Wave-1).

This dashboard is the resume entry point if the parent session or the
machine crashes.  It tracks every background sub-agent: branch, brief,
last-known state, log file location.  Each sub-agent commits its own
progress eagerly to its branch (see "Resume protocol" below).

## Wave 1 — fan-out 3-way

| Agent | Phase | Branch | State | Brief | Log |
|---|---|---|---|---|---|
| **A** | Phase 6 — drop 6 portable NTT-layer admits | `agent/phase-6-portable-ntt` | **A done** (4/6 proven, tip `65668af62`); **A2 spawning**: stretch goal — close 2 layer-1 admits via 4-per-zeta refactor recipe | `proofs/agent-status/agent-A-brief.md` + `agent-A2-brief.md` | `proofs/agent-status/agent-A.md` (on agent branch) |
| **B** | Phase 7c — Serialize re-root | `agent/phase-7c-serialize` | **done**: 9/9 brief cites + 1/6 trivial helper, 5 documented for next phase (tip `06d5e65ff`, ~75 min wall) | `proofs/agent-status/agent-B-brief.md` | `proofs/agent-status/agent-B.md` (on agent branch) |
| **C** | Phase 6c — AVX2 Sampling/Compress | `agent/phase-6c-avx2-stragglers` | **C+C2 done** (4/5 proven total, 1/5 admit-with-comment; C2 added 2 SMTPat axioms in Avx2_extract matching existing convention; tip `d077f29bc`) | `proofs/agent-status/agent-C-brief.md` + `agent-C2-brief.md` | `proofs/agent-status/agent-C.md` (on agent branch) |

States: `not started` / `spawning` / `running` / `paused (user review)` / `done` / `escalated`.

## Resource budget

- ≤ 4 concurrent F\* processes (8 in short bursts).
- Each F\* / Z3: 8 GB virtual cap (`ulimit -v 8388608`, `--z3cliopt
  smt.memory_max_size=8000`).
- Total RAM target: < 32 GB working set so the system never approaches
  the 48 GB OOM cliff.
- Each agent runs **one** fstar-mcp session at a time.

| Agent | fstar-mcp port |
|---|---|
| Parent (this session) | 3001 |
| A | 3002 |
| B | 3003 |
| C | 3004 |

## Resume protocol (if parent session or machine crashes)

```
cd ~/libcrux-trait-opacify
git fetch
git log --oneline trait-opacify -5

# For each agent branch listed above:
git log --oneline agent/phase-6-portable-ntt -20
git show agent/phase-6-portable-ntt:libcrux-ml-kem/proofs/agent-status/agent-A.md
# (repeat for B, C)

# Decide: resume agent (re-spawn with same brief + its log appended), or
# take over manually.
```

The brief files in `proofs/agent-status/agent-X-brief.md` on `trait-opacify`
are the source of truth for the prompt that was originally given.  The log
files on each agent branch are the source of truth for what the agent
actually did.

## Tooling decision (recorded after agent A's first 4 admits)

- **Default to plain `make`** for verification.  Inner loop is
  Rust-edit → `python3 hax.py extract` → `make X.fst.checked`; re-extract
  invalidates any fstar-mcp session anyway, so the session-amortization
  story doesn't apply.  Agent A demonstrated 50 s `make` cycles per
  iteration and dropped 4/6 admits in ~30 min.
- **fstar-mcp pays off only** when iterating ≥5 times on the same
  hand-written F\* file content (e.g., commute lemmas in
  `Hacspec_ml_kem.Commute.Chunk.fst` during Phase 7a).  Reassess at
  Wave 2.

## Update cadence

- Sub-agents: commit log file after **each meaningful step**.  Eager,
  not batched.  Commit messages: `agent-X: status — <one-line summary>`.
- Parent (this session): updates `dashboard.md` whenever an agent's State
  column changes, after polling agent branches.

## Coordination rules

- Sub-agents never push to origin, never merge to `trait-opacify`, never
  touch any other agent's branch.
- Parent reviews and merges (or hands diff to user).
- Cross-agent F\* spec edits: each agent's brief calls out which spec
  files are read-only vs. editable.  Conflicts surface at merge time.
