# Agent dashboard — trait-opacify branch

Updated: 2026-04-28 (post track A — Phase 7a Step 1 done).

This dashboard is the resume entry point if the parent session or the
machine crashes.  It tracks every background sub-agent: branch, brief,
last-known state, log file location.  Each sub-agent commits its own
progress eagerly to its branch (see "Resume protocol" below).

## Wave 1 — fan-out 3-way

| Agent | Phase | Branch | State | Brief | Log |
|---|---|---|---|---|---|
| **A** | Phase 6 — drop 6 portable NTT-layer admits | `agent/phase-6-portable-ntt` | **A+A2 done & MERGED** (4/6 proven; A2 0/2 stretch — added 2 helper lemmas for future predicate-reshape USER work); merge `6f41ec5bc` | `proofs/agent-status/agent-A-brief.md` + `agent-A2-brief.md` | `proofs/agent-status/agent-A.md` (on agent branch + trait-opacify) |
| **B** | Phase 7c — Serialize re-root | `agent/phase-7c-serialize` (HELD) | **HELD for future specialist work** — see `held-work-Bprime-L123.md`. Branch tip `1c2b0ee4f` preserved for L1/L2/L3 specialist relaunch. | `proofs/agent-status/agent-B-brief.md` + `agent-B-prime-brief.md` | `proofs/agent-status/agent-B.md` (on branch); `held-work-Bprime-L123.md` (on trait-opacify) |
| **E** | Phase 7a — Polynomial scalar ops (Wave 2) | DELETED | **Killed** — admit-driven scaffolding, work superseded by E2's real proofs.  Branch + worktree + held-work doc deleted 2026-04-28 to remove distraction. |  |  |
| **E2** | Phase 7a — real-proof relaunch | merged via `5ace3f268` | **2/6 closed and merged** (poly_barrett_reduce, add_to_ring_element).  4/6 (subtract_reduce, add_error_reduce, add_standard_error_reduce, add_message_error_reduce) HELD pending strategic decision; see proof-style-guide.md §12 + handoff-2026-04-28.md. | `proofs/agent-status/agent-E2-brief.md` | `proofs/agent-status/agent-E2.md` |
| **F** | Phase 7b — NTT/Inv-NTT layers + INTT-Mont post foundation | merged via `2a8291431` | **Foundation done** — opaque `intt_mont_form_chunk` predicate + `lemma_intt_mont_finalize_fe` per-element bridge + Tier-0 numeric chain proving `1441 = mont²/128` (per pq-crystals/kyber/ref/ntt.c line 106).  Forward NTT layer 1 hacspec bridge committed (1/8 layer fns).  Layers 2-8 + full INTT-Mont post on invert_ntt_montgomery DEFERRED — Z3 timeout on layer-2 lane bridge, structural F* work needed. | `proofs/agent-status/agent-F-brief.md` | `proofs/agent-status/agent-F.md` |
| **E3** | Phase 7a-finish (4 reduce fns) | ABANDONED 2026-04-28 | **Killed** — explored 5 paths to discharge the 4 held reduce fns via a strengthened invert_ntt_montgomery post: full Tier-3 (Z3-blocked, days), admit-bridge (policy-violating), caller-assumes (rejected), refactor (sacrifices fusion optimization), spec-extension-into-Mont (wrong-direction).  No clear winner; stopped to document antipattern.  Branch + worktree deleted. | `proofs/agent-status/agent-E3-brief.md` (kept for reference) | n/a |
| **C** | Phase 6c — AVX2 Sampling/Compress | `agent/phase-6c-avx2-stragglers` | **C+C2 done & MERGED** (4/5 proven, 1/5 admit-with-comment; 2 SMTPat axioms in Avx2_extract); merge `2953fbf9c` | `proofs/agent-status/agent-C-brief.md` + `agent-C2-brief.md` | `proofs/agent-status/agent-C.md` (on agent branch + trait-opacify) |
| **trackA** | Phase 7a Step 1 — inverse NTT layer 1 hacspec bridge + Step 9 scaling-chain doc comments + Bridges.fst split | trait-opacify direct (no agent branch) | **DONE & VERIFIED**, tip `ba8681b38`. Created `Hacspec_ml_kem.Commute.Bridges.fst` (sibling of Chunk.fst); contains forward + inverse layer 1 function-form per-vector hacspec bridges.  Bridges.fst verifies in 5.8s with hints.  Polynomial.fst regression encountered mid-session was traced to a stale .fst extraction (.fsti was newer); fixed via `python3 hax.py extract`.  All ml-kem modules verified post-fix, no regressions. | n/a (this dashboard + agent-trackA.md are the durable artifacts) | `proofs/agent-status/agent-trackA.md` |

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
