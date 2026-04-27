# Handoff prompt — paste into new session

Copy the block below into a fresh Claude Code session at
`/Users/karthik/libcrux-trait-opacify/libcrux-ml-kem`.  It primes the
new session to load durable state and resume work.

---

```
You are continuing a multi-agent F* verification effort on the
libcrux-ml-kem trait-opacify branch.  The previous session ran 6
agents in parallel across Phases 6, 6c, 7c, and 7a, then handed off
intentionally for token efficiency.

Resume protocol — read these files in order, then report back what
state you found:

1. libcrux-ml-kem/proofs/agent-status/handoff-2026-04-27.md  (THIS FIRST)
2. libcrux-ml-kem/MLKEM_STATUS.md
3. libcrux-ml-kem/proofs/session-handoff.md
4. libcrux-ml-kem/proofs/agent-status/dashboard.md
5. libcrux-ml-kem/proofs/proof-style-guide.md
6. libcrux-ml-kem/proofs/agent-status/held-work-Bprime-L123.md

If Agent E (Phase 7a Polynomial) had not completed when the handoff
was prepared, check now:
- git log --oneline agent/phase-7a-polynomial -10
- git show agent/phase-7a-polynomial:libcrux-ml-kem/proofs/agent-status/agent-E.md | tail -40
If E has finished and you find a completion notification waiting,
update handoff-2026-04-27.md with E's outcome, then propose merging
agent/phase-7a-polynomial into trait-opacify (or holding it like
B+B' if the proofs are bridge-only and not worth merging).

Working principles to honor (these are durable preferences from
prior sessions, do not relearn):
- User handles math-heavy / Z3-blocked / template-setting proofs.
  Agents handle pattern-following / Tier-N composition / mechanical work.
- Default to plain `make` for verification; fstar-mcp only when
  iterating ≥5 times on the SAME hand-written F* file.
- Resource budget: ≤4 concurrent F* processes (8 brief), 8 GB each,
  total <32 GB on this 48 GB box.  Past OOMs crashed the system.
- Agents work in isolated worktrees on dedicated branches;
  eager-commit logs to proofs/agent-status/agent-X.md on the branch.
- Bridge-admit scaffolding (B's pattern) is NOT preferred when the
  spec being bridged is scheduled for deletion.  Hold and document
  for future specialist work instead.
- Rust function bodies: don't touch algorithmically (only loop-
  invariant strengthening).  F* spec / commute / opaque-predicate
  files: editable.  traits.rs::spec opaque per-branch predicates:
  don't redesign.

After loading state, decide the next concrete action:
- If E is done: aggregate its outcome, update dashboard, and ask the
  user whether to spawn Wave 3 (Phases 7b NTT, 7d Matrix, 7n
  Sampling — see handoff doc for the parallelism plan).
- If E is still running: poll, check memory pressure, wait for
  completion notification.  Don't spawn additional agents until E
  finishes.

Be terse in your initial state report — one paragraph or a short
table.  Don't replay the full handoff doc back to the user.
```

---

## Why a handoff prompt and not just "continue from where we left off"

A fresh session has no memory of this conversation.  The prompt above
gives it a precise read-list and the durable preferences it needs to
honor without relearning them.  All other state is in git, where the
new session reads it directly.

The new session may also miss subtle context (e.g., why a particular
agent was held).  The handoff doc covers those decisions explicitly.
