# Edit-check loop: fstar-mcp vs admit-everything-else (Ind_cpa.fst)

Date: 2026-04-29
Branch: `trait-opacify`
Target: `libcrux-ml-kem/proofs/fstar/extraction/Libcrux_ml_kem.Ind_cpa.fst` (1365 LoC)
Cache state at start: warm (217 `.checked` files), Ind_cpa already in `ADMIT_MODULES`
F* version: 2026.03.24, Z3 4.13.3, Apple Silicon (Darwin arm64)

## 1. Verdict

**Inconclusive at the level of the original question, but with strong directional findings:**

- For **admitted modules** (Ind_cpa as it stands today on this branch), the **plain `make check/<X>.fst` loop wins** at ~9 s warm. fstar-mcp typecheck_buffer over HTTP failed to deliver responses to the client within practical timeouts. Approach B (admit-everything-else) provides no benefit because the module is already admitted in the default Makefile.
- For **non-admitted heavy modules** (the realistic case Approach B was designed for), Approach B was attempted but proves intractable on this branch: removing Ind_cpa from `ADMIT_MODULES` triggered a single Z3 query that consumed >11 minutes CPU before the experiment was killed. (Confirms Ind_cpa really does not close on this branch — that's why it's admitted.)
- fstar-mcp's session ID was happily issued and `last_activity` advanced on the server side, but the HTTP `tools/call` response never returned to `curl` — both `lax` and `verify-to-position` to line 30 timed out at 5 min and 2 min respectively. **The fstar-mcp HTTP transport appears unreliable for buffers of ~55 KB.**

**Practical winner: plain `make check/<X>.fst` (Approach 0 / baseline).** Approach A is faster *in principle* but did not deliver responses in this session. Approach B has no purpose for already-admitted modules and is impractical when the proof is genuinely broken.

## 2. Concrete numbers

| Scenario | Wall time | Notes |
|---|---|---|
| **Baseline** `make check/Libcrux_ml_kem.Ind_cpa.fst` (Ind_cpa in ADMIT_MODULES, warm) | **9.0 s** real, 4.0 s F* TOTAL TIME | one fstar.exe spawn per call, no SMT |
| **Approach A** `create_session` (HTTP) — *fstar.exe was already resident from prior agent (PID 32385)* | timed out at 600 s (10 min); session DID register on server side after ~13 min | reused old fstar.exe, did not reload deps |
| **Approach A** `typecheck_buffer kind=lax` (full 56 KB body) | timed out at 300 s (5 min); server's `last_activity` advanced (i.e., F* completed work) but client never got response | HTTP transport bug |
| **Approach A** `typecheck_buffer kind=verify-to-position to_line=30` | timed out at 120 s (2 min); same symptom | confirms not a content-size issue alone |
| **Approach B** make `ADMIT_MODULES=<all-but-Ind_cpa-and-SLOW>` cold (`.checked` deleted) | **11 min 38 s** **and FAILED** | Z3 hung on serialize_vector queries; this proof legitimately doesn't close on this branch |
| **Approach B** rerun (after kill) | 2 min 37 s, failed at unrelated `Hacspec_ml_kem.Commute.Chunk.fst.checked` | dep-graph cascade re-verifies stale deps |
| **Approach B** third rerun | 50.9 s, same Commute.Chunk failure | second-order cache thrash |

## 3. Pros / cons

| Dimension | Approach 0 (plain make + ADMIT) | Approach A (fstar-mcp) | Approach B (admit-all-but-target) |
|---|---|---|---|
| Cold start | ~9 s (warm cache) | session-create slow + unreliable | tens of seconds to minutes (depends on cache + dep stability) |
| Warm iteration | ~9 s every call (no incremental win) | should be 0.5–5 s in principle; observed: did not return | not applicable: dep-graph rechecks on every stale cache hit |
| Incrementality within a file | none — full re-typecheck | yes, fragments + position-scoped | none — full module re-check |
| Concurrency safety | safe — independent fstar.exe per call | session can be killed by other `make` runs (memory note) | safe |
| Error signal | raw F* stdout (must read) | structured `diagnostics[]` JSON | raw F* stdout |
| Setup cost | zero — Makefile already has it | one HTTP round-trip + correct include_dirs/options | construct ALL_MODS list, exclude SLOW_MODULES |
| Robustness on this branch | best — fully working today | unreliable — HTTP responses don't come back | brittle — any stale dep `.checked` blocks the make |
| Lax mode | no | yes (`kind: "lax"`) when it works | no |

## 4. Recommended canonical edit-check loop (Ind_cpa or other heavy module on this branch)

**Today, on `trait-opacify` branch, for an admitted module:**
```bash
cd /Users/karthik/libcrux-trait-opacify/libcrux-ml-kem/proofs/fstar/extraction
make check/Libcrux_ml_kem.Ind_cpa.fst
# ~9 s warm, prints diagnostic if anything in the module fails to parse/type
```

**If editing a non-admitted heavy module (e.g. Polynomial / Invert_ntt where the proof exists):**
1. Delete that module's `.checked` only (not bulk):
   `rm -f /Users/karthik/libcrux-trait-opacify/.fstar-cache/checked/<Mod>.fst.checked`
2. Iterate via `make check/<Mod>.fst` — Makefile rebuilds only what's required; admitted deps stay admitted via the existing ADMIT_MODULES list.
3. Do NOT use Approach B (admit-all-but-target) on this branch — it loses the SLOW_MODULES guard and exposes you to unrelated cache-stale failures (e.g. `Hacspec_ml_kem.Commute.Chunk.fst`).

**If you want to use fstar-mcp:** start a fresh server in *this very shell*, create the session, and immediately verify it responds to a small `lookup_symbol` call BEFORE attempting `typecheck_buffer` on the full file. If small calls also hang, fall back to plain `make`.

**Recommended fstar-mcp invocation** (when the transport is healthy):
```jsonc
// create_session — file_path, cwd, include_dirs, and these options:
"options": [
  "--warn_error", "-321-331-241-274-239-271",
  "--ext", "context_pruning",
  "--z3version", "4.13.3",
  "--cache_checked_modules",
  "--cache_dir", "/Users/karthik/libcrux-trait-opacify/.fstar-cache/checked",
  "--already_cached", "+Prims+FStar+LowStar+C+Spec.Loops+TestLib"
]
```

## 5. Notable surprises

1. **fstar-mcp HTTP transport is the bottleneck, not F* itself.** Server-side `last_activity` advanced (F* completed the typecheck), but the JSON-RPC POST never delivered a response to `curl` — confirmed with `Accept: application/json` and `Accept: text/event-stream`. The skill docs do not mention this; it deserves a feedback memory.
2. **Long-resident fstar.exe `--ide` processes from prior sessions persist for >12 hours** and silently get reused by `create_session` — the "create_session is slow" cost in the skill docs may be misleading on a warm system. (PID 32385 had been alive since 7:32 AM that day.)
3. **The `feedback_fstar_mcp_session_dies_after_make.md` failure mode was NOT triggered here** — sessions remained alive across `make` invocations during this experiment. The killer is apparently more specific than "any concurrent make."
4. **Approach B has a hidden trap:** removing a SLOW_MODULES from ADMIT triggers a Makefile.base error, AND any unrelated stale `.checked` will be silently force-rebuilt by the dep walk and may fail (we hit `Hacspec_ml_kem.Commute.Chunk.fst` failing during a make of Ind_cpa). The "admit everything else" mental model is leakier than it looks.
5. **The plan's assumption that warm iterations on Approach A would beat Approach B** holds in principle but Approach A failed empirically here — it's only better than `make` if you can keep responses flowing.
6. **Per `feedback_no_cache_nuke.md`** — the experiment confirmed why: even surgical `.checked` deletion caused cascading rebuilds when the upstream graph was already stale.

## 6. Files left clean

Verified `Libcrux_ml_kem.Ind_cpa.fst` SHA = `863e76ec61a9cc38828b08a2966f73bb20dceab7` (unchanged from start). Makefile not edited. New `.checked` writes went only to the standard cache dir. No commits made.

External worktree agents modified `libcrux-ml-kem/src/vector/traits.rs`, `specs/ml-kem/proofs/fstar/commute/Hacspec_ml_kem.Commute.Chunk.fst`, and `Hacspec_ml_kem.ModQ.fst` *during* the experiment window — these mtimes (08:01, 08:08, 07:58 on 2026-04-29) overlap with this experiment but were not produced by this agent.
