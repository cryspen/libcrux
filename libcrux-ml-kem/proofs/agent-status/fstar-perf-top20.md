# F* verification time — top-20 culprits

Standing instruction (per memory `feedback_track_fstar_perf`): refresh
this file after every full F* build (`python3 hax.py prove` or full
`make`).  Append new snapshots; keep prior ones for regression tracking.

Use awk/python to parse `Query-stats` lines from the build log:
- per-function `total = Σ ms` and `max single query ms`
- count of queries
- `failed` flag (Z3 returned unknown / canceled)
- `saturated` flag (`used rlimit > 0.8 * rlimit`)

---

## Snapshot 1 — 2026-04-28 — `verification_result.txt` from prior session (tip `ba8681b38`-ish)

Source: `libcrux-ml-kem/verification_result.txt` (last `hax.py prove`
exit 0 from morning track-A session).  All ml-kem-related modules.

| # | Total (s) | Max query (ms) | Queries | Failed | rlimit-sat | Module | Function |
|---|---|---|---|---|---|---|---|
| 1 | 31.9 | 31739 | 3 | 1 | 1 | Libcrux_ml_kem.Invert_ntt | invert_ntt_at_layer_4_plus |
| 2 | 30.4 | 30437 | 1 | 0 | 0 | Hacspec_ml_kem.Commute.Chunk | lemma_base_case_mult_even_mod_core |
| 3 | 24.7 |  1796 | 225 | 42 | 0 | Libcrux_ml_kem.Ntt | ntt_at_layer_4_plus |
| 4 |  8.5 |   461 | 75 | 0 | 0 | Libcrux_ml_kem.Vector.Avx2 | op_ntt_layer_3_step |
| 5 |  8.2 |   150 | 75 | 2 | 0 | Libcrux_ml_kem.Vector.Avx2 | op_inv_ntt_layer_3_step |
| 6 |  7.2 |  3644 | 2 | 0 | 0 | Libcrux_ml_kem.Polynomial | v_ZETAS_TIMES_MONTGOMERY_R |
| 7 |  7.0 |   121 | 79 | 17 | 0 | Libcrux_ml_kem.Ntt | ntt_at_layer_7_ |
| 8 |  7.0 |   100 | 81 | 6 | 0 | Libcrux_ml_kem.Polynomial | add_message_error_reduce |
| 9 |  6.7 |   212 | 70 | 0 | 0 | Libcrux_ml_kem.Vector.Portable | op_inv_ntt_layer_3_step |
| 10 |  6.5 |   121 | 70 | 0 | 0 | Libcrux_ml_kem.Vector.Portable | op_ntt_layer_3_step |
| 11 |  5.6 |   164 | 57 | 0 | 0 | Libcrux_ml_kem.Vector.Portable | op_inv_ntt_layer_2_step |
| 12 |  5.3 |   113 | 60 | 40 | 0 | Libcrux_ml_kem.Polynomial | add_to_ring_element |
| 13 |  5.3 |   116 | 57 | 0 | 0 | Libcrux_ml_kem.Vector.Portable | op_ntt_layer_2_step |
| 14 |  5.1 |   121 | 57 | 6 | 0 | Libcrux_ml_kem.Polynomial | subtract_reduce |
| 15 |  5.0 |   153 | 54 | 0 | 0 | Libcrux_ml_kem.Ntt | ntt_vector_u |
| 16 |  4.8 |   129 | 56 | 16 | 0 | Libcrux_ml_kem.Polynomial | ntt_multiply |
| 17 |  4.3 |   101 | 52 | 5 | 0 | Libcrux_ml_kem.Polynomial | add_error_reduce |
| 18 |  4.2 |    97 | 50 | 6 | 0 | Libcrux_ml_kem.Polynomial | add_standard_error_reduce |
| 19 |  3.4 |  3302 | 2 | 0 | 0 | Hacspec_ml_kem.Commute.Chunk | lemma_ntt_layer_1_step_lane_bridge |
| 20 |  3.2 |   127 | 33 | 1 | 0 | Libcrux_ml_kem.Vector.Portable | op_decompress_1_ |

### Observations

- **Two outliers dominate**: `invert_ntt_at_layer_4_plus` (#1) and
  `lemma_base_case_mult_even_mod_core` (#2) each cost ~30 s on a single
  query — i.e., one heavy SMT problem each, not many small ones.
  **#1's Q2 hit the rlimit ceiling (saturated) — known borderline.**
  Both are candidates for proof restructuring or temporary admits.
- **`ntt_at_layer_4_plus` (#3)**: 225 queries with 42 failures.
  High failure rate suggests intermittent flakiness or unhinted paths.
- **The 7 `Polynomial` reduce-family fns** (#6, #8, #12, #14, #16,
  #17, #18) collectively cost ~38 s.  Most are 50-80 queries each at
  100-130 ms max — these are the strengthened Phase 7a fns from
  agents E2 and (in flight) trackD.
- **The 6 `op_{ntt,inv_ntt}_layer_{2,3}_step` wrappers** in
  Vector.Portable + Vector.Avx2 cost ~36 s combined — Phase 7b agent
  F's forward layer 1 path is reflected here.
- **`Hacspec_ml_kem.Commute.Chunk`** has just 1 outlier each
  (#2 even base-case, #19 ntt-layer-1 lane bridge) — the Tier-2
  algebra dominates over everything else in that file.

### Bypass-during-experiment proposals

| Function | Today's strategy | Bypass during edit-iter |
|---|---|---|
| `invert_ntt_at_layer_4_plus` (#1) | rlimit 200 | wrap in `--admit_smt_queries true` while iterating on `_1`/`_2`/`_3` (saves ~32 s + retry costs per Invert_ntt build) |
| `ntt_at_layer_4_plus` (#3) | hint replay (some failures) | same admit pattern when iterating elsewhere in Ntt.fst |
| `lemma_base_case_mult_even_mod_core` (#2) | calc-style + rlimit 400 | leave as-is — once-and-done query |
| Polynomial reduce fns (#8, #12, #14, etc.) | strengthened by E2 / trackD | edit one at a time, admit the others |

---

## Snapshot 2 — 2026-04-28 afternoon — `Invert_ntt.fst.checked` build only (post-Step-4, tip `8358b1093`)

Source: `/tmp/inv_ntt_optB.log`.  Single-module rebuild after lane (a)
Step 4 strengthening landed.

| # | Total (s) | Max query (ms) | Queries | Failed | Function |
|---|---|---|---|---|---|
| 1 | 269.6 | 68995 | 464 | 0 | invert_ntt_at_layer_1_ |
| 2 | 222.7 | 28218 | 195 | 1 | invert_ntt_at_layer_4_plus |
| 3 | 2.1 | 1964 | 2 | 0 | invert_ntt_at_layer_2_ |
| 4 | 0.7 | 579 | 2 | 0 | invert_ntt_at_layer_3_ |
| 5 | 0.2 | 141 | 2 | 0 | invert_ntt_montgomery |

Total wall time: 528 s (8.8 min).

### Observations

- **`invert_ntt_at_layer_1_` blew up to 270 s** because of the
  strengthened post (rlimit 800, `--split_queries always`, 464 split
  queries).  Expected; this is the active edit.
- **`invert_ntt_at_layer_4_plus` is HALF the cost (223 s)** even when
  not edited.  Q2 fails at rlimit 200 ("canceled"), F* retries
  successfully.  This is the dominant baseline overhead in any
  Invert_ntt rebuild.  Hints don't help its borderline queries.
- **`_2`, `_3`, `_montgomery` replay in 3 s combined** — hint replay
  works fine for them.
- **Iteration speedup target**: bypassing `_4_plus` saves ~3.7 min
  per Invert_ntt rebuild.  For active work on layers 1/2/3 only, an
  `--admit_smt_queries true` wrap is a major savings.

### Open question

- Why does `invert_ntt_at_layer_4_plus` Q2 always fail under hint
  replay?  Either the hint is stale (proof structure changed since
  the hint was recorded) or the borderline rlimit doesn't tolerate
  hint cost.  Worth investigating once Phase 7a is closed —
  re-recording hints might recover the savings.

---

## Reducing F* iter-loop turnaround — proven techniques

Three orthogonal mechanisms.  Use them in this order of preference
(fastest first):

### α. fstar-mcp `typecheck_buffer` — sub-second feedback

Skip `make` entirely during inner-loop iteration on a single .fst file.
The fstar-mcp server (port 3001) holds a long-running F* session with
the file's deps already loaded; `typecheck_buffer` re-verifies the
buffer in sub-second wall time.  See memory `feedback_use_fstar_mcp.md`
and skill at `~/.claude/skills/fstar-mcp/`.

**When to use**: editing F* lemma bodies in `Hacspec_ml_kem.Commute.Chunk`
or `Hacspec_ml_kem.Commute.Bridges`; iterating on the body proof of a
single `.fst` after re-extracting once.

**When NOT to use**: after `python3 hax.py extract`, the .fst is
regenerated from Rust source — the fstar-mcp session's view of the .fst
becomes stale.  Need to `update_buffer` or re-create session.  For
edit-Rust-then-verify cycles, either still use fstar-mcp (refresh
buffer after each extract) or fall back to `make` (slower but clean).

### β. Per-function admit during iteration — `#[hax_lib::fstar::options("--admit_smt_queries true")]`

Apply on Rust-side functions you're NOT actively editing.  This injects
`#push-options "--admit_smt_queries true"` around that function's body
in the extracted .fst, so its proof obligations pass trivially.

**Saves ~222s per Invert_ntt rebuild** if applied to
`invert_ntt_at_layer_4_plus` while iterating on `_1`/`_2`/`_3` (per
Snapshot 2 above: 4_plus is half the wall cost when hint replay fails
on its borderline Q2).

**Pattern** (do NOT commit; revert before end-of-step verify):
```rust
#[hax_lib::fstar::options("--admit_smt_queries true")]  // TEMP — see Step 2 iter notes
pub(crate) fn invert_ntt_at_layer_4_plus<...>(...) { ... }
```

**Workflow**:
1. Add the attribute to the irrelevant fn(s) in `src/invert_ntt.rs`.
2. `python3 hax.py extract` (re-renders .fst).
3. Iterate via `make`/fstar-mcp on your target fn.
4. **Before commit**: remove the attribute, re-extract, run a clean
   `make` to confirm regression-clean.

### γ. Whole-module admit via `ADMIT_MODULES` Makefile var

Already used for `Libcrux_ml_kem.Ind_cpa.fst`, `Libcrux_ml_kem.Ind_cca.Unpacked.fst`,
and all `Vector.Neon.*` modules (per `Makefile:5-13`).

**When to consider adding more**: end-of-step regression checks where
a heavy module dirty-rebuilds despite not being on the active proof
path.  Likely candidates if needed:

- `Libcrux_ml_kem.Sampling.fst` (~1056 stats-lines in last full prove,
  one of the heaviest).  Not on the INTT critical path.
- `Libcrux_ml_kem.Serialize.fst` (~246 stats-lines).  Not on INTT path.
- `Libcrux_ml_kem.Ntt.fst` (forward NTT, ~630 stats-lines).  Not on
  the inverse-NTT path.

**Don't admit** on the active critical path (`Polynomial.fst`,
`Invert_ntt.fst`, `Vector.{Avx2,Portable}.fst`,
`Hacspec_ml_kem.Commute.{Chunk,Bridges}.fst`, `Vector.Traits.fst`).
Admit-during-debugging hides regressions in those.

### Recommended discipline for the INTT critical path (Steps 2-5)

| Phase | Best tool | Bypass |
|---|---|---|
| Step 2 layer 3 / 2 (Bridges.fst lemma writing) | fstar-mcp typecheck_buffer | n/a — Bridges.fst doesn't need Invert_ntt rebuilt |
| Step 3 layer 4_plus bridge (Bridges.fst) | fstar-mcp | n/a |
| Step 4 layer 2/3/4_plus Rust strengthening | `make Invert_ntt.fst.checked` | per-fn admit on the OTHER layers + `_montgomery` |
| Step 5 `invert_ntt_montgomery` post chain | `make` (no shortcuts; needs all layers) | none |
| End of each step | full `make` regression | remove all temp admits |

---

## Snapshot 2 — 2026-04-29 — Wave-B baseline (above-trait worktree, `fa31480cd`)

**Source:** `/tmp/wave-b-baseline-take3.log` (full make from
`~/libcrux-ml-kem-above-trait/libcrux-ml-kem/proofs/fstar/extraction/`).
**Wall:** ~9 min cold.  **Errors:** 0 (108 hint-replay warnings, all
F* auto-retried successfully — F* IDE sessions on Bridges.fst /
Ind_cpa.fst kept warm in source worktree concurrently).

### NOT directly comparable to Snapshot 1

Wave-B's local Makefile admits the entire below-trait surface
(`Vector.{Portable,Avx2}.*`) plus Wave-C's consumer chain (Matrix,
Ind_cca.*, Mlkem*).  Plus a TEMP admit on `Libcrux_ml_kem.Invert_ntt.fst`
because its `inv_ntt_layer_int_vec_step_reduce` Q101 saturates at
rlimit 200 in the without-hint retry path (hint-replay fails first,
then no-hint retry hits 200/200 used in 57 s).  Lane A5 will
UNADMIT Invert_ntt.fst when it begins (A5 owns this module per
wave-B-prompt §"WAVE-B SCOPE").

### Wave-B verification surface (top entries above 0.05 s)

| # | Total (s) | Max query (ms) | Queries | Failed | rlimit-sat | Module | Function |
|---|---|---|---|---|---|---|---|
| 1 | 4.9 | 4867 |  1 | 0 | 0 | Libcrux_ml_kem.Serialize | compress_then_serialize_message |
| 2 | 1.2 |  142 | 42 | 0 | 0 | Libcrux_ml_kem.Ntt | ntt_at_layer_4_plus |
| 3 | 1.2 | 1179 |  1 | 0 | 0 | Libcrux_ml_kem.Serialize | deserialize_to_reduced_ring_element |
| 4 | 1.0 |  966 |  1 | 0 | 0 | Libcrux_ml_kem.Serialize | deserialize_then_decompress_message |
| 5 | 0.5 |   50 | 16 | 0 | 0 | Libcrux_ml_kem.Polynomial | ntt_multiply |
| 6 | 0.4 |   28 | 17 | 0 | 0 | Libcrux_ml_kem.Ntt | ntt_at_layer_7_ |
| 7 | 0.3 |   64 | 11 | 0 | 0 | Libcrux_ml_kem.Polynomial | add_to_ring_element |
| 8 | 0.2 |  145 |  2 | 0 | 0 | Libcrux_ml_kem.Polynomial | multiply_by_constant_bounded |
| 9 | 0.1 |   28 |  6 | 0 | 0 | Libcrux_ml_kem.Polynomial | add_message_error_reduce |
| 10 | 0.1 |   25 |  6 | 0 | 0 | Libcrux_ml_kem.Polynomial | add_standard_error_reduce |
| 11 | 0.1 |   26 |  5 | 0 | 0 | Libcrux_ml_kem.Polynomial | add_error_reduce |

### Observations

- **`compress_then_serialize_message` 4.9 s, 1 query, max 4867 ms** —
  a single heavy Z3 problem.  Above-trait `Serialize.fst`; A1's Phase 7c
  migration touches this module.  Watch for regression when A1 adds
  hacspec citations.
- **`ntt_at_layer_4_plus` 1.2 s / 42 queries** vs Snapshot 1's 24.7 s /
  225 queries.  Hint replay is doing most of the work — most queries
  succeed immediately on hint match.  A5's strengthening work could
  invalidate these hints; A5 should expect rlimit-sat regressions
  when it touches Chunk.fst / Bridges.fst.
- **A3 targets all under 0.4 s** in the warm-cache state:
  `add_to_ring_element` 0.3 s, `add_message_error_reduce` 0.1 s,
  `add_standard_error_reduce` 0.1 s, `add_error_reduce` 0.1 s.
  USER-7's `subtract_reduce` is admitted via `--admit_smt_queries true`
  on the body (so no Query-stats reach the table).  When A3 unadmits
  the body, expect these 4 functions' Z3 cost to jump.
- **Hacspec_ml_kem.Commute.Chunk lemmas not in the table** — those live
  in `specs/ml-kem/proofs/fstar/commute/` (separate sub-Makefile), so
  Query-stats for them appear only when `make` is run from THAT dir.
  Wave-B's per-lane work needs to refresh that dir's perf data
  separately (or run with `--query_stats` from a top-level prove).

### Regression-watch thresholds for Wave-B

- **A1**: alert if `compress_then_serialize_message` total grows
  >7.4 s (1.5×) or its max query >7300 ms.  Other Serialize fns
  similarly.
- **A2**: Sampling.fst not currently in top-11 (warm-cache + lax
  bypasses); A2's `lax→panic_free` removal will introduce new
  Query-stats lines.  Establish per-fn baseline at A2 start.
- **A3**: alert if `add_*_reduce` family totals jump >0.5 s or any
  of them shows >5 saturated rlimit queries.  USER-7's
  `subtract_reduce` will appear in the table for the first time
  when A3 unadmits.
- **A5**: A5 unadmits Invert_ntt.fst.  Expect `inv_ntt_layer_int_vec_step_reduce`
  Q101 saturation to recur (this is the Step 5 spike target).
  Also watch `invert_ntt_at_layer_4_plus` (Snapshot 1: 31.9 s / 1
  failed query at rlimit 200) — currently bypassed via
  `--admit_smt_queries true` per `agent-trackA.md` "Layer 4_plus
  regression — diagnosis + landing decision".

---

## Snapshot 3 — 2026-04-29 — Wave-B 4-lane parallel merge (`tip TBD post-push`)

**Source:** `/tmp/wave-b-merged-baseline-take5.log` (full make from
`~/libcrux-ml-kem-above-trait/libcrux-ml-kem/proofs/fstar/extraction/`
post-merge of all 4 Wave-B lane branches + Makefile cleanup +
Phase 6d Neon `.fsti` admit + duplicate-`noeq` workaround on
regenerated Vector.Neon.Vector_type.fsti).
**Wall:** ~10 min cold.  **Errors:** 0.

### Wave-B parallel-fanout outcome

Lanes closed: A1 (-1, `to_unsigned_field_modulus`), A3 (-1 via
`subtract_reduce` body discharge with USER-7 array-form bridge fix
+ unshadowing trick).  Filed: A2 (USER-10 with smtprofiling-grade
4-path diagnostic), A5 (Steps 3.3/4/5 strengthened with USER-13/14/15
on bodies; layer_2 newly admitted as USER-13).  **Net admit-count
delta: -2 PROGRESS, +3 USER-N filings, 0 SIDEWAYS.**

### Top-20 culprits (post-merge)

| # | Total (s) | Max query (ms) | Queries | Failed | rlimit-sat | Module | Function |
|---|---|---|---|---|---|---|---|
| 1 | **153.6** | **153301** | 26 | 1 | 1 | Hacspec_ml_kem.Commute.Bridges | lemma_inv_ntt_layer_2_step_lane_bridge |
| 2 | 22.1 | 22139 |   1 |  0 |  0 | Libcrux_ml_kem.Vector.Portable.Arithmetic | to_unsigned_representative |
| 3 |  8.8 |  2592 | 110 |  0 |  0 | Libcrux_ml_kem.Polynomial | subtract_reduce |
| 4 |  8.7 |  2714 |  22 |  0 |  0 | Libcrux_ml_kem.Vector.Portable.Compress | decompress_1_ |
| 5 |  4.8 |  4804 |   1 |  0 |  0 | Libcrux_ml_kem.Serialize | compress_then_serialize_message |
| 6 |  4.0 |  4028 |   1 |  0 |  0 | Libcrux_ml_kem.Vector.Avx2 | op_serialize_4_post_bridge |
| 7 |  3.9 |   142 | 121 |  0 |  0 | Libcrux_ml_kem.Invert_ntt | invert_ntt_at_layer_1_ |
| 8 |  3.0 |  3037 |   1 |  0 |  0 | Libcrux_ml_kem.Vector.Avx2 | impl_3 |
| 9 |  2.2 |   736 |  43 |  0 |  0 | Libcrux_ml_kem.Invert_ntt | inv_ntt_layer_int_vec_step_reduce |
| 10 | 1.5 | 1546 |   1 |  0 |  0 | Libcrux_ml_kem.Vector.Portable | impl_1 |
| 11 | 1.4 | 1383 |   1 |  0 |  0 | Libcrux_ml_kem.Vector.Portable.Arithmetic | multiply_by_constant |
| 12 | 1.2 |  145 |  42 |  0 |  0 | Libcrux_ml_kem.Ntt | ntt_at_layer_4_plus |
| 13 | 1.2 | 1174 |   1 |  0 |  0 | Libcrux_ml_kem.Vector.Avx2 | op_serialize_4_pre_bridge |
| 14 | 1.1 | 1099 |   1 |  0 |  0 | Libcrux_ml_kem.Serialize | deserialize_to_reduced_ring_element |
| 15 | 0.9 |   33 |  38 |  0 |  0 | Libcrux_ml_kem.Invert_ntt | invert_ntt_at_layer_3_ |
| 16 | 0.9 |  897 |   2 |  0 |  0 | Libcrux_ml_kem.Vector.Avx2 | op_serialize_11_post_bridge |
| 17 | 0.9 |  876 |   1 |  0 |  0 | Libcrux_ml_kem.Vector.Portable.Compress | compress_message_coefficient |
| 18 | 0.9 |  875 |   1 |  0 |  0 | Libcrux_ml_kem.Serialize | deserialize_then_decompress_message |
| 19 | 0.6 |  645 |   1 |  0 |  0 | Libcrux_ml_kem.Vector.Avx2 | op_deserialize_4_post_bridge |
| 20 | 0.6 |  622 |   1 |  0 |  0 | Libcrux_ml_kem.Vector.Avx2 | op_serialize_10_post_bridge |

### Major regression — needs investigation

**`lemma_inv_ntt_layer_2_step_lane_bridge` jumped 3.4 s → 153.6 s**
(Snapshot 1 → Snapshot 3, 45×).  1 query failed (presumably hint
replay miss → without-hint retry succeeded after 153 s); 1 query
saturated rlimit.  Likely cause: A5's new helpers in `Chunk.fst`
(Phase 7a / lane A5 additions section + parameter unshadowing) plus
A3's array-form lemmas changed the dependency graph hashes, so the
old `Bridges.fst` hint cache no longer replays.

**Recommendation for next session:** re-record hints for Bridges.fst
(`make check/Hacspec_ml_kem.Commute.Bridges.fst` once with
`--record_hints`, then commit hints).  This should drop the 153 s
back to ~3-5 s.

### Other notable changes vs Snapshot 1

- `to_unsigned_representative` 8.5 s → 22.1 s (2.6×) — same hint
  cache invalidation pattern; A1's removal of `panic_free` from its
  caller `to_unsigned_field_modulus` means the caller now propagates
  the trait post into Serialize, which routes through this fn.
- `subtract_reduce` 5.1 s → 8.8 s — A3's body now actually verifies
  (was admitted in Snapshot 1).  Net benefit: -1 admit; 1.7× cost is
  acceptable.
- `compress_then_serialize_message` 4.9 s → 4.8 s — flat, A1's
  closure didn't perturb this consumer.
- `Vector.Avx2.op_serialize_*_bridge` family appears for the first
  time at 0.5-4.0 s — these are the bridges B3 closed in the
  parallel below-trait session at `e5c4a6f49`.  Genuine new
  verification work, not regressions.

### Wave-B local Makefile workaround (2026-04-29)

Wave-B's local Makefile in `~/libcrux-ml-kem-above-trait/` was
accidentally committed by lane A5 (`aae3046a9`) and reverted by the
coordinator (`7e75d3d7c`).  The local Makefile remains in the
worktree (uncommitted) for future sessions to reuse.  Phase 6d
`.fsti` admit (`22b5c016e`) is upstream-clean and committed.

### hax codegen bug — duplicate `noeq` on Vector_type.fsti

`hax extract` regenerates `Libcrux_ml_kem.Vector.Neon.Vector_type.fsti`
with TWO `noeq` qualifiers on `t_SIMD128Vector` (Error 162 at line
10-13 — "Duplicate qualifiers").  Workaround applied LOCALLY in
above-trait's gitignored .fsti via `sed`.  Source worktree avoids
this because its `src/vector/neon/vector_type.rs` has uncommitted
edits that produce a different .fsti shape.  **File as USER-N:**
hax codegen bug; track separately from the F* verification work.
