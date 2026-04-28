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
