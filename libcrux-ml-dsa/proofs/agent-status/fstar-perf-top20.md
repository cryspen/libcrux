# F* verification time — top-20 culprits

This file tracks the slowest F* verification queries observed during
ML-DSA proof builds.  Updated after each significant build (full
`./hax.sh prove` or repo-wide `make`).  Snapshots are appended; do
not delete prior entries — diffs across snapshots reveal regressions
and improvements.

**Producer:** `./extract-fstar-perf.sh [N=20] [LOG=../verification_result.txt]`
parses `Query-stats` lines from a build log and emits two ranked
tables (per-function totals, per-module totals).  Run after a full
build and paste the output below as a new dated snapshot.

**Why we track this:** F* verification time is the sprint-deadline
threat.  A full prove on this repo is dominated by a small number of
borderline queries (NTT-layer butterflies, decompose mask logic,
montgomery_reduce_element).  Knowing the top 20 lets us:
- (a) optimize the proofs that matter (factor lemmas, tighter bounds,
  per-iteration unfolds, lower fuel/ifuel),
- (b) bypass them with `#push-options "--admit_smt_queries true"`
  during experiments where they're not the focus,
- (c) catch regressions — a function that climbs from #15 to #2
  between snapshots is either a real proof breakage or a hint-cache
  miss that needs `--record_hints`.

Cap: keep at most the most recent ~10 snapshots; older entries can
be moved to `fstar-perf-top20.archive.md` if the file gets long.

---

## Snapshot 2026-04-28 (Step 9 mid-cascade, partial)

Source: `/tmp/sltr-portable.log` (in-flight Portable rebuild for
shift_left_then_reduce; cascade from `Specs.fst` change still
re-verifying NTT/Invntt; Avx2 modules not yet reached).

**Caveat:** this is a *partial* sample (~100s Z3 time across 25 fns
in 3 Portable modules).  A full snapshot needs a complete
`./hax.sh prove` post-cascade.

### Top-20 per-function totals

| # | Function | Module | total (s) | max query (ms) | queries | flags |
|---|---|---|---:|---:|---:|---|
| 1 | `ntt_at_layer_3_` | `L_md.Simd.Portable.Ntt` | 68.33 | 8285 | 36 | — |
| 2 | `ntt_at_layer_0_` | `L_md.Simd.Portable.Ntt` | 4.84 | 170 | 64 | — |
| 3 | `ntt_at_layer_4_` | `L_md.Simd.Portable.Ntt` | 4.40 | 892 | 20 | — |
| 4 | `invert_ntt_at_layer_0_` | `L_md.Simd.Portable.Invntt` | 4.39 | 156 | 64 | — |
| 5 | `decompose_element` | `L_md.Simd.Portable.Arithmetic` | 4.12 | 292 | 18 | — |
| 6 | `ntt_at_layer_1_` | `L_md.Simd.Portable.Ntt` | 3.61 | 117 | 64 | — |
| 7 | `invert_ntt_at_layer_1_` | `L_md.Simd.Portable.Invntt` | 3.39 | 120 | 64 | — |
| 8 | `ntt_at_layer_2_` | `L_md.Simd.Portable.Ntt` | 2.87 | 99 | 64 | — |
| 9 | `invert_ntt_at_layer_2_` | `L_md.Simd.Portable.Invntt` | 2.71 | 89 | 64 | — |
| 10 | `outer_3_plus` | `L_md.Simd.Portable.Invntt` | 0.25 | 30 | 13 | — |
| 11 | `ntt_at_layer_5_` | `L_md.Simd.Portable.Ntt` | 0.23 | 35 | 11 | — |
| 12 | `power2round_element` | `L_md.Simd.Portable.Arithmetic` | 0.20 | 46 | 5 | — |
| 13 | `get_n_least_significant_bits` | `L_md.Simd.Portable.Arithmetic` | 0.19 | 32 | 13 | — |
| 14 | `outer_3_plus` | `L_md.Simd.Portable.Ntt` | 0.14 | 25 | 8 | — |
| 15 | `uuse_one_hint` | `L_md.Simd.Portable.Arithmetic` | 0.09 | 46 | 2 | — |
| 16 | `ntt_at_layer_6_` | `L_md.Simd.Portable.Ntt` | 0.06 | 17 | 5 | — |
| 17 | `simd_unit_ntt_at_layer_0_` | `L_md.Simd.Portable.Ntt` | 0.06 | 39 | 3 | — |
| 18 | `outer_3_plus__round` | `L_md.Simd.Portable.Ntt` | 0.05 | 18 | 4 | — |
| 19 | `simd_unit_invert_ntt_at_layer_0_` | `L_md.Simd.Portable.Invntt` | 0.05 | 37 | 3 | — |
| 20 | `simd_unit_ntt_at_layer_2_` | `L_md.Simd.Portable.Ntt` | 0.05 | 10 | 6 | — |

### Top module totals

| # | Module | total (s) | functions tracked |
|---|---|---:|---:|
| 1 | `L_md.Simd.Portable.Ntt` | 84.68 | 14 |
| 2 | `L_md.Simd.Portable.Invntt` | 10.86 | 7 |
| 3 | `L_md.Simd.Portable.Arithmetic` | 4.61 | 4 |

_Sample size: 549 Query-stats lines, 100s total Z3 time, across 25
functions in 3 modules.  Partial; full snapshot pending end-of-cascade._

### Notes / actions

1. **`ntt_at_layer_3_` dominates** — 68 s alone, max single query
   8.3 s.  This is 81% of all observed Z3 time in this slice.
   Optimization candidates (in order of effort): (a) split the
   function body into 4 per-zeta sub-functions to localize the wide
   context; (b) drop fuel from 0 to 0/ifuel 0; (c) factor any
   intermediate `assert (forall i. ...)` into a separate lemma so
   Z3 sees the conclusion at function-level without re-deriving.
2. **NTT layers 0-2 have stable budgets** (~3-5 s each, 64 queries) —
   suggests these are at a good local optimum; layer 3 is the
   outlier.
3. **`decompose_element`** comes in at 4.1 s — non-NTT but high.
   Worth checking if the corner-case `mask` reasoning could factor
   into a sub-lemma.
4. The current verification_result.txt at repo root is mostly
   ADMIT-mode emissions (no Query-stats) so this snapshot draws from
   the in-flight cascade log instead.

---

<!-- Append future snapshots above this comment. -->
