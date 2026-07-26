# Appendix (hand-written; appended by generate_verification_status.py)

## Proof times

The ml-dsa proof sources (src annotations, `proofs/fstar/spec/` companions,
committed hints) are byte-identical to the campaign state at `6584a585c`, so
the campaign's timing data remains authoritative. Headline numbers (Apple
Silicon, serial builds, committed hints via `--use_hints`):

- Full ml-dsa F* closure: on the order of 1–2 hours cold; minutes warm with
  the committed hints and a seeded `.checked` cache.
- Heaviest module: `Libcrux_ml_dsa.Simd.Avx2.Invntt` — ~8.4 min for a clean
  single-module re-verify with committed hints (2026-07-25 spot-check on the
  merge branch; down from ~311 min pre-`#restart-solver` restructure, see the
  per-decl `#restart-solver` campaign note).
- The `--z3refresh`/`--split_queries always` declaration set (~7% of decls)
  dominates build wall (~68%): the AVX2/portable NTT and inverse-NTT layer
  proofs, `sign_internal`/`verify_internal` composition, and the encoding
  serializers.

Detailed per-function top-20 tables are tracked in the engineering log
(`fstar-perf-top20.md`, snapshots through 2026-07); regenerate after any full
cold build by aggregating `Query-stats` lines from the build log.
