# Appendix (hand-written; appended by generate_verification_status.py)

## Coverage boundaries

ML-DSA is a work in progress. The arithmetic core (NTT/inverse-NTT, Montgomery/Barrett,
decompose/`make_hint`/`use_hint`) and the (de)serialization bounds are functionally correct against
`Hacspec_ml_dsa`, and essentially the whole API is panic-free. Not yet covered by functional
correctness (per-function tiers are in the tables above):

- **Top-level API — panic-free, FC admitted.** The public `sign`/`verify`/`generate_key_pair`
  (`ml_dsa_generic`) are proven panic-free, but their functional-correctness `ensures` are
  **admitted** — the end-to-end FIPS-204 equivalence theorem is not yet closed. The admitted sites
  are the *Body-admit sites* in the body above.
- **Lax and Unverified:** the `sample` rejection-sampling `lax` markers (unbounded loops,
  probabilistic termination — trusted by design) and `src/simd/tests.rs` test functions (not
  extracted), both listed in the body above.

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
