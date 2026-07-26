# Appendix (hand-written; appended by generate_verification_status.py)

## Proof times

The ml-kem proof sources (src annotations, `proofs/fstar/spec/` companions,
committed hints) are byte-identical to the campaign state at `6584a585c`, so
the campaign's timing data remains authoritative. Headline numbers (Apple
Silicon, serial builds, committed hints via `--use_hints`):

- Full ml-kem F* closure: ~22 min of Z3 wall cold (2026-05 cold baseline);
  ~6–13 min for full `make` gates warm with committed hints.
- Heaviest single queries: `Vector.Avx2.Serialize.deserialize_5_` (~35 s),
  the portable `op_{ntt,inv_ntt}_layer_{2,3}_step` wrappers (50–70 s each
  cold at rlimit 600/800), and the `Hacspec_ml_kem.Commute.*` NTT bridge
  lemmas (`lemma_intra_vec_per_coeff` ~224 s in incremental gates).
- Warm incremental `make all` gates run ~1–13 min depending on which cone a
  change invalidates.

Detailed per-function top-20/25 tables are tracked in the engineering log
(`fstar-perf-top20.md`, snapshots through 2026-07); regenerate after any full
cold build by aggregating `Query-stats` lines from the build log.
