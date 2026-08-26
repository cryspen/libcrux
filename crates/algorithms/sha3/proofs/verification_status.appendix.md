# Appendix (hand-written; appended by generate_verification_status.py)

## Coverage boundaries

All three backends (Portable, Neon, AVX2) are fully verified: `ADMIT_MODULES` is empty, and the
`EquivImplSpec.*` functional-correctness equivalence against `Hacspec_sha3` holds for the one-shot
hashing APIs on every backend. Two deliberate boundaries remain (per-function tier counts are in
the auto-generated body above and not repeated here):

- **Unverified — the `Digest`-trait glue.** `src/impl_digest_trait.rs`
  (`new`/`reset`/`update`/`finish`/`hash`) is the RustCrypto `Digest`/`Hasher` wrapper layer. It is
  filtered out of hax extraction (`-i -…::**`), so it has no F\* proof at any tier — it is thin
  dispatch over the verified one-shot/incremental core.
- **Incremental APIs — panic-free, not spec-equivalent.** The streaming absorb/squeeze paths
  (all backends) are proven panic-free with state-machine invariants, but not yet proven equal to
  `Hacspec_sha3`. That incremental-sponge ≡ spec refinement is the genuine remaining
  functional-correctness work.

## Proof times

Dated snapshot (2026-07-26, Apple Silicon, serial `make -j2`, committed hints via `--use_hints`),
measured during the portable-era build **before** SIMD verification landed — so the SIMD rows are
stale (e.g. AVX2 was typecheck-only then). Refresh by aggregating `Query-stats` from a full cold
build. Each module's slowest observed re-verify; modules not listed verify in under ~1.5 s.

| Time (s) | Module |
|---:|---|
| 96.1 | Libcrux_sha3.Generic_keccak.Portable (absorb/squeeze FC bodies) |
| 92.5 | EquivImplSpec.Keccakf.Generic |
| 89.3 | Libcrux_sha3.Generic_keccak.Xof.Bundle |
| 34.7 | Libcrux_sha3.Simd.Portable (load/store per-byte proofs) |
| 20.3 | Libcrux_sha3.Generic_keccak |
| 20.0 | Libcrux_sha3 (API dispatch) |
| 19.2 | EquivImplSpec.Sponge.Portable |
| 18.2 | EquivImplSpec.Sponge.Portable.Steps |
| 17.2 | EquivImplSpec.Keccakf.ChiFold |
| 17.1 | EquivImplSpec.Sponge.Portable.SqueezeAPI |
| 14.7 | Libcrux_sha3.Portable.Incremental.Bundle |
|  4.1 | Libcrux_sha3.Traits |
|  3.9 | EquivImplSpec.Sponge.Generic.Core |
|  3.1 | EquivImplSpec.Correctness.Portable (top theorems) |
