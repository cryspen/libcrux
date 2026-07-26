# Appendix (hand-written; appended by generate_verification_status.py)

## Deferred SIMD store_block proofs

During the 2026-07 merge of upstream `main` into the proofs line, upstream
flattened `src/simd/{arm64,avx2}/` — the campaign's proven submodule tree
(load/store/wrappers, including the ~2,200-line opaque-range `store_block`
proofs) — into single ~200-line impl modules without proof annotations, and
dropped the SIMD equivalence contracts from `generic_keccak/simd{128,256}.rs`
and the Hacspec ensures from the Neon/AVX2 top-level APIs. The campaign's SIMD
proofs (fully verified at campaign tip `6584a585c`) target the old module
structure and need rework before they can re-attach.

Until that rework lands, the following are **documented trust obligations**:

- `proofs/fstar/extraction/Makefile` `ADMIT_MODULES` (each carries a
  `# trusted-module:` mirror):
  - `Libcrux_sha3.Simd.Arm64`, `Libcrux_sha3.Simd.Avx2` — main's flat SIMD
    impls, unproven;
  - `Libcrux_sha3.Generic_keccak.Simd128`, `Libcrux_sha3.Generic_keccak.Simd256`
    — `keccak2`/`keccak4` carry runtime `assert!` obligations that the campaign
    discharged via contracts citing the deferred SIMD equivalence stack.
- Trusted posts on admitted functions: `keccak2`/`keccak4` length preservation
  (justification comments at the functions; proven by the campaign for the
  structured predecessor code).
- `proofs/fstar/equivalence/Makefile` `ROOTS` is portable-only: the SIMD
  equivalence modules (`EquivImplSpec.Correctness.{Avx2,Neon}`,
  `EquivImplSpec.Keccakf.{Arm64,Avx2}`, `EquivImplSpec.Sponge.{Arm64,Avx2}.*`)
  are removed from the build but remain tracked for the rework.
- The hand-written `Libcrux_sha3.Simd.{Arm64,Avx2}.StoreBlockHelpers` modules
  are excluded from the extraction ROOTS (tracked; cited only by the deferred
  proofs).

**What remains verified:** the portable path end-to-end — keccak-f, sponge,
portable API and incremental API — including the `EquivImplSpec.*` functional
correctness equivalence against the `Hacspec_sha3` spec; and the SIMD
incremental API wrappers' length contracts against the proven generic keccak
state machine (the `Simd.*` bodies themselves remain admitted).

**Recovery path:** rework the opaque-range store_block proofs onto main's
flattened simd modules, re-add the `generic_keccak/simd{128,256}` contracts and
the Neon/AVX2 API Hacspec ensures, re-enable the SIMD equivalence ROOTS, and
empty `ADMIT_MODULES`.

Note on the summary table: the "Unverified (not extracted)" count includes
the orphaned campaign proof-helper submodules under `src/simd/{arm64,avx2}/`
(load/store/wrappers) — they are not compiled into the crate (main's flat
`simd/{arm64,avx2}.rs` replaced them) and are retained in-tree only as the
starting point for the store_block rework; and the "Lax" count is exactly the
four deferred ADMIT modules above.

The sha3 trust-ledger baseline was regenerated to record this surface — a
documented, bounded exception to the monotonic-non-increase rule (SIMD
deferral chosen 2026-07-25).

## Proof times

Per-module F* verification wall time for the post-merge portable
verification (2026-07-26, Apple Silicon, serial `make -j2`, committed hints
via `--use_hints`). Times are each module's slowest observed re-verify across
the merge-adaptation builds (cold-ish; warm cache-hit revalidation is ~0.5 s
per module). Modules not listed verified in under ~1.5 s.

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
|  5.7 | Libcrux_sha3.Simd.Avx2 (admitted, typecheck only) |
|  4.1 | Libcrux_sha3.Traits |
|  3.9 | EquivImplSpec.Sponge.Generic.Core |
|  3.1 | EquivImplSpec.Correctness.Portable (top theorems) |

Full portable closure (extraction + equivalence sub-builds) completes in
roughly 5–6 minutes cold with committed hints, ~40 s warm.
