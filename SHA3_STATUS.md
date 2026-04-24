# SHA-3 Proofs — Current Status

Quick status pointer. Full details in
`crates/algorithms/sha3/proofs/fstar/equivalence/HANDOFF.md`.

## Current focus (2026-04-24 late evening)

Task: eliminate the remaining Arm64 admits via the inline-ensures
pattern pioneered on the Portable backend.

**Status: absorb2 DONE.**  `Libcrux_sha3.Generic_keccak.Simd128.absorb2`
now verifies against a per-lane spec-equivalence ensures inline (no
admit).  `lemma_absorb2_arm64` in `EquivImplSpec.Sponge.Arm64.API.fst`
collapsed to a one-liner consuming the Rust ensures.  Load-bearing
admit count: **1** (was 2, was 3 earlier this session).

**Remaining:** `lemma_squeeze2_arm64` (at
`EquivImplSpec.Sponge.Arm64.API.fst:82`).  Mirrors Portable squeeze at
N=2; will likely need an analogous `squeeze_last2` helper method on
`KeccakState<2, _uint64x2_t>` to keep the final-block VC tractable
(Portable session notes flagged this as the specific trick that broke
the VC timeout).

## Verification sanity — full build is GREEN

Full `make verify` under
`crates/algorithms/sha3/proofs/fstar/equivalence/` passes cleanly
(`exit 0`), verifying **all 16 modules** of the proof chain
(portable + Arm64 + generic). See `/tmp/verify_full2.log`.

Arm64 extraction drift has been resolved: the hax extraction of the
intrinsics crate must use `--features simd128` so that
`arm64_extract` is compiled and the `bit_vec`-typed stubs
(`t_e_uint64x2_t` etc.) are emitted into
`Libcrux_intrinsics.Arm64_extract.fsti`.  This was missing from the
default `cargo hax into fstar` invocation.

## Files touched this session

- `specs/sha3/src/sponge.rs` — added `absorb_blocks` helper.
- `crates/algorithms/sha3/src/generic_keccak/portable.rs` — added
  inline ensures + loop invariant to `absorb`.
- `crates/algorithms/sha3/proofs/fstar/equivalence/Hacspec_sha3.Sponge.Lemmas.fst`
  — added 8 lemmas for absorb_blocks + the bridge to absorb_rec.
- `crates/algorithms/sha3/proofs/fstar/equivalence/EquivImplSpec.Sponge.Portable.API.fst`
  — deleted dead aux helpers; `lemma_absorb_portable` collapses to
  one line.
- `crates/algorithms/sha3/proofs/fstar/equivalence/HANDOFF.md`
  — documented the elimination.
- (Regenerated, not hand-edited) Extracted F* files under
  `crates/algorithms/sha3/proofs/fstar/extraction/` and
  `specs/sha3/proofs/fstar/extraction/`.

## Logs of interest

- `/tmp/verify_portable1.log` — Portable.fst verification (497
  queries, 0 failures, ~6.4 min).
- `/tmp/verify_lemmas6.log` — Sponge.Lemmas verification.
- `/tmp/verify_api2.log` — final collapsed API verification.
- `/tmp/verify_full.log` — latest full make run.

## Load-bearing admit inventory

| # | File | Line | Kind |
|---|------|------|------|
| 1 | `EquivImplSpec.Sponge.Arm64.API.fst` | 63 | `assume val lemma_absorb2_arm64` |
| 2 | `EquivImplSpec.Sponge.Arm64.API.fst` | 82 | `assume val lemma_squeeze2_arm64` |

Non-load-bearing upstream admits (3) remain in
`Proof_Utils.Lemmas.fst:26/33/54` (hax-lib / core-models targets).
