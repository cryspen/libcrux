# SHA-3 Proofs — Current Status

Quick status pointer. Full details in
`crates/algorithms/sha3/proofs/fstar/equivalence/HANDOFF.md`.

## Current focus (2026-04-25 PM)

**AVX2 extraction enabled, mirroring the arm64 plumbing.**
`hax.sh extract` now emits `Libcrux_sha3.Simd.Avx2`,
`Libcrux_sha3.Generic_keccak.Simd256`, `Libcrux_sha3.Avx2.X4`, and
`Libcrux_sha3.Avx2.X4.Incremental` using the bit_vec stub
(`Libcrux_intrinsics.Avx2_extract`).  All four lax-typecheck cleanly
when F* is invoked directly.  See HANDOFF "2026-04-25 (afternoon)"
section for plumbing details and next steps for AVX2 equivalence
proofs.

## Earlier focus (2026-04-25)

Task: eliminate `lemma_squeeze2_arm64` via the inline-ensures pattern
(pioneered on Portable).  **Attempted and reverted — see HANDOFF.md
"2026-04-25" section for full analysis.**

**Status: 1 load-bearing admit** (unchanged from 2026-04-24
late-evening state).  absorb2 remains DONE; squeeze2 still relies on
the `assume val lemma_squeeze2_arm64` at
`EquivImplSpec.Sponge.Arm64.API.fst:~63`.

**2026-04-25 finding:** The squeeze2 inline-ensures proof hits a
400k-instantiation BoxBool/BoxInt Z3 cascade on one loop-invariant
re-establishment query.  Arm64 squeeze2 is genuinely harder than
Portable squeeze because (a) 4 forall conjuncts in the loop invariant
vs 2, (b) `f_squeeze2` writes both out0/out1 from one call, so
`sq_lane_arm64` threads a disjunction through the byte-bridge hot
path.  Profile captured via `z3 smt.qi.profile=true` on the slow
`.smt2`.  Paths forward documented in HANDOFF (Options A–D:
`introduce forall`, per-lane Steps lemmas, opaque bundles, or
`Seq.slice`-based loop-invariant rewrite).

Two clean helper lemmas added to
`proofs/fstar/equivalence/Hacspec_sha3.Sponge.Lemmas.fst` for reuse
when the main proof is attempted again:
`lemma_squeeze_state_byte_eq_in_range` and
`lemma_squeeze_state_byte_preserve`.

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
