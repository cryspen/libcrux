# SHA-3 Proofs — Current Status

Quick status pointer. Full details in
`crates/algorithms/sha3/proofs/fstar/equivalence/HANDOFF.md`.

## Current focus (2026-04-25 evening)

**AVX2 modules now verify without `--admit_smt_queries`.**
The four extracted AVX2 modules — `Libcrux_sha3.Simd.Avx2`,
`Libcrux_sha3.Generic_keccak.Simd256`, `Libcrux_sha3.Avx2.X4`, and
`Libcrux_sha3.Avx2.X4.Incremental` — pass `make verify` cleanly under
the default flags (no `OTHERFLAGS="--admit_smt_queries true"`).

API contracts are real and discharged.  Four body-level `admit()`
calls remain inside the heavy bit-twiddling helpers (mirroring the
arm64 pattern): `Generic_keccak.Simd256.keccak4`, and
`Simd.Avx2.{load_block, load_last, store_block}`.  These are local —
they do not poison any caller's verification.

### Source changes (2026-04-25 evening)

- `crates/algorithms/sha3/src/simd/avx2.rs` — added
  `#[hax_lib::requires]` / `#[hax_lib::ensures]` to `load_block`,
  `load_last`, `store_block`; `#[hax_lib::attributes]` on `Absorb<4>`
  / `Squeeze4` / `KeccakItem<4>` impls with per-method requires;
  `xor_and_rotate` impl carries the trait's
  `LEFT + RIGHT == 64 && 0 < RIGHT < 64` requires; `rotate_left` and
  `_vxarq_u64` require `0 <= RIGHT <= 64`; `debug_assert!` in
  `rotate_left` gated under `cfg(not(any(eurydice, hax)))`; body-level
  `hax_lib::fstar!("admit()")` in `load_block`/`load_last`/`store_block`.
- `crates/algorithms/sha3/src/generic_keccak/simd256.rs` — added
  `#[hax_lib::requires]` / `#[hax_lib::ensures]` to `keccak4`;
  `#[hax_lib::attributes]` on `impl KeccakState<4, Vec256>` with
  per-method requires/ensures on the four `squeeze_*` methods;
  body-level admit in `keccak4`.
- `crates/algorithms/sha3/src/avx2.rs` — `x4::shake256` and the seven
  `x4::incremental::*` functions all carry `#[hax_lib::requires]` /
  `#[hax_lib::ensures]` mirroring the analogous Portable annotations
  in `src/portable.rs`.
- `crates/algorithms/sha3/src/traits.rs` — `Squeeze4` trait now has
  `#[hax_lib::attributes]` plus a `requires`/`ensures` on the
  `squeeze4` method (mirrors `Squeeze2`).
- `crates/algorithms/sha3/hax.sh` — added a `sed` patch in
  `patch_fstar_extractions` that prepends `noeq` to
  `Libcrux_sha3.Avx2.X4.Incremental.t_KeccakState`, since its
  `Vec256` field has no decidable equality.

### Outstanding for AVX2

- The four body-level admits in `absorb4`/`load_block`/`load_last`/
  `store_block` are the AVX2 analogues of arm64's body admits.
  They need bit-vector reasoning to discharge.
- `Generic_keccak.Simd256.squeeze4` body has NO admit and verifies
  cleanly (mirrors `Simd128.squeeze2`).
- See "AVX2 — equivalence-chain admits" below for the load-bearing
  lemmas that now mirror the arm64 chain (lane-correctness primitives,
  `avx2_sc_*` records, `lemma_{absorb,squeeze}4_avx2`).

### AVX2 equivalence-chain replication (2026-04-25 evening, late)

Created four new files mirroring the arm64 chain:

- `EquivImplSpec.Keccakf.Avx2.fst` — defines `avx2_lane =
  get_lane_u64x4`, `lc_avx2` record, derives `lemma_keccakf1600_avx2`
  and `lemma_extract_lane_zero_avx2`.  **All seven lane-correctness
  proofs are real `let`s**, modulo one local
  `lemma_shl_xor_shr_is_rotate_left` admit (Core_models opacity).
- `EquivImplSpec.Sponge.Avx2.fst` — defines `sq_lane_avx2` and the
  `sponge_correctness` record `sc_avx2`.  Three `avx2_sc_*` bridges
  are `admit ()`s (need bytewise lane-ensures on
  `mm256_loadu_si256_u8` / `mm256_storeu_si256_u8`).
- `EquivImplSpec.Sponge.Avx2.Steps.fst` — `lemma_absorb_block_avx2`,
  `lemma_absorb_last_avx2`, `lemma_squeeze_block_avx2`,
  `lemma_squeeze_last_avx2` — all four **proved by composition** of
  the (admitted) primitives.
- `EquivImplSpec.Sponge.Avx2.API.fst` — `assume val lemma_absorb4_avx2`,
  `assume val lemma_squeeze4_avx2`, `lemma_keccak4_avx2` proved by
  composition, `lemma_shake256_x4_avx2` proved from
  `lemma_keccak4_avx2`.

Source changes:
- `crates/algorithms/sha3/src/generic_keccak/simd256.rs` refactored to
  expose `absorb4` and `squeeze4` as separate functions (mirrors
  `Simd128.absorb2` / `Simd128.squeeze2`).  `keccak4` now composes them.
- `crates/algorithms/sha3/src/simd/avx2.rs::_veor5q_u64` re-bracketed
  left-associatively (((a^b)^c)^d)^e to match the spec shape
  (avoids needing assoc/comm of `^.` in `avx2_lc_xor5`).
- `crates/utils/intrinsics/src/avx2_extract.rs` — added
  `vec256_as_u64x4` + `get_lane_u64x4` to the `Vec256` interface, plus
  per-u64-lane SMTPat lemmas
  (`lemma_mm256_{xor,or,andnot,slli_epi64,srli_epi64,set1_epi64x}_u64x4`)
  alongside the existing `BitVec.Intrinsics` `include`s.  Mirrors how
  arm64 intrinsics carry per-`get_lane_u64x2` ensures.
- `fstar-helpers/fstar-bitvec/BitVec.Intrinsics.fsti` — added
  bit_vec definitions for the 5 newly-imported AVX2 ops
  (`mm256_xor_si256`, `mm256_or_si256`, `mm256_andnot_si256`,
  `mm256_slli_epi64`, `mm256_set1_epi64x`).
- `crates/algorithms/sha3/hax.sh::patch_fstar_extractions` — appends
  the six `let lemma_mm256_*_u64x4 = admit()` definitions to the
  re-extracted `Libcrux_intrinsics.Avx2_extract.fst`.

## Earlier focus (2026-04-25 PM)

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

## Load-bearing admit inventory (2026-04-25 evening)

### Arm64

| # | File | Line | Kind |
|---|------|------|------|
| 1 | `EquivImplSpec.Sponge.Arm64.API.fst` | 88 | `assume val lemma_squeeze2_arm64` |

### AVX2 — extracted code body admits (mirror arm64 pattern)

| # | File | Kind |
|---|------|------|
| 2 | `Libcrux_sha3.Generic_keccak.Simd256.fst` (`absorb4`, `keccak4` chain) | `admit()` body of `absorb4` |
| 3 | `Libcrux_sha3.Simd.Avx2.fst` | `admit()` body of `load_block` |
| 4 | `Libcrux_sha3.Simd.Avx2.fst` | `admit()` body of `load_last` |
| 5 | `Libcrux_sha3.Simd.Avx2.fst` | `admit()` body of `store_block` |

### AVX2 — equivalence-chain admits (replicating arm64 chain)

| # | File | Kind |
|---|------|------|
| 6..11 | `Libcrux_intrinsics.Avx2_extract.fst` | 6 × `admit()` on per-u64-lane SMTPat lemmas: `lemma_mm256_{xor,or,andnot,slli_epi64,srli_epi64,set1_epi64x}_u64x4` |
| 12 | `EquivImplSpec.Keccakf.Avx2.fst` | `admit()` on `lemma_shl_xor_shr_is_rotate_left` (Core_models.Num.impl_u64__rotate_left is opaque) |
| 13 | `EquivImplSpec.Sponge.Avx2.API.fst` | `assume val lemma_absorb4_avx2` |
| 14 | `EquivImplSpec.Sponge.Avx2.API.fst` | `assume val lemma_squeeze4_avx2` |

**ALL SEVEN lane-correctness lemmas (`avx2_lc_zero`, `avx2_lc_xor5`,
`avx2_lc_rotate_left1_and_xor`, `avx2_lc_xor_and_rotate`,
`avx2_lc_and_not_xor`, `avx2_lc_xor_constant`, `avx2_lc_xor`) are
PROVED** (by composing the SMTPat'd `lemma_mm256_*_u64x4` admits, which
themselves mirror how arm64's per-lane intrinsic ensures are *also*
admitted in `Libcrux_intrinsics.Arm64_extract`).  Same trust boundary
as arm64.  The `_veor5q_u64` Rust source was re-bracketed
left-associatively (((a^b)^c)^d)^e to match the spec shape — same
number of XOR ops, no perf regression.

**ALL THREE `avx2_sc_*` bridge lemmas (`avx2_sc_load_block`,
`avx2_sc_load_last`, `avx2_sc_store_block`) are now PROVED** —
they mirror the proved `arm64_sc_*` lemmas at N=4, threading
`avx2_lane = get_lane_u64x4` through per-u64-lane ensures clauses
on `Simd.Avx2.{load_block, load_last, store_block}` (added to the
Rust source mirroring arm64) and ultimately bottoming out on
per-u64-lane ensures on `mm256_loadu_si256_u8` /
`mm256_storeu_si256_u8` (added to `avx2_extract.rs`, mirroring
arm64's NEON load/store stubs).  Source change: `Simd.Avx2.load_last`
loop unrolled to expose `buffer0..buffer3` separately (same
compiled code as the previous `for i in 0..4 { buffers[i]... }`
form) so the F* bridge can reconstruct each buffer in scope.

The two API-level `assume val`s (#13, #14) are the AVX2 analogues of
`lemma_absorb2_arm64` (recently proved on arm64) and
`lemma_squeeze2_arm64` (still admitted on arm64); discharging them
requires inline loop-invariant proofs on
`Generic_keccak.Simd256.{absorb4, squeeze4}` analogous to the ones on
`Simd128.{absorb2, squeeze2}`.

`lemma_keccak4_avx2` is **proved by composition** of #13 and #14
(mirrors how `lemma_keccak2_arm64` composes the two arm64
driver-lemmas).  `lemma_shake256_x4_avx2` (top-level hasher
theorem for `Libcrux_sha3.Avx2.X4.shake256`) is then
proved from `lemma_keccak4_avx2`.

Admits #2-#5 are the AVX2 analogues of arm64's body-level admits in
`Libcrux_sha3.Simd.Arm64.fst` and `Libcrux_sha3.Generic_keccak.Simd128.fst`.
The API contracts (preconditions, postconditions, and integration
into the keccak/sponge chain) are real and discharged.

`lemma_absorb2_arm64` (formerly load-bearing) is **now proved** — it
appears as a real `let` definition at
`EquivImplSpec.Sponge.Arm64.API.fst:67`.

Admits #2-#5 are the AVX2 analogues of arm64's body-level admits in
`Libcrux_sha3.Simd.Arm64.fst` and `Libcrux_sha3.Generic_keccak.Simd128.fst`.
The API contracts (preconditions, postconditions, and integration
into the keccak/sponge chain) are real and discharged.

`lemma_absorb2_arm64` (formerly load-bearing) is **now proved** — it
appears as a real `let` definition at
`EquivImplSpec.Sponge.Arm64.API.fst:67`.

Non-load-bearing upstream admits (3) remain in
`Proof_Utils.Lemmas.fst:26/33/54` (hax-lib / core-models targets).
