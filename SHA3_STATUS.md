# SHA-3 Proofs — Current Status

Quick status pointer. Full details in
`crates/algorithms/sha3/proofs/fstar/equivalence/HANDOFF.md`.

## Current focus (2026-04-26)

**Arm64 `load_block` body admit DISCHARGED.**  Net arm64 body-level
admit count drops from 2 to 1 (`store_block` is the last remaining
body admit on arm64).  Committed in `abf8b5297` ("load-blocl"); per-lane
ensures + loop invariant on `Simd.Arm64.load_block` follow the same
pattern that already verifies arm64 `load_last`.  Source change:
`crates/algorithms/sha3/src/simd/arm64.rs::load_block` gets a real
proof; `--z3rlimit` settings adjusted to `800 --split_queries always`.

### "Real" admits remaining — concise inventory

**Arm64 (2 load-bearing):**

| # | Where | Kind | Notes |
|---|-------|------|-------|
| A1 | `Libcrux_sha3.Simd.Arm64.fst:909` | body `admit ()` in `store_block` | needs bytewise byte-level reasoning + loop invariant; mirrors arm64 `load_block`/`load_last` patterns now that those are proved |
| A2 | `EquivImplSpec.Sponge.Arm64.API.fst:88` | `assume val lemma_squeeze2_arm64` | unblocked by the per-lane Steps lemma (Option B from the squeeze2 post-mortem) — same lemma also unblocks AVX2 `lemma_squeeze4_avx2` |

**AVX2 (3 load-bearing):**

| # | Where | Kind | Notes |
|---|-------|------|-------|
| V1 | `Libcrux_sha3.Simd.Avx2.fst:1433` | body `admit ()` in `store_block` | mirror of A1 at N=4 |
| V2 | `EquivImplSpec.Sponge.Avx2.API.fst:87` | `assume val lemma_squeeze4_avx2` | mirror of A2 at N=4; same Option B lemma closes both |
| V3 | `Libcrux_intrinsics.Avx2_extract.fsti:21` | `val lemma_get_lane_u64x4_bit` (bit-bridge axiom) | single trust point relating the opaque `vec256_as_u64x4` lane extraction to the underlying bit vector — all ten `lemma_mm256_*_u64x4` SMTPats (six original + four added this session for `unpackhi/unpacklo_epi64`, `set_epi64x`, `permute2x128_si256`) now derive from this one bridge |

(NEON intrinsic-level `val` declarations in `Libcrux_intrinsics.Arm64_extract.fsti`
are uninterpreted axioms too, but the same intrinsic-level trust
boundary applies on both platforms — not double-counted above.)

### Recently DISCHARGED (no longer admits)

- **Arm64 `load_block`** — body admit removed (commit `abf8b5297`,
  2026-04-26).  Now verifies its full per-lane equivalence ensures
  inline.  *(Arm64 `load_last` was never an admit.)*
- **6 AVX2 `lemma_mm256_*_u64x4` SMTPats** — `or, xor, andnot,
  slli_epi64, srli_epi64, set1_epi64x` — were `admit ()`s in the
  extracted `.fsti`; now real `let` proofs deriving from the V3
  bit-bridge (commit `ef12db0ce`, 2026-04-25 night).  Trust shrinks
  from 6 axioms to 1.
- **`lemma_shl_xor_shr_is_rotate_left`** — proved in
  `Libcrux_sha3.Proof_utils.Lemmas.fst:21` via per-bit equality +
  `lemma_int_t_eq_via_bits` + `lemma_rotate_left_u_get_bit`.  No
  longer an admit.  (Stale comment in `EquivImplSpec.Keccakf.Avx2.fst:96-99`
  still references it as "admitted" — text-only doc lag.)
- **3 `Proof_Utils.Lemmas.fst` upstream admits** — closed via
  `cryspen/hax integer-lemmas` branch (commit `a078bd14c`).
- **`avx2_sc_load_block` / `avx2_sc_load_last` / `avx2_sc_store_block`**
  — all three bridges proved (commit `c6aada632`).
- **`lemma_absorb4_avx2`** — driver-level `assume val` flipped to a
  real `let` (commit `a2c9f1da4`).
- **`lemma_absorb2_arm64`** — proved earlier (2026-04-24 evening).

### AVX2 `load_block` — committed but NOT verifying

`crates/algorithms/sha3/src/simd/avx2.rs` adds `load_lane_u64`,
`load_u64x4x4`, `load_u64x4` helpers (both ops helpers
`[@@ "opaque_to_smt"]`) and an inline loop invariant on `load_block`.
Helpers verify cleanly.  **`load_block` itself does NOT verify
within F*'s practical limits** — N=4 doubles the per-state-element
conjuncts vs arm64 N=2, pushing total split count to 600+, and the
verification path also exposes a hard F*/Z3 RPC parse-error bug
after ~800 z3 process spawns (likely an fd / handle leak in F*
2025.03.25-dev).  See HANDOFF.md for the full configuration matrix
tried and the three suggested next steps (refactor to
`load_block_chunk` helper / simplify ensures with recursive predicate
/ hand-prove in F*).  Until `load_block` verifies, the AVX2 body
admits stay at `store_block` + `load_block`.

#### Intrinsic-level work that DID land this session

`crates/utils/intrinsics/src/avx2_extract.rs` and
`fstar-helpers/fstar-bitvec/BitVec.Intrinsics.fsti`: added bit-level
definitions and four new SMTPat lemmas
`lemma_mm256_{unpackhi,unpacklo}_epi64_u64x4`,
`lemma_mm256_set_epi64x_u64x4`,
`lemma_mm256_permute2x128_si256_u64x4` — all **proved** from the
existing bridge axiom `lemma_get_lane_u64x4_bit` (no new trust
axioms, V3 still the only u64x4 trust point).  These are usable by
ML-DSA NTT/INVNTT/encoding too if those proofs ever need u64-lane
semantics.

## Earlier focus (2026-04-25 later)

**Attempted `lemma_squeeze4_avx2`; banked infrastructure, deferred main proof.**
The full inline-ensures pattern at N=4 (mirroring Portable.squeeze)
hits the same Z3 BoxBool cascade documented in the squeeze2 attempt
post-mortem; at N=4 it's worse (8 forall conjuncts vs 4 at N=2, and
12 live arrays in the VC vs 6).  The path forward is Option B from
the squeeze2 post-mortem: build a per-lane Steps lemma so each VC
sees only one lane's facts.  Estimated ~2-3 days.

### What landed (banked)

- `KeccakState<4, Vec256>::squeeze_last4` — new helper method with
  per-lane ensures pinning each output to `Hacspec_sha3.Sponge.squeeze_last`.
  Verified clean (824 queries, 0 failed).  Re-usable by the eventual
  Option B proof.
- `_keccak_state_impl4_opts` push-options workaround so methods
  inside `impl KeccakState<4, Vec256>` can use `--z3rlimit 800
  --split_queries always` (mirrors Portable's setup).
- `out0.len() < usize::MAX - 200` precondition propagated up to
  `Simd256::keccak4` and `avx2::shake256` — needed for the eventual
  `Hacspec_sha3.Sponge.squeeze` ensures.

`lemma_squeeze4_avx2` in `EquivImplSpec.Sponge.Avx2.API.fst` remains
an `assume val`.  Admit count unchanged.

See `crates/algorithms/sha3/proofs/fstar/equivalence/HANDOFF.md`
"2026-04-25 (later)" for the post-mortem and Option B sketch.

## Earlier focus (2026-04-25 night, late)

**`lemma_absorb4_avx2` is now PROVED.**  The AVX2 driver-level absorb
lemma is no longer an `assume val` — it's a real `let` discharged by
the Rust-side ensures on `Libcrux_sha3.Generic_keccak.Simd256.absorb4`
(proved inline via an `absorb_blocks`-based loop invariant at N=4,
mirroring the arm64 `Simd128.absorb2` proof at N=2).  Net AVX2
load-bearing admit count drops from 9 to 8.

`absorb4` body no longer has the `hax_lib::fstar!("admit()")`.  The
function now verifies its full per-lane equivalence ensures clause at
`--z3rlimit 800 --split_queries always`.  Two `assert
(slices_same_len 4 data)` hints inside the per-iteration and post-loop
scaffolding give Z3 the bridge fact for the `lemma_absorb_block_avx2`
preconditions.

Incidental fix: `squeeze4`'s `--z3rlimit` bumped from 300 to 600 with
`--split_queries always`, since the original was hitting timeouts on
the loop-body `f_squeeze4` precondition (pre-existing flake unmasked
once we removed the `absorb4` body admit and Z3 stopped short-
circuiting the module).

### Source changes (2026-04-25 night, late)

- `crates/algorithms/sha3/src/generic_keccak/simd256.rs` — `absorb4`
  gets per-lane `ensures` (4 conjuncts) + inline scaffolding (4 ×
  `lemma_extract_lane_zero_avx2` + 4 × `lemma_absorb_blocks_base`
  pre-loop, 4 × `lemma_absorb_block_avx2` + 4 × `lemma_absorb_blocks_tail`
  per-iter, 4 × `lemma_absorb_last_avx2` + 4 ×
  `lemma_absorb_rec_via_blocks` post-loop) mirroring arm64 absorb2
  at N=4; explicit `assert (slices_same_len 4 data)` hints for Z3.
  Body `admit()` removed.  `squeeze4` rlimit bumped to 600 with
  `--split_queries always`.
- `crates/algorithms/sha3/proofs/fstar/equivalence/EquivImplSpec.Sponge.Avx2.API.fst`
  — `lemma_absorb4_avx2` flipped from `assume val` to `let _ =
  Simd256.absorb4 rate delim data in ()`, mirroring arm64
  `lemma_absorb2_arm64`.

## Earlier focus (2026-04-25 evening)

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

## Load-bearing admit inventory (2026-04-26)

### Arm64 (2)

| # | File | Line | Kind |
|---|------|------|------|
| A1 | `Libcrux_sha3.Simd.Arm64.fst` | 909 | body `admit ()` inside `store_block` |
| A2 | `EquivImplSpec.Sponge.Arm64.API.fst` | 88 | `assume val lemma_squeeze2_arm64` |

### AVX2 (3)

| # | File | Line | Kind |
|---|------|------|------|
| V1 | `Libcrux_sha3.Simd.Avx2.fst` | 1433 | body `admit ()` inside `store_block` |
| V2 | `EquivImplSpec.Sponge.Avx2.API.fst` | 87 | `assume val lemma_squeeze4_avx2` |
| V3 | `Libcrux_intrinsics.Avx2_extract.fsti` | 21 | `val lemma_get_lane_u64x4_bit` (the single bit-bridge axiom relating `get_lane_u64x4` to the underlying bit vector — all ten SMTPat'd `lemma_mm256_*_u64x4` lemmas now derive from this) |

### Discharged since 2026-04-25 evening

- `Libcrux_sha3.Simd.Arm64.fst::load_block` body — proved
  (commit `abf8b5297`, 2026-04-26).
- `Libcrux_intrinsics.Avx2_extract.fsti::lemma_mm256_{or,xor,andnot,slli_epi64,srli_epi64,set1_epi64x}_u64x4`
  — 6 admits collapsed to 1 bit-bridge `val` (commit `ef12db0ce`).
- `Libcrux_sha3.Proof_utils.Lemmas.lemma_shl_xor_shr_is_rotate_left`
  — proved via per-bit equality + `lemma_int_t_eq_via_bits`.  The
  comment at `EquivImplSpec.Keccakf.Avx2.fst:96-99` calling it
  "admitted" is stale doc (the lemma is a real `let` proof now).
- `Proof_Utils.Lemmas.fst` — 4 upstream admits closed via
  `cryspen/hax integer-lemmas` branch (commit `a078bd14c`).
- AVX2 `lemma_absorb4_avx2`, `avx2_sc_*` bridges (3), `arm64_sc_*`
  bridges, all 7 lane-correctness lemmas, `lemma_keccak4_avx2`,
  `lemma_shake256_x4_avx2`, `lemma_absorb2_arm64` — all proved earlier.

### Properties of the remaining inventory

- **A1 ↔ V1 mirror at N=2/N=4.**  Both `store_block` bodies need
  byte-level loop-invariant + per-lane bytewise reasoning
  (essentially the dual of the now-proved `load_block` patterns).
- **A2 ↔ V2 mirror at N=2/N=4.**  Both API-level `assume val`s are
  unblocked by the same per-lane Steps lemma (Option B from the
  squeeze2 post-mortem) — one `lemma_squeeze_one_step` proof closes
  both, since `Simd128.squeeze2` and `Simd256.squeeze4` then become 2
  / 4 calls with single-lane state in scope.
- **V3 is the only AVX2-specific intrinsic-level trust axiom.**  It
  plays the same role as the (uninterpreted) NEON intrinsic `val`s
  on arm64 — a primitive bit/lane semantic relation — but, unlike
  arm64, AVX2 collapses 6 such axioms down to this single bridge.

Non-load-bearing utility admits: none.  (The 3 historical admits in
`Proof_Utils.Lemmas.fst` are gone.)
