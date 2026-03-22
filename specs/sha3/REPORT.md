# SHA-3 Equivalence Proof Report

## Overview

This directory contains formal equivalence proofs between the libcrux SHA-3
implementation (`crates/algorithms/sha3`) and the hacspec specification
(`specs/sha3`), verified using F* via hax extraction.

The proofs target the **normalizable-primitives** branch of hax, where
`t_Array`/`t_Slice` are represented as F* `list` (not `Seq.seq`), and
bitwise/fold operations are concrete and normalizable.

## File Structure

### Hacspec Specification (hax-extracted)
- `Hacspec_sha3.fst` — Root module; defines `createi` (delegates to `Rust_primitives.Arrays.createi`)
- `Hacspec_sha3.Keccak_f.fst` — Keccak-f[1600] step functions: theta, rho, pi, chi, iota, keccak_f
- `Hacspec_sha3.Sponge.fst` — Sponge construction: absorb, squeeze, keccak
- `Hacspec_sha3.Sha3.fst` — Top-level API: sha3_224, sha3_256, sha3_384, sha3_512, shake128, shake256

### Equivalence Proofs (hand-written)
- `Sha3_Equivalence.fst` — Portable (u64, N=1) equivalence proof
- `Sha3_Equivalence_Neon.fst` — Neon (u8/SIMD128, N=2) lane-wise equivalence proof
- `Sha3_Equivalence_Avx2.fst` — AVX2 placeholder (no F* extraction yet)

## Verification Status

All files typecheck in non-lax mode (37 seconds total for `Sha3_Equivalence.fst`).

### Sha3_Equivalence.fst — Portable Proof

| Lemma | Status | Notes |
|-------|--------|-------|
| **Phase 1: Primitive ops** | | |
| `lemma_xor5_unfold` | PROVED | `= ()` |
| `lemma_vrax1q_unfold` | PROVED | `= ()` |
| `lemma_vbcaxq_unfold` | PROVED | `= ()` |
| `lemma_veorq_n_unfold` | PROVED | `= ()` |
| **Phase 2: State accessors** | | |
| `lemma_get_transposed` | PROVED | `= ()` |
| `lemma_set_ij_unfold` | PROVED | `= ()` |
| **Phase 3: Round constants** | | |
| `lemma_round_constants_equal` | PROVED | `assert_norm` on array equality |
| **Phase 4: Iota** | | |
| `lemma_iota_equiv` | PROVED | `= ()` |
| **Phase 5: Theta + Rho** | | |
| `lemma_rotate_left_zero` | `admit()` | `rotate_left` is abstract; no axiom in `.fsti` |
| `lemma_rho_theta_eq` | `admit()` | Bridge: `rho_theta == rho(theta(state))` via 4 nested `createi` |
| `lemma_theta_rho_equiv` | `--admit_smt_queries true` | 25 chained `list_upd` vs `createi`; see "Open Problems" below |
| **Phase 6: Pi** | | |
| `lemma_pi_equiv` | `--admit_smt_queries true` | Same structural issue as theta_rho; see "Open Problems" |
| **Phase 7: Chi** | | |
| `logand_commutative` | `assume val` | `(a &. b) == (b &. a)` — true but not in abstract interface |
| `lemma_chi_fold_reduces` | `assume val` | `fold_range` can't be reduced by normalizer |
| `lemma_chi_equiv` | **PROVED** | Pointwise via `forall_intro` + explicit `eq_intro` |
| **Phase 8: Single round / keccakf1600** | | |
| `lemma_one_round_equiv` | **PROVED** | Chains sub-lemmas |
| `lemma_rounds_equiv` | **PROVED** | Recursive induction, fuel 1 |
| `lemma_keccakf1600_is_impl_rounds` | `--admit_smt_queries true` | `fold_range` can't normalize to recursive helper |
| `lemma_keccak_f_is_spec_rounds` | `--admit_smt_queries true` | Same `fold_range` issue |
| `lemma_keccakf1600_equiv` | **PROVED** | Composes bridge + induction lemmas |
| **Phase 9: Load / Store / Sponge** | | |
| `lemma_load_block_fold_equiv` | `assume val` | `fold_range` reduction blocked |
| `lemma_load_last_fold_equiv` | `assume val` | `fold_range` reduction blocked |
| `lemma_store_block_fold_equiv` | `assume val` | `fold_range` reduction blocked |
| `lemma_load_block_equiv` | PROVED | Delegates to assume val |
| `lemma_load_last_equiv` | PROVED | Delegates to assume val |
| `lemma_store_block_equiv` | PROVED | Delegates to assume val |
| **Phase 10: Top-level API** | | |
| `lemma_keccak1_equiv` | `--admit_smt_queries true` | Full sponge loop equivalence |
| `lemma_sha{224,256,384,512}_equiv` | PROVED | `= ()` (trivial wrapper unfolds) |
| `lemma_shake{128,256}_equiv` | PROVED | `= ()` (trivial wrapper unfolds) |

### Sha3_Equivalence_Neon.fst — NEON Lane-wise Proof

| Category | Status |
|----------|--------|
| Intrinsic lane-wise semantics (7 `assume val`) | Assumed (neon_lane, vdupq, veorq, veor3q, vrax1q, vxarq, vbcaxq) |
| KeccakItem lane-wise equivalence (7 lemmas) | PROVED |
| State extraction helper (`lemma_get_ij_extract`) | PROVED |
| Step function lane-wise (4 `assume val`) | Assumed (theta_rho, pi, chi, iota) |
| `lemma_neon_one_round_lane` | `--admit_smt_queries true` |
| `lemma_neon_rounds_lane` | `--admit_smt_queries true` |
| `lemma_keccakf1600_unfold` | `--admit_smt_queries true` |
| `lemma_neon_keccakf1600_is_neon_rounds` | `--admit_smt_queries true` |
| `lemma_neon_keccakf1600_equiv` (main theorem) | PROVED (composes sub-lemmas) |
| Round constants | PROVED (delegates to portable) |
| `lemma_neon_iota_lane_proved` | `--admit_smt_queries true` |
| Load/Store lane-wise (2 `assume val`) | Assumed |
| Sponge lane-wise (`lemma_neon_keccak2_lane0_equiv`) | `assume val` |
| Top-level API unfolds (6 lemmas) | PROVED |

### Sha3_Equivalence_Avx2.fst

Placeholder — no AVX2 F* extraction exists yet. Module is empty and typechecks trivially.

## Changes to hax proof-libs

The following changes were made to `~/hax` (normalizable-primitives branch) to support the proofs:

### `Rust_primitives.Arrays.fsti`
- `list_init`: Changed from `val` to `[@@"opaque_to_smt"] let rec` — makes it normalizable by F*'s normalizer but hidden from SMT to avoid blowups
- `list_init_index`: Added `val` with `SMTPat` for pointwise reasoning about `createi` results
- `list_upd`: Changed from `val` to `[@@"opaque_to_smt"] let rec` — normalizable but hidden from SMT
- `createi`: Changed from `val` with `admits` to concrete `let` calling `list_init`

### `Rust_primitives.Arrays.fst`
- `list_init_index`: Body is `admit()` — proving requires `list_init` visible to SMT within `.fst`, but `.fsti` `let rec` definitions are opaque to SMT in the implementing `.fst`
- `list_upd_index`: Body is `admit()` — same `.fsti`/`.fst` SMT visibility issue

## Open Problems

### 1. Proving `lemma_pi_equiv` and `lemma_theta_rho_equiv`

Both lemmas compare 25 chained `list_upd` operations (impl) against a single
`createi`/`list_init` call (spec). The fundamental issue:

- **Impl side**: `list_upd (list_upd ... state i0 v0) i1 v1` — the normalizer
  reduces this to nested `let hd :: tl = state in ...`, which requires
  destructuring the symbolic `state` list.

- **Spec side**: `list_init 25 (fun idx -> state.[perm(idx)])` — normalizes to
  `[state.[p0]; state.[p1]; ...; state.[p24]]`.

These are semantically equal but syntactically different after normalization.
`trefl` fails because the term structures differ. SMT can't handle the
normalized terms (too large/complex).

**Approaches tried**:
- Pure SMT (`= ()`) — fails, can't connect both sides
- `forall_intro` + `eq_intro` — inner lemma fails
- 25 pointwise asserts + `split_queries` — 15min SMTPat blowup
- Tactic `norm [delta] + trefl` — syntactically different after norm
- Tactic `norm [delta] + smt` — normalized terms too large for SMT
- Match destructuring of `state` — "patterns incomplete" or `ks.f_st` not substituted

**Proposed solution**: A proof-libs helper that destructures a `t_Array t (mk_usize n)`
into its `n` elements and rebuilds it as a concrete list literal. This would allow both
sides to normalize to the same concrete list of `s_k` terms. Alternatively, a custom
F* tactic that introduces element bindings and rewrites the goal.

### 2. Bridge lemmas (`fold_range` vs recursive helpers)

`impl_2__keccakf1600` uses `Rust_primitives.Hax.Folds.fold_range` which is
recursive but can't be normalized because the body contains heavyweight functions
(`impl_2__theta`, `impl_2__rho`, etc.) that aren't `unfold`. These bridge lemmas
need `--admit_smt_queries true`.

### 3. Load/Store/Sponge equivalences

These relate the impl's `fold_range`-based loops (load_block, store_block) to the
spec's `fold_range`-based loops (xor_block_into_state, squeeze_state). Both use
`fold_range` which can't be reduced. These are `assume val` for now.

### 4. `list_init_index` / `list_upd_index` proofs in proof-libs

These lemmas have `admit()` in the `.fst` because `let rec` definitions in `.fsti`
are opaque to SMT within the implementing `.fst`. The proof by induction works
when there is no `.fsti` (verified experimentally). Options:
- Remove the `.fsti` for `Rust_primitives.Arrays`
- Move these proofs to a separate module without a `.fsti`
- Use a tactic-based proof that doesn't rely on SMT seeing the definition

## Dependencies

- **hax**: `normalizable-primitives` branch (commit `3f7ed945` + local changes to `Rust_primitives.Arrays`)
- **F***: `~/FStar/bin/fstar.exe`
- **Z3**: version 4.13.3

## How to Verify

```bash
# From specs/sha3:
# Verify spec files
cd /path/to/libcrux-rust-spec/specs/sha3
make -C proofs/fstar/extraction

# Or verify individual files via the F* MCP server:
# Start server: fstar-mcp --mode http --port 3000
# Then create sessions with appropriate include paths (see fstar-helpers/Makefile.base)
```
