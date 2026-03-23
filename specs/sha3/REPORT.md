# SHA-3 Equivalence Proof Report

## Overview

This directory contains formal equivalence proofs between the libcrux SHA-3
implementation (`crates/algorithms/sha3`) and the hacspec specification
(`specs/sha3`), verified using F* via hax extraction.

The proofs target the **normalizable-primitives** branch of hax, where
`t_Array`/`t_Slice` are represented as F* `list` (not `Seq.seq`), and
bitwise/fold operations are concrete and normalizable.

## How to Verify

```bash
# Prerequisites: FSTAR_HOME set, z3 4.13.3 on PATH, cargo/hax/jq installed

# Default (admits slow equivalence proofs):
cd specs/sha3
FSTAR_HOME=~/FStar make -C proofs/fstar/extraction

# Full verification including equivalence proofs:
FSTAR_HOME=~/FStar VERIFY_SLOW_MODULES=yes make -C proofs/fstar/extraction
```

## File Structure

### Hacspec Specification (hax-extracted)
- `Hacspec_sha3.Keccak_f.fst` — Keccak-f[1600] step functions (**pure hax output**)
- `Hacspec_sha3.Sponge.fst` — Sponge construction (**pure hax output**)
- `Hacspec_sha3.Sha3.fst` — Top-level API (**pure hax output**)
- `Hacspec_sha3.fst` — Root module (**hand-edited**, see below)

### Equivalence Proofs (hand-written)
- `Sha3_Equivalence.fst` — Portable (u64, N=1) equivalence
- `Sha3_Equivalence_Neon.fst` — Neon (u8/SIMD128, N=2) lane-wise equivalence
- `Sha3_Equivalence_Avx2.fst` — AVX2 placeholder (no F* extraction yet)

## Manual Edits Required After Re-extraction

Running `cargo hax into fstar` from `specs/sha3` will overwrite `Hacspec_sha3.fst`.
The following edit must be re-applied:

**`Hacspec_sha3.fst`**: Replace the hax-extracted content:
```fstar
assume val createi ...
assume val createi_lemma ... (Seq.index ...)
```
with:
```fstar
unfold let createi (#v_T: Type0) (v_N: usize) (#v_F: Type0)
      (f: (x:usize{x <. v_N}) -> v_T) : t_Array v_T v_N
    = Rust_primitives.Arrays.createi v_N f
```

This is needed because hax generates `Seq.index`-based lemmas which are
incompatible with the `list`-based `t_Array` in normalizable-primitives.
Ideally this fix should be upstreamed into hax.

**Implementation files** (`crates/algorithms/sha3/proofs/fstar/extraction/`):
No manual edits needed. The typeclass constraint removal on `t_KeccakState`
and `t_KeccakXofState` was done in a prior commit and is part of the branch.
The Rust source edit (`Core.Slice` → `Core_models.Slice` in `traits.rs`)
ensures correct extraction.

## Verification Status

### Sha3_Equivalence.fst — Portable Proof (35 lemmas)

**Fully proved (19 lemmas):**
- Phase 1 primitives: `lemma_xor5_unfold`, `lemma_vrax1q_unfold`, `lemma_vbcaxq_unfold`, `lemma_veorq_n_unfold`
- Phase 2 accessors: `lemma_get_transposed`, `lemma_set_ij_unfold`
- Phase 3 constants: `lemma_round_constants_equal`
- Phase 4 iota: `lemma_iota_equiv`
- Phase 7 chi: `lemma_chi_equiv` (pointwise via `forall_intro` + explicit `eq_intro`)
- Phase 8 rounds: `lemma_one_round_equiv`, `lemma_rounds_equiv` (induction), `lemma_keccakf1600_equiv`
- Phase 9 wrappers: `lemma_load_block_equiv`, `lemma_load_last_equiv`, `lemma_store_block_equiv`
- Phase 10 API: `lemma_sha{224,256,384,512}_equiv`, `lemma_shake{128,256}_equiv`

**Admitted — `--admit_smt_queries true` (4 lemmas):**
- `lemma_theta_rho_equiv` — 25 chained list_upd vs createi
- `lemma_pi_equiv` — same structural issue
- `lemma_keccakf1600_is_impl_rounds` — fold_range ↔ recursive helper bridge
- `lemma_keccak_f_is_spec_rounds` — same bridge

**Admitted — `admit()` (2 lemmas):**
- `lemma_rotate_left_zero` — rotate_left is abstract
- `lemma_rho_theta_eq` — bridge for rho(theta(state))

**Assumed — `assume val` (6):**
- `logand_commutative` — AND commutativity (not in abstract interface)
- `lemma_chi_fold_reduces` — fold_range reduction for chi
- `lemma_load_block_fold_equiv`, `lemma_load_last_fold_equiv`, `lemma_store_block_fold_equiv` — fold_range for load/store
- `lemma_keccak1_equiv` body uses `admit()` — full sponge loop

### Sha3_Equivalence_Neon.fst — Neon Proof (35 items)

**Fully proved (16):** KeccakItem lane lemmas (7), `get_ij_extract`, `round_constants`, `keccakf1600_equiv` (main theorem), API unfolds (6)

**Admitted — `--admit_smt_queries true` (5):** `neon_one_round_lane`, `neon_rounds_lane`, `keccakf1600_unfold`, `neon_keccakf1600_is_neon_rounds`, `neon_iota_lane_proved`

**Assumed — `assume val` (14):** 7 intrinsic lane-wise, 4 step function lane-wise, 2 load/store lane, 1 sponge lane

## Known Issues

### pi/theta_rho: 25-element array permutation equivalence

Both `lemma_pi_equiv` and `lemma_theta_rho_equiv` compare 25 chained `list_upd`
operations (impl) vs `createi`/`list_init` (spec). Multiple proof strategies
were attempted:

- Pure SMT, forall_intro + eq_intro, 25 pointwise asserts, tactic norm + trefl/smt, match destructuring — all fail or cause 15+ minute blowups
- Root cause: `list_upd` is `opaque_to_smt` (to prevent blowups) but this prevents SMT from tracing through 25 chained updates
- A custom tactic or proof-libs helper for destructuring fixed-size lists would resolve this

### fold_range bridge lemmas

`impl_2__keccakf1600` uses `fold_range` which can't normalize because the body
contains heavyweight functions. Bridge lemmas need `--admit_smt_queries true`.

### Implementation debug_assert! failures

Several impl files (`Simd.Arm64`, `Generic_keccak.Portable`, `Simd128`, `Neon`)
fail non-lax due to `Hax_lib.v_assert` from `debug_assert!` without preconditions.
These are pre-existing issues unrelated to the normalizable-primitives migration.

## Dependencies

- **hax**: `normalizable-primitives` branch (`https://github.com/cryspen/hax`)
  - Local proof-lib changes in `~/hax` (to be pushed): `Rust_primitives.Arrays.{fst,fsti}` — `list_init`/`list_upd` made `[@@"opaque_to_smt"] let rec` in `.fsti`, `createi` made concrete, `list_init_index`/`list_upd_index` with SMTPat, `eq_intro` proved by induction
- **F***: `~/FStar/bin/fstar.exe`
- **Z3**: version 4.13.3
