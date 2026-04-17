# Plan: Generalize Impl_Spec_Keccakf to Any Lane-Correct KeccakItem

## Context

`Impl_Spec_Keccakf.Generic.fst` proves keccak_f equivalence for **any** KeccakItem backend, given a 7-field `lane_correctness` record. The generic proof is complete and verified. Backend instantiations for Portable (N=1) and Arm64/NEON (N=2) are done. AVX2 (N=4) is deferred until extraction is available on an x86_64 host.

## Status Summary

| Step | Status | Notes |
|------|--------|-------|
| Step 0: Rust cross-spec tests | **DONE** | 9 tests in `generic_keccak.rs::neon_to_spec_tests` |
| Step 0.5: `arm64_extract.rs` lane specs | **DONE** | 9 types with `vec<W>_as_<T>x<N>` + `get_lane_<T>x<N>`, ~40 intrinsics with ensures |
| Step 1: `lane_correctness` record | **DONE** | `Impl_Spec_Keccakf.Generic.fst:93-134` |
| Step 2: `extract_lane` | **DONE** | `Impl_Spec_Keccakf.Generic.fst:140-148` |
| Step 3: Generic impl-side lemmas | **DONE** | All `= ()` with abstract v_T |
| Step 4: Per-step `to_spec` commutativity | **DONE** | theta, rho, pi, chi, iota — all verified |
| Step 5: Full keccakf1600 composition | **DONE** | `lemma_keccakf1600_to_spec` at `Generic.fst:1635-1649` |
| Step 6a: Portable instantiation | **DONE** | `Impl_Spec_Keccakf.Portable.fst` |
| Step 6b: Arm64/NEON instantiation | **DONE** | `Impl_Spec_Keccakf.Arm64.fst` |
| Step 6c: AVX2 instantiation | Deferred | No extraction on this host |

## Architecture: `extract_lane` Commutativity

The central theorem in `Impl_Spec_Keccakf.Generic.fst`:

```fstar
val lemma_keccakf1600_to_spec
    (v_N: usize) (#v_T: Type0) {| inst: t_KeccakItem v_T v_N |}
    (lc: lane_correctness v_N #v_T)
    (ks: t_KeccakState v_N v_T)
    (l: nat{l < v v_N})
  : Lemma (extract_lane v_N lc
             (impl_2__keccakf1600 v_N #v_T ks).f_st l
           == keccak_f (extract_lane v_N lc ks.f_st l))
```

## Step 0: Rust cross-spec tests (DONE)

9 tests in `generic_keccak.rs::neon_to_spec_tests` empirically validate lane-wise commutativity for every step function and full keccakf1600 on NEON. All pass.

## Step 0.5: `arm64_extract.rs` comprehensive spec pass (DONE)

### Type-level lane views (9 types)

Each NEON type now has `vec<W>_as_<T>x<N>` (abstract `val`) and `get_lane_<T>x<N>` (concrete `let`) in its F* interface block:

| Rust type | Width | View | Lane getter |
|-----------|-------|------|-------------|
| `_uint16x4_t` | 64 | `vec64_as_u16x4` | `get_lane_u16x4` |
| `_int16x4_t` | 64 | `vec64_as_i16x4` | `get_lane_i16x4` |
| `_int16x8_t` | 128 | `vec128_as_i16x8` | `get_lane_i16x8` |
| `_uint8x16_t` | 128 | `vec128_as_u8x16` | `get_lane_u8x16` |
| `_uint16x8_t` | 128 | `vec128_as_u16x8` | `get_lane_u16x8` |
| `_uint32x4_t` | 128 | `vec128_as_u32x4` | `get_lane_u32x4` |
| `_int32x4_t` | 128 | `vec128_as_i32x4` | `get_lane_i32x4` |
| `_uint64x2_t` | 128 | `vec128_as_u64x2` | `get_lane_u64x2` |
| `_int64x2_t` | 128 | `vec128_as_i64x2` | `get_lane_i64x2` |

### Intrinsic specs by category

All ensures use `forall`-over-lane form (no `Spec.Utils` dependency — the intrinsics .fsti is self-contained).

| Category | Count | Status | Examples |
|----------|-------|--------|----------|
| Broadcasts | 4 | **Done** | `_vdupq_n_u64`, `_vdupq_n_s16`, `_vdupq_n_u32`, `_vdupq_n_u16`, `_vdupq_n_u8` |
| Element-wise arith | 3 | **Done** | `_vaddq_s16`, `_vsubq_s16`, `_vaddq_u32` |
| Scalar-broadcast arith | 3 | **Done** | `_vmulq_n_s16`, `_vmulq_n_u16`, `_vmulq_n_u32` |
| Element-wise multiply | 1 | **Done** | `_vmulq_s16` |
| Bitwise logic | 5 | **Done** | `_vandq_s16`, `_vandq_u32`, `_vandq_u16`, `_vbicq_u64`, `_veorq_s16`, `_veorq_u64`, `_veorq_u8`, `_veorq_u32` |
| Fused bitwise (Keccak) | 3 | **Done** | `_veor3q_u64`, `_vbcaxq_u64`, `_vrax1q_u64` |
| Keccak XOR-rotate | 1 | **Done** | `_vxarq_u64` |
| Comparisons | 2 | **Done** | `_vcgeq_s16`, `_vcleq_s16` |
| Loads | 4 | **Done** | `_vld1q_u64` (requires+ensures), `_vld1q_s16`, `_vld1q_u8`, `_vld1q_u16`, `_vld1q_u32`; `_vld1q_bytes`/`_vld1q_bytes_u64` (requires-only or l_True) |
| Stores | 4 | **Done** | `_vst1q_s16`, `_vst1q_u64`, `_vst1q_bytes_u64`, `_vst1q_u8`, `_vst1q_bytes` (length-only) |
| Reinterprets (identity) | 16 | **Done** | `$result == $a` for all 128-bit type casts |
| Permutations (TRN) | 8 | **Done** | `_vtrn1q_s16/s32/s64/u64`, `_vtrn2q_s16/s32/s64/u64` |
| Lane slicing | 3 | **Done** | `_vget_low_s16`, `_vget_low_u16`, `_vget_high_u16` |
| Widening multiplies | 4 | **Done** | `_vmull_s16`, `_vmull_high_s16`, `_vmlal_s16`, `_vmlal_high_s16` |
| Table lookup | 1 | **Done** | `_vqtbl1q_u8` |
| Horizontal reductions | 3 | **Done** | `_vaddv_u16`, `_vaddvq_s16`, `_vaddvq_u16` (explicit sums) |
| Constant shifts | 7 | **Deferred** | Need `requires` for `>>!`/`<<!` subtyping |
| Parameterized-index | 2 | **Deferred** | `_vdupq_laneq_u32`, `_vextq_u32` — need `requires` for index |
| Saturating multiply-high | 3 | **Deferred** | `_vqdmulhq_n_s16`, `_vqdmulhq_s16`, `_vqdmulhq_n_s32` |
| Variable shifts | 2 | **Deferred** | `_vshlq_s16`, `_vshlq_u16` |
| Shift-left-and-insert | 2 | **Deferred** | `_vsliq_n_s32`, `_vsliq_n_s64` |
| AES | 2 | **Out of scope** | `_vaesmcq_u8`, `_vaeseq_u8` |
| Carryless multiply | 1 | **Out of scope** | `_vmull_p64` |

### Deferred items: what's needed

The constant-shift and parameterized-index intrinsics need `requires` clauses constraining the const generic parameter (e.g., `SHIFT_BY >= 0 /\ SHIFT_BY < 16` for `_vshrq_n_s16`). Without this, F*'s `>>!` operator fails a subtyping check. These intrinsics are not used by SHA-3 (only by ml-kem NEON, which is excluded from extraction).

## Step 1: `lane_correctness` record (DONE)

Defined at `Impl_Spec_Keccakf.Generic.fst:93-134`:

```fstar
noeq type lane_correctness (v_N: usize) (#v_T: Type0)
    {| inst: t_KeccakItem v_T v_N |} = {
  lane: v_T -> l:nat{l < v v_N} -> u64;
  lc_zero: ...;
  lc_xor5: ...;
  lc_rotate_left1_and_xor: ...;
  lc_xor_and_rotate: ...;
  lc_and_not_xor: ...;
  lc_xor_constant: ...;
  lc_xor: ...;
}
```

Note: `lc_and_not_xor` uses argument order `a ^. (b &. (~. c))` matching the NEON `vbcaxq` instruction directly.

## Step 2: `extract_lane` (DONE)

```fstar
[@"opaque_to_smt"]
let extract_lane (v_N: usize) (#v_T: Type0) {| inst: t_KeccakItem v_T v_N |}
    (lc: lane_correctness v_N #v_T)
    (state: t_Array v_T (mk_usize 25))
    (l: nat{l < v v_N})
  : t_Array u64 (mk_usize 25) =
  Rust_primitives.Arrays.createi (mk_usize 25) (fun i -> lc.lane state.[i] l)
```

## Steps 3-5: Generic proof (DONE)

The full generic proof is 1649 lines in `Impl_Spec_Keccakf.Generic.fst`. Key architectural decisions:
- `opaque_to_smt` on `extract_lane` with explicit `reveal_opaque` + `lemma_extract_lane_index` for controlled unfolding
- Per-step extract_lane lemmas for theta, rho, pi, chi, iota
- Chi uses `ChiFold` module for the fold_range reduction
- `SpecRounds` module bridges fuel-25 spec evaluation
- 24-round composition via `fold_range` induction

## Step 6a: Portable instantiation (DONE)

`Impl_Spec_Keccakf.Portable.fst` (156 lines):
- `portable_lane (x: u64) (l: nat{l < 1}) : u64 = x`
- All 7 `lc_*` fields are `= ()`
- `lemma_extract_lane_portable_identity`: proves `extract_lane` is the identity at N=1
- Main theorem collapses to: `keccakf1600 ks == keccak_f ks` (no extract_lane wrapper)

## Step 6b: Arm64/NEON instantiation (DONE)

`Impl_Spec_Keccakf.Arm64.fst` (151 lines):
- `arm64_lane (v: t_e_uint64x2_t) (l: nat{l < 2}) : u64 = get_lane_u64x2 v l`
- All 7 `lc_*` fields are `= ()` — the `forall`-over-lane ensures clauses on the intrinsics supply the proof obligations directly
- Main theorem: per-lane commutativity for N=2

## Files

| File | Status |
|------|--------|
| `generic_keccak.rs` | Tests added (Step 0 — DONE) |
| `intrinsics/src/arm64_extract.rs` | 9 type views + ~40 ensures (DONE) |
| `intrinsics/proofs/fstar/extraction/Libcrux_intrinsics.Arm64_extract.fsti` | Regenerated (DONE) |
| `equivalence/Impl_Spec_Keccakf.Generic.fst` | Generic proof (DONE) |
| `equivalence/Impl_Spec_Keccakf.ChiFold.fst` | Chi fold helper (DONE) |
| `equivalence/Impl_Spec_Keccakf.SpecRounds.fst` | Spec bridge (DONE) |
| `equivalence/Impl_Spec_Keccakf.Portable.fst` | Portable instantiation (DONE) |
| `equivalence/Impl_Spec_Keccakf.Arm64.fst` | Arm64 instantiation (DONE) |
| `equivalence/Makefile` | All roots added (DONE) |
| `equivalence/Impl_Spec_Keccakf.fst` | Old monolithic proof — kept for sponge compat |

## Follow-ups (not in scope of this plan)

- **Sponge generalization**: Generalize `Impl_Spec_Sponge.*` (Core/Absorb/Squeeze/Keccak) to arbitrary `v_N` on top of `Impl_Spec_Keccakf.Generic`. Once done, the old monolithic `Impl_Spec_Keccakf.fst` can be deleted.
- **AVX2 instantiation**: `Impl_Spec_Keccakf.Avx2.fst` when extraction lands on x86_64.
- **Constant-shift specs**: Add `requires` constraints and re-enable ensures for `_vshrq_n_*`, `_vshlq_n_*`.
- **AES / poly-mul specs**: Pair with F* reference implementations.
