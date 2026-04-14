# Plan: Generalize Impl_Spec_Keccakf to Any Lane-Correct KeccakItem

## Context

`Impl_Spec_Keccakf.fst` (1262 lines) proves keccak_f equivalence for the portable backend (N=1, u64). We want to generalize it so that **any** KeccakItem implementation (NEON N=2, AVX2 N=4, future backends) gets the keccak_f proof for free, given ~7 lane-correctness hypotheses about its operations.

The critical structural insight: the Generic_keccak step functions (`impl_2__theta`, `impl_2__rho_0_`-`rho_4_`, `impl_2__pi_0_`-`pi_4_`, `impl_2__chi`, `impl_2__iota`) are fully polymorphic -- they have the **same body** for all N/T, just dispatching through typeclass methods. The current `= ()` proofs for rho/pi lemmas work because of **array update semantics** (not u64-specific unfolding), so they should generalize to abstract `v_T`.

## Architecture: `to_spec` Commutativity

The central idea is an explicit **`to_spec`** function that maps SIMD implementation state to N copies of scalar spec state:

```fstar
let to_spec (#v_T: Type0) (v_N: usize) {| inst: t_KeccakItem v_T v_N |}
    (lc: lane_correctness v_N #v_T)
    (state: t_Array v_T (mk_usize 25))
  : t_Array (t_Array u64 (mk_usize 25)) v_N =
  Rust_primitives.Arrays.createi v_N (fun l ->
    Rust_primitives.Arrays.createi (mk_usize 25) (fun i -> lc.lane state.[i] l))
```

Then prove **commutativity** of `to_spec` with each step function:

```fstar
(to_spec lc (impl_step state)).[l] == spec_step ((to_spec lc state).[l])
```

**End-to-end**: By composing step-wise commutativity:
```fstar
to_spec lc (keccakf1600 v_N #v_T ks).f_st ==
  map_array keccak_f (to_spec lc ks.f_st)
```

i.e., running impl keccakf1600 then extracting lanes = extracting lanes then running spec keccak_f on each.

## Step 0: Rust cross-spec tests (DONE)

9 tests in `generic_keccak.rs::neon_to_spec_tests` empirically validate lane-wise commutativity for every step function and full keccakf1600 on NEON. All pass.

## Step 0.5: Add u64x2 lane specs to `arm64_extract.rs`

**Pattern**: Follow `avx2_extract.rs` which uses `#[hax_lib::fstar::replace(interface, ...)]` on the `Vec256` struct to emit `vec256_as_i16x16` and `get_lane`, then uses `#[hax_lib::ensures(...)]` on intrinsic functions to add F* postconditions referencing the lane interpretation.

**File**: `crates/utils/intrinsics/src/arm64_extract.rs` (generates `Libcrux_intrinsics.Arm64_extract.fsti`)

### 1. Extend `_uint64x2_t` struct annotation to emit lane interpretation

Currently (line 44-47):
```rust
#[derive(Clone, Copy)]
#[hax_lib::lean::replace("abbrev _uint64x2_t := BitVec 128")]
#[hax_lib::fstar::replace(interface, "unfold type $:{_uint64x2_t} = bit_vec 128")]
pub struct _uint64x2_t(u8);
```

Change to:
```rust
#[derive(Clone, Copy)]
#[hax_lib::lean::replace("abbrev _uint64x2_t := BitVec 128")]
#[hax_lib::fstar::replace(interface, r#"
unfold type $:{_uint64x2_t} = bit_vec 128
val vec128_as_u64x2 (x: $:{_uint64x2_t}) : t_Array u64 (mk_usize 2)
let get_lane64 (v: $:{_uint64x2_t}) (i:nat{i < 2}) = Seq.index (vec128_as_u64x2 v) i
"#)]
pub struct _uint64x2_t(u8);
```

### 2. Add `#[hax_lib::ensures]` on keccak-relevant intrinsics

**`_vdupq_n_u64`** (broadcast scalar to both lanes):
```rust
#[hax_lib::ensures(|result| fstar!("vec128_as_u64x2 $result == Seq.create 2 $i"))]
pub fn _vdupq_n_u64(i: u64) -> _uint64x2_t { ... }
```

**`_veorq_u64`** (lane-wise XOR):
```rust
#[hax_lib::ensures(|result| fstar!("forall (i:nat{i < 2}). get_lane64 $result i == (get_lane64 $mask i ^. get_lane64 $shifted i)"))]
pub fn _veorq_u64(mask: _uint64x2_t, shifted: _uint64x2_t) -> _uint64x2_t { ... }
```

**`_veor3q_u64`** (lane-wise triple XOR):
```rust
#[hax_lib::ensures(|result| fstar!("forall (i:nat{i < 2}). get_lane64 $result i == ((get_lane64 $a i ^. get_lane64 $b i) ^. get_lane64 $c i)"))]
pub fn _veor3q_u64(a: _uint64x2_t, b: _uint64x2_t, c: _uint64x2_t) -> _uint64x2_t { ... }
```

**`_vrax1q_u64`** (lane-wise: a[i] XOR rotate_left(b[i], 1)):
```rust
#[hax_lib::ensures(|result| fstar!("forall (i:nat{i < 2}). get_lane64 $result i == (get_lane64 $a i ^. Core_models.Num.impl_u64__rotate_left (get_lane64 $b i) (mk_u32 1))"))]
pub fn _vrax1q_u64(a: _uint64x2_t, b: _uint64x2_t) -> _uint64x2_t { ... }
```

**`_vxarq_u64`** (lane-wise: rotate_left(a[i] XOR b[i], LEFT)):
```rust
#[hax_lib::ensures(|result| fstar!("forall (i:nat{i < 2}). get_lane64 $result i == Core_models.Num.impl_u64__rotate_left (get_lane64 $a i ^. get_lane64 $b i) (cast ${LEFT} <: u32)"))]
pub fn _vxarq_u64<const LEFT: i32, const RIGHT: i32>(a: _uint64x2_t, b: _uint64x2_t) -> _uint64x2_t { ... }
```

**`_vbcaxq_u64`** (lane-wise: a[i] XOR (b[i] AND NOT c[i])):
```rust
#[hax_lib::ensures(|result| fstar!("forall (i:nat{i < 2}). get_lane64 $result i == (get_lane64 $a i ^. (get_lane64 $b i &. (~. (get_lane64 $c i))))"))]
pub fn _vbcaxq_u64(a: _uint64x2_t, b: _uint64x2_t, c: _uint64x2_t) -> _uint64x2_t { ... }
```

**`_vld1q_u64`** (load 2 u64s into lanes):
```rust
#[hax_lib::requires(array.len() >= 2)]
#[hax_lib::ensures(|result| fstar!("forall (i:nat{i < 2}). get_lane64 $result i == Seq.index $array i"))]
pub fn _vld1q_u64(array: &[u64]) -> _uint64x2_t { ... }
```

**`_vst1q_u64`** (store lanes to u64 slice) — already has length postcondition, extend:
```rust
#[hax_lib::ensures(|()| fstar!("future($out).len() == $out.len() /\\ (forall (i:nat{i < 2}). i < Seq.length (future $out) ==> Seq.index (future $out) i == get_lane64 $v i)"))]
pub fn _vst1q_u64(out: &mut [u64], v: _uint64x2_t) { ... }
```

### Connection to Step 6 (NEON instantiation)

The `Impl_Spec_Keccakf_Neon.fst` instantiation file will:
- Define `neon_lane (v: t_e_uint64x2_t) (l: nat{l < 2}) : u64 = get_lane64 v l`
- Prove each `lc_*` hypothesis from the postconditions emitted by hax from the annotations above
- These proofs should be short (1-3 lines each), just unfolding the KeccakItem methods and applying the intrinsic specs

**No additional assume vals needed in the proof files** -- all assumptions are localized in `arm64_extract.rs` → `Arm64_extract.fsti`.

## Step 1: Define lane-correctness specification

```fstar
noeq type lane_correctness (v_N: usize) (#v_T: Type0) 
    {| inst: t_KeccakItem v_T v_N |} = {
  lane: v_T -> l:nat{l < v v_N} -> u64;
  lc_zero:                 ... lane (f_zero ()) l == mk_u64 0
  lc_xor5:                 ... lane (f_xor5 a b c d e) l == (((lane a l ^. lane b l) ^. lane c l) ^. lane d l) ^. lane e l
  lc_rotate_left1_and_xor: ... lane (f_rotate_left1_and_xor a b) l == lane a l ^. rotate_left (lane b l) 1
  lc_xor_and_rotate:       ... lane (f_xor_and_rotate L R a b) l == rotate_left (lane a l ^. lane b l) L
  lc_and_not_xor:          ... lane (f_and_not_xor a b c) l == lane a l ^. ((~.(lane b l)) &. lane c l)
  lc_xor_constant:         ... lane (f_xor_constant a c) l == lane a l ^. c
  lc_xor:                  ... lane (f_xor a b) l == lane a l ^. lane b l
}
```

## Step 2: Define `to_spec` / `extract_lane`

```fstar
let extract_lane v_N lc (state: t_Array v_T 25) (l: nat{l < v v_N}) : t_Array u64 25 =
  Rust_primitives.Arrays.createi 25 (fun i -> lc.lane state.[i] l)
```

## Step 3: Generic impl-side lemmas (abstract v_T)

Generalize existing `lemma_rho_0_` etc. to state results in terms of abstract KeccakItem operations (not concrete u64). Should still be `= ()` since they depend only on array update semantics.

## Step 4: Per-step `to_spec` commutativity

For each step, prove: `extract_lane lc (impl_step state) l == spec_step (extract_lane lc state l)`

- **Theta+Rho**: Uses lc_xor5, lc_rotate_left1_and_xor, lc_xor_and_rotate, lc_xor
- **Pi**: Pure permutation, no lane-correctness needed
- **Chi**: Uses lc_and_not_xor (+ logand_commutative for spec comparison)
- **Iota**: Uses lc_xor_constant

## Step 5: Compose into full keccakf1600 commutativity

Chain per-step commutativity into one-round, then induction over 24 rounds.

## Step 6: Instantiate for each backend

- **Portable (N=1, u64)**: lane(x, 0) = x. All lc_* are `= ()`.
- **NEON (N=2, uint64x2_t)**: lane = neon_lane (assume val). lc_* proved from ~7 NEON intrinsic assumptions.
- **AVX2 (N=4, Vec256)**: lane = avx2_lane (assume val). Extra: rotate_left decomposition lemma.

## Files

| File | Action |
|------|--------|
| `generic_keccak.rs` | Tests added (Step 0 -- DONE) |
| `intrinsics/src/arm64_extract.rs` | Add `vec128_as_u64x2`/`get_lane64` to struct, `#[hax_lib::ensures]` on 7 intrinsics → generates `Arm64_extract.fsti` |
| `Impl_Spec_Keccakf.fst` | Generalize to parametric v_N/v_T |
| `Impl_Spec_Keccakf_Portable.fst` | New: portable instantiation |
| `Impl_Spec_Keccakf_Neon.fst` | New: NEON instantiation (uses Arm64_extract specs) |
| `Impl_Spec_Keccakf_Avx2.fst` | New (when extraction available) |
| `Makefile` | Add new roots |

## Scalability: `opaque_to_smt`

After proving a lemma for a function, mark it `@["opaque_to_smt"]`. In lemmas that need to see inside, use `reveal_opaque`. Apply bottom-up as layers are proved.

## Risks

- **Will `= ()` work with abstract v_T?** Array update semantics are type-independent, so it should. Fallback: explicit `assert` hints.
- **Typeclass resolution**: Should work with explicit `{| inst |}` parameter.
