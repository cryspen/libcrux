# Sponge-Layer Proof Plan

## Status

### Proven (no admits)
- **Phase 9**: Rate/delimiter constants (8 lemmas, all `= ()`)
- **Phase 10**: Lane index equivalence (`= ()`)
- **Phase 17**: Top-level hash function equivalences (6 lemmas)
  - `lemma_sha256_equiv`, `lemma_sha224_equiv`, `lemma_sha384_equiv`,
    `lemma_sha512_equiv`, `lemma_shake128_equiv`, `lemma_shake256_equiv`
  - Each calls `lemma_keccak1_equiv` with concrete rate/delim/output_len.
    The SMT solver unfolds the non-recursive wrapper chain
    (e.g. `sha256 → sha256_ema → Portable.sha256 → keccak1`) automatically.
- **Phase 16 partial**: `lemma_new_state_equiv` (`= ()`, definitional)

### Admitted — strong postconditions, needs proof body
- **Phase 11**: `lemma_load_block_equiv` — load_block == xor_block_into_state
- **Phase 12**: `lemma_load_last_equiv`, `lemma_load_last_as_absorb`
- **Phase 13**: `lemma_store_block_equiv` — store_block == squeeze_state
- **Phase 14**: `lemma_absorb_block_equiv`, `lemma_absorb_final_equiv`
- **Phase 15**: `lemma_absorb_loop_equiv` (recursive, inductive)

### Admitted — weak postconditions (`True`), needs strengthening + proof
- **Phase 15 bridges**: `lemma_impl_absorb_is_loop`, `lemma_spec_absorb_is_loop`
- **Phase 16 sub-lemmas**: `lemma_absorb_phase_equiv`,
  `lemma_squeeze_single_equiv`, `lemma_squeeze_general_equiv`
- **Phase 16 main**: `lemma_keccak1_equiv` (the central theorem)

## What to prove next

### 1. fold_range step lemma (utility)

Define a reusable `lemma_fold_range_step` that peels one iteration:

```
fold_range start end_ inv init f
  == fold_range (start+1) end_ inv (f init start) f
```

This is provable at `--fuel 1` and is needed by all bridge lemmas.
Check `Rust_primitives.Hax.Folds` for an existing version first.

### 2. Phase 15 bridge lemmas

**`lemma_impl_absorb_is_loop`**: Show keccak1's absorb fold_range equals
`impl_absorb_loop`. Approach: induction using `lemma_fold_range_step`.

The fold body in keccak1 calls `lemma_mul_succ_le` (a unit-returning lemma)
before `impl_2__absorb_block`. This doesn't affect the result but must be
accounted for in the bridge.

**`lemma_spec_absorb_is_loop`**: Same pattern for the spec side. Simpler
because the spec's fold body calls `absorb_block` directly, matching
`spec_absorb_loop` exactly.

### 3. Phase 15 absorb loop equivalence

`lemma_absorb_loop_equiv` already has the right postcondition:
```
(impl_absorb_loop ks data rate i n).f_st == spec_absorb_loop state data rate i n
```

Proof: induction on `n - i` at `--fuel 1`.
- Base: `i = n` → both return input, which matches by precondition.
- Step: call `lemma_absorb_block_equiv` for one iteration, then recurse.

Requires `lemma_absorb_block_equiv` (Phase 14, admitted).

### 4. Phase 14 per-step equivalences

**`lemma_absorb_block_equiv`**: Compose `lemma_load_block_equiv` (Phase 11)
with `Impl_Spec_Keccakf.lemma_keccakf1600_equiv`.

**`lemma_absorb_final_equiv`**: Compose `lemma_load_last_equiv` (Phase 12)
with `Impl_Spec_Keccakf.lemma_keccakf1600_equiv`.

Both should be short (call two lemmas, solver connects them).

### 5. Phases 11-13 (the hard per-operation proofs)

**Phase 11 (`lemma_load_block_equiv`)**: HARD. Impl uses two-loop
(read-all, XOR-all), spec uses one-loop (read-and-XOR). Proof needs:
- lane_index injectivity for `i < 25`
- Each state element modified at most once → order irrelevant
- Per-element equality + `forall_intro` + `eq_intro`
- May need `--fuel 8 --z3rlimit 200` or recursive bridge for the fold_ranges.

**Phase 12 (`lemma_load_last_equiv`)**: MEDIUM. Show impl's RATE-byte buffer
and spec's 200-byte buffer agree on bytes 0..RATE-1, then apply Phase 11.

**Phase 13 (`lemma_store_block_equiv`)**: MEDIUM. Same loop structure on both
sides after spec restructuring. Per-position equality using Phase 10
(`lane_index == impl index`). Should be more tractable than Phase 11.

### 6. Phase 16 squeeze equivalences

Define recursive squeeze helpers (like absorb helpers):

```fstar
let rec impl_squeeze_loop (ks: impl_state) (out: t_Slice u8) (rate: usize)
    (i n: usize) : (t_Slice u8 & impl_state) = ...
let rec spec_squeeze_loop (state: spec_state) (out: t_Array u8 output_len)
    (rate output_len: usize) (i n: usize) : (t_Array u8 output_len & spec_state) = ...
```

Then:
1. Bridge: keccak1's squeeze code == `impl_squeeze_loop`
2. Bridge: keccak's squeeze fold_range == `spec_squeeze_loop`
3. Induction: `impl_squeeze_loop` output == `spec_squeeze_loop` output
   (using `lemma_store_block_equiv` per step + keccakf equiv between steps)

The structural mismatch: impl uses if/else + loop + remainder; spec uses
a unified for-loop with `if round > 0 then keccakf`. Both execute the same
`(squeeze, keccakf)` sequence, just structured differently.

### 7. Phase 16 main theorem

`lemma_keccak1_equiv`: Compose everything:
1. `lemma_new_state_equiv` (done)
2. Bridge: keccak1's absorb fold_range == `impl_absorb_loop`
3. Bridge: keccak's absorb fold_range == `spec_absorb_loop`
4. `lemma_absorb_loop_equiv`: loop states match
5. `lemma_absorb_final_equiv`: states match after final block
6. Squeeze equivalence: outputs match

Needs the SMT solver to unfold `keccak1` and `keccak` and match
intermediate values with the bridge lemma results.
Expect `--z3rlimit 300` or higher.

## Recommended order

Bottom-up from the hardest unknowns:

1. `lemma_fold_range_step` (utility)
2. Phase 13: `lemma_store_block_equiv` (medium, unblocks squeeze)
3. Phase 11: `lemma_load_block_equiv` (hard, unblocks absorb)
4. Phase 12: `lemma_load_last_equiv` (medium, builds on Phase 11)
5. Phase 14: `lemma_absorb_block_equiv` + `lemma_absorb_final_equiv`
6. Phase 15: bridges + `lemma_absorb_loop_equiv`
7. Phase 16: squeeze helpers + `lemma_keccak1_equiv`

Phase 17 is already done and will remain valid throughout.
