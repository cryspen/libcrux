# SHA-3 Proof Status and Next Steps

## Completed (no sorry)

**File: `LibcruxStubs.lean`**:
- `update_at_range`: real splice definition (extract ++ v ++ extract)
- `copy_from_slice_u8`: irreducible wrapper with @[spec] for specset "int"
  (fixes OOM: raw copy_from_slice only has @[hax_spec] for specset "bv")

**File: `Impl_Spec_Mvcgen.lean`** (~960 lines):
- All step proofs fully verified (theta, rho, pi, iota, chi helpers)

**File: `Impl_Spec_Compose.lean`** (~580 lines):
- Chi, round, keccak_f fully verified
- fold_range_inv_irrelevant lemma

**File: `Impl_Spec_Sponge.lean`** — Sponge layer:
- impl_new_spec: proved
- Pure functions: flat_perm/flat_perm_inv, bytes_to_u64_le, load_block_pure, lane_byte, store_block_pure
- byte_loop_inv + byte_loop_inv_init + byte_loop_inv_step: proved
- byte_xor_compose: proved (connects byte_loop_inv + xor_loop_inv → load_block_pure)
- xor_loop_spec: fully proved
- byte_loop_spec: fully proved
- store_loop_inv: defined
- splice_seq + splice_seq_getD: defined (getD sorry)
- store_block_spec: hax_mvcgen succeeds (67s), 8 of 11 VCs closed

## Immediate TODOs (store_block_spec)

3 sorry VCs remain. Close them using helper lemmas:

### vc18: loop step
Goal: `store_loop_inv` holds at `i+1` after `splice_seq`.
Approach: Use `splice_seq_getD` to get element-wise access. Split on `b < 8*i` (old invariant) vs `8*i ≤ b < 8*(i+1)` (new bytes = lane_byte).
Needs: `splice_seq_getD` proved, plus bridge `to_le_bytes` literal → `lane_byte`.

### vc35: composition (remainder path, len % 8 > 0)
Goal: After loop + remainder splice, full postcondition holds.
Has `store_loop_inv` at `len/8` + remainder splice via `splice_seq`.
Approach: Combine loop invariant (covers `b < 8*(len/8)`) with remainder splice (covers `8*(len/8) ≤ b < len`).

### vc36: composition (no remainder, len % 8 = 0)
Goal: Loop result directly satisfies postcondition.
Has `store_loop_inv` at `len/8` and `¬(len % 8 > 0)` i.e. `len % 8 = 0`.
Approach: `len = 8 * (len/8)` so `store_loop_inv` at `len/8` IS the postcondition.

### Helper lemmas needed (sorry):
1. **`splice_seq_getD`**: Element-wise access to splice result.
   `(extract 0 start ++ v ++ extract stop size).toList.getD k = if start ≤ k < stop then v[k-start] else s[k]`
2. **`remainder_copy_len_eq`**: Already defined but unused (vc31 closed differently).

## Other sorry proofs in Impl_Spec_Sponge.lean

- **load_block_spec** vc29: needs manual wp decomposition to apply byte_loop_spec + xor_loop_spec
- **load_last_pure**: sorry body (pure function definition)
- **load_last_spec, absorb_block_spec, absorb_final_spec, squeeze_spec**: sorry proofs
- **slice_len_spec, lemma_mul_succ_le_spec, RangeTo_getElemRustArray_spec**: sorry proofs
- **keccak1_spec**: sorry (top-level sponge)

## Key patterns (see Mvcgen.md)

1. **fold_range_inv_irrelevant**: Swap FROM extraction's True/sorry invariant TO real invariant. Two-step for store_block (extraction inv → True → real inv).
2. **Local wrappers**: `lb_get`/`lb_set` for get_ij/set_ij, `copy_from_slice_u8` for copy_from_slice. Needed when Hax function only has @[hax_spec] for specset "bv".
3. **Dead binding elimination**: `simp only [Impl.len, slice_length, pure_bind]` removes unused `let _ ← Impl.len`.
4. **splice_seq**: Pure function for update_at_range result. `@[spec]` on update_at_range returns `splice_seq`.

## Build

```bash
cd crates/algorithms/sha3/proofs/lean
rm -f .lake/build/lib/lean/Impl_Spec_Sponge.olean .lake/build/lib/lean/Impl_Spec_Sponge.ilean .lake/build/lib/lean/Impl_Spec_Sponge.trace
time lake build Impl_Spec_Sponge  # ~67s
```
