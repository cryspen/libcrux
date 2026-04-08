# SHA-3 Proof Status and Next Steps

## Completed (no sorry)

**File: `Stubs.lean`** — Byte conversion stubs filled in:
- `Impl_9.from_le_bytes`: real LE byte→u64 implementation (@[spec] + @[irreducible])
- `Impl_9.to_le_bytes`: real u64→LE byte implementation (@[spec] + @[irreducible])

**File: `Impl_Spec_Mvcgen.lean`** — All step proofs fully verified:
- Pure reference definitions (rotate_left_pure, theta_c/d, pi_pure, chi_pure, iota_pure, round_pure, apply_rounds, keccak_f_pure)
- Infrastructure specs (usize_mul/add/div/mod, getElemResult, i32_add/eq, cast_i32_u32)
- All specs use P → ⦃ True ⦄ form with hax_mvcgen
- Layer 0: Primitive specs (veor5q, vbcaxq, veorq_n, rotate_left_portable, vrax1q, vxarq)
- Layer 1: Accessor specs (get_ij, set_ij, Impl_2_set, KeccakState_getElem)
- Layer 2: Step specs — iota, pi (5 sub-steps + composition), rho (5 sub-steps + composition), theta

**File: `Impl_Spec_Compose.lean`** — Chi, round, keccak_f fully verified:
- Chi: nested 5×5 loop with invariant swap + hax_mvcgen. Postcondition: r.st.toVec = chi_pure
- Bridge lemmas: iota_bridge, chi_bridge, pi_bridge, rho_theta_bridge (with sub-bridges for theta_c/d, rho offsets)
- Stronger specs: impl_pi_pure_spec, round_iota_pure_spec (via Triple.of_entails_right)
- round_body_spec: hax_mvcgen chains 5 specs, bridges connect to round_pure
- keccakf1600_spec: 24-round loop with apply_rounds invariant, postcondition = keccak_f_pure

**File: `Impl_Spec_Sponge.lean`** — Sponge layer infrastructure:
- impl_new_spec: zero-initialized state
- flat_perm / flat_perm_inv: transposition permutation, involution by 25-case exhaustion
- bytes_to_u64_le: pure LE byte→u64 conversion (@[irreducible])
- load_block_pure: concrete definition using flat_perm_inv + bytes_to_u64_le (@[irreducible])
- xor_loop_inv, xor_loop_inv_init, xor_loop_inv_step: all proved
- xor_loop_spec: fully proved (loop 2 of load_block)
- lb_get/lb_set wrappers with specs
- byte_loop_inv, byte_loop_inv_init: proved
- byte_xor_compose: proved — connects byte_loop_inv + xor_loop_inv → load_block_pure

## In Progress — Sponge Layer

### byte_loop_spec (loop 1 of load_block) — 3 sorries

Standalone spec for the byte conversion fold_range. Structure: invariant swap + hax_mvcgen.

**Remaining VCs:**
1. **vc4, vc5** (overflow): `start + 8*i < USize64.size` — mechanical, needs `hbounds` specialized with current `i` + `blocks.size_lt_usizeSize`
2. **vc8** (slice size): `(blocks.extract offset (offset+8)).size = 8` — needs `hbounds` + `Array.size_extract`
3. **vc11** (step): `byte_loop_inv` maintained after `update_at_usize` with `from_le_bytes` result — needs bridge between `from_le_bytes` output (on extracted slice) and `bytes_to_u64_le` (on input list). The byte values should match: `extractedArray.toVec[k] = blocks.val.toList.getD (start + 8*i + k) 0`.

### load_block_spec — 1 sorry

All VCs closed except vc29 (compositional goal). Will close by wiring `byte_loop_spec` + `xor_loop_spec` + `byte_xor_compose`.

Added precondition: `hrate_le : RATE.toNat ≤ 200` (needed for array bounds since state is 25 lanes × 8 bytes).

### Next steps (priority order):

1. **Close byte_loop_spec VCs** — vc4/5/8 are mechanical overflow/size. vc11 needs the from_le_bytes ↔ bytes_to_u64_le bridge (main proof work).
2. **Wire load_block_spec vc29** — compose byte_loop_spec + xor_loop_spec + byte_xor_compose
3. **store_block_spec** — extract bytes from state (reverse of load_block)
4. **load_last_spec** — similar to load_block + padding
5. **absorb_block_spec** — already structurally validated (trait dispatch + hax_mvcgen), 2 sorry VCs
6. **absorb_final_spec** — same pattern as absorb_block
7. **squeeze_spec** — wraps store_block via Squeeze trait
8. **keccak1_spec** — full sponge, already decomposed by hax_mvcgen into ~20 VCs

### Key infrastructure available (from Hax library):
All needed @[spec] definitions exist:
- `hax_lib.assert` — checks bool, returns unit
- `rust_primitives.hax.repeat` — creates array filled with value
- `update_at_usize` — array point update
- `from_le_bytes` (Impl_9) — now has real body (@[spec] + @[irreducible])
- `core_models.result.Impl.unwrap` — unwraps Result
- `core_models.convert.TryInto.try_into` — slice to array
- `Range.getElemArrayUSize64_spec` / `getElemVectorUSize64_spec` — slice range indexing
- `core_models.slice.Impl.len.spec` — slice length
- `fold_range` specs for USize64

### Hacspec reference (specs/sha3/proofs/lean/extraction/hacspec_sha3.lean):
- `xor_block_into_state`: single-loop version of load_block (combines byte conversion + XOR)
- `lane_index`: same as flat_perm (5*(l%5) + l/5)
- `keccak`: full sponge with absorb/squeeze phases

## Build instructions

```bash
cd crates/algorithms/sha3/proofs/lean
# Clean build:
rm -f .lake/build/lib/lean/Impl_Spec_*.olean .lake/build/lib/lean/Impl_Spec_*.ilean
lake build 2>&1 | tee /tmp/build.log
# Quick check:
grep -E '(error|sorry)' /tmp/build.log | grep -v 'Stubs\|LibcruxStubs\|extraction'
```

## Key learnings (see also Mvcgen.md)

1. **P → ⦃ True ⦄ form**: All specs must use this. Conjunction preconditions generate sorry.val.
2. **Local wrappers**: Needed when mvcgen can't match type-level args (get_ij, set_ij, Impl_2.set, Impl_2.iota).
3. **Invariant swap**: fold_range_inv_irrelevant before hax_mvcgen. Inner loops use conv + ext.
4. **Bridge lemmas**: element-wise getD → pure Vector equality via Vector.ext + toArray_getD_eq.
5. **Triple.of_entails_right**: Strengthen postconditions from element-wise to pure function equalities.
6. **Make pure functions irreducible**: Before proofs that mention them in postconditions. Otherwise mvcgen timeout.
7. **grind for USize64 modular arithmetic**: vc_omega can't handle x = y % n → x < n. grind can.
8. **flat_perm transposition**: set_ij(state, i/5, i%5) writes to 5*(i%5)+i/5, not i. Prove involution by exhaustion.
9. **native_decide +revert**: For concrete equality goals after rcases that still have free variables.
10. **Seq.size_lt_usizeSize**: Needed for overflow VCs involving slice sizes (`blocks.val.size < USize64.size`).
11. **Factoring loop specs**: When two loops are nested in `do` blocks, `rw [show ... from fold_range_inv_irrelevant]` can't find them through `bind`. Factor each loop as a standalone spec lemma and compose.
12. **Vector.getElem ↔ Array.getD bridge**: `v.toArray.getD j 0 = v[j]` via `unfold Array.getD; rw [dif_pos ...]; exact Vector.getElem_toArray _`.
