# SHA-3 Proof Status and Next Steps

## Completed (no sorry)

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

**File: `Impl_Spec_Sponge.lean`** — State initialization verified:
- impl_new_spec: zero-initialized state

## In Progress — Sponge Layer

### XOR loop (loop 2 of load_block) — 1 sorry

**What's proved:**
- flat_perm / flat_perm_inv: transposition permutation, involution by 25-case exhaustion
- xor_loop_inv_init, xor_loop_inv_step: loop invariant helpers
- lb_get/lb_set: local wrappers for get_ij/set_ij (mvcgen matching)
- xor_loop_spec structure: invariant swap + hax_mvcgen decomposes body
- All arithmetic VCs closed (vc_omega + grind for i%5 < 5)

**1 sorry (vc12 — step VC):**
- Need to wire set_ij postcondition through xor_loop_inv_step
- Requires: Vector.getElem ↔ Array.getD conversion + flat_perm index matching
- The xor_loop_inv_step helper is already proved — just needs mechanical wiring

### Next steps (bottom-up order):

1. **Close xor_loop_spec vc12** — wire set postcondition through xor_loop_inv_step
2. **Loop 1 of load_block** (byte parsing) — parse 8 bytes → u64 via from_le_bytes
   - Needs specs for: from_le_bytes, unwrap, try_into, range indexing
   - Define parse_bytes_pure, invariant, use same loop pattern
3. **Compose loops 1+2** into full load_block_spec
   - Also handle the two `hax_lib.assert` checks
4. **load_last_spec** — similar to load_block + padding
5. **store_block_spec** — extract bytes from state (reverse of load_block)
6. **absorb_block_spec** — already structurally validated (trait dispatch + hax_mvcgen)
7. **absorb_final_spec** — same pattern as absorb_block
8. **squeeze_spec** — wraps store_block via Squeeze trait
9. **keccak1_spec** — full sponge, already decomposed by hax_mvcgen into ~20 VCs

### Key infrastructure needed for sponge:
- `@[spec]` for `core_models.num.Impl_9.from_le_bytes` (u8[8] → u64)
- `@[spec]` for `core_models.num.Impl_9.to_le_bytes` (u64 → u8[8])
- `@[spec]` for `core_models.result.Impl.unwrap` (Result → value)
- `@[spec]` for `core_models.convert.TryInto.try_into` (slice → array)
- `@[spec]` for range indexing `blocks[start..end]_?`
- `@[spec]` for `core_models.slice.Impl.len` (already sorry'd)
- `@[spec]` for `libcrux_sha3.proof_utils.lemmas.lemma_mul_succ_le` (ghost lemma)
- `@[spec]` for `rust_primitives.hax.repeat` (array initialization)

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
