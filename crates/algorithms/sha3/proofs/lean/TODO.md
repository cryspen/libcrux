# SHA-3 Proof Status and Next Steps

## Completed (no sorry)

**File: `Impl_Spec_Mvcgen.lean`** — All step proofs fully verified:
- Pure reference definitions (rotate_left_pure, theta_c/d, pi_pure, chi_pure, iota_pure, round_pure, keccak_f_pure)
- Infrastructure specs (usize_mul/add/div/mod, getElemResult, i32_add/eq, cast_i32_u32)
- Layer 0: Primitive specs (veor5q, vbcaxq, veorq_n, rotate_left_portable, vrax1q, vxarq)
- Layer 1: Accessor specs (get_ij, set_ij, Impl_2_set, KeccakState_getElem)
- Layer 2: Step specs — iota, pi (5 sub-steps + composition), rho (5 sub-steps + composition), theta
- Helper lemmas: Vector.toArray_getD_eq, modifies_only4/5, pi_perm_table, rotate_left_pure_zero, theta_d_from_c

## In Progress

**File: `Impl_Spec_Compose.lean`** — Chi proof (2 sorry in helpers, 1 sorry in main proof):

### Chi proof structure (complete, 1 blocker)

The proof uses loop invariant approach:
1. `fold_range_usize_spec` — custom @[spec] wrapping existing fold_range_spec_int_USize64
2. `fold_range_inv_irrelevant` — swap trivial extraction invariant for real one
3. Outer loop invariant: `chi_inv old_arr st_arr i 0` (columns < i updated)
4. Inner loop invariant: `chi_inv old_arr st_arr i j` (positions in column i with row < j updated)

**Verified VCs:**
- Outer initial: `chi_inv st st 0 0` — trivial (nothing processed)
- Inner initial: inherits from outer
- Inner VC2 (column complete): `chi_inv i 5 → chi_inv (i+1) 0` — proved via `chi_inv_finish_column`
- Outer VC2 (all done): `chi_inv 5 0 → postcondition` — proved (k%5 < 5 always true)
- All arithmetic/bounds VCs: closed by `vc_omega`

**BLOCKER: Inner step (vc8/vc9)**
mvcgen generates `sorry.val` for `Impl_2_set_spec`'s `⌜ i.toNat < 5 ∧ j.toNat < 5 ⌝` precondition when `i` and `j` are abstract loop variables (not concrete literals).

### Fix: `conj` wrapper approach

Wrapping `∧` in an opaque `@[irreducible] def conj (a b : Prop) := a ∧ b` makes mvcgen emit it as a normal VC goal (confirmed by experiment). The fix requires:

1. Change `Impl_2_set_spec` and `KeccakState_getElem_spec` in `Impl_Spec_Mvcgen.lean` to use `conj` instead of `∧` in their preconditions
2. Update all existing proofs that pattern-match on the conjunction: add `unfold conj at h; obtain ⟨hi, hj⟩ := h` or use a `vc_conj` macro
3. Existing pi/rho proofs use these specs with concrete indices — mvcgen will generate `conj (0 < 5) (1 < 5)` VCs, which `unfold conj; exact ⟨by vc_omega, by vc_omega⟩` closes

**Alternative:** Use separate `_conj` specs in Compose only. But `@[spec]` can't be erased, so having both registered means mvcgen may pick the original. Would need to make the conj version higher priority.

**Alternative 2 (user suggestion):** Reformulate specs as `P → ⦃ True ⦄ f x ⦃ Q ⦄` instead of `⦃ P ⦄ f x ⦃ Q ⦄`. This moves the precondition outside the Hoare triple. Not tested yet.

### Helper lemma issues

- `chi_body_arr_flat` — needs `&&&` commutativity for `u64` (bitwise AND). `and_comm` in Lean's `Bool` doesn't directly apply to `UInt64.HAnd`.
- `chi_inv_update` — references `Array.getD` but the environment uses `Array[i]?.getD` (Array API version mismatch). Needs `Array.getD` ↔ `Array.getElem?` bridge.

## TODO (not started)

- `impl_chi_spec` — close inner step (requires conj fix or wp_bind for set)
- `rho_theta_bridge` — compose `impl_theta_spec` + `impl_rho_spec` into `rho_theta_pure`
- `round_impl_spec` — compose theta+rho bridge + pi + chi + iota → `round_pure`
- `keccakf1600_spec` — 24-round fold → `keccak_f_pure`

## Build instructions

```bash
cd crates/algorithms/sha3/proofs/lean
# Clean build (needed after changing Impl_Spec_Mvcgen):
rm -f .lake/build/lib/lean/Impl_Spec_*.olean .lake/build/lib/lean/Impl_Spec_*.ilean
lake build 2>&1 | tee /tmp/build.log
# Quick check:
grep -E '(error|sorry)' /tmp/build.log | grep -v 'Stubs\|LibcruxStubs\|extraction'
```

## Key learnings (see also Mvcgen.md)

1. **fold_range invariant swap**: `fold_range` ignores invariant at runtime (ghost args). `fold_range_inv_irrelevant` lets us swap any invariant.
2. **fold_range_usize_spec**: The existing `fold_range_spec_int_USize64` is `@[specset int]`, not `@[spec]`, so mvcgen doesn't use it. Wrapping it as `@[spec]` makes mvcgen decompose loops.
3. **conj wrapper**: `@[irreducible] def conj (a b : Prop) := a ∧ b` tricks mvcgen into generating proper VCs for conjunction preconditions with abstract arguments.
4. **`(i + 1).toNat` reduction**: For USize64, `(i + 1).toNat = i.toNat + 1` requires `USize64.add_def`, `BitVec.toNat_add`, `Nat.mod_eq_of_lt` — not just `vc_omega`.
