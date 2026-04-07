# hax_mvcgen Proof Strategies

## Setup

```lean
set_option hax_mvcgen.specset "int"  -- activate integer spec set
```

Use `hax_mvcgen` (not bare `mvcgen`) — it auto-discovers `@[specset int]` specs.

## Core patterns

### Pattern 1: P → ⦃ True ⦄ f ⦃ Q ⦄ (precondition outside triple)

**All** `@[spec]` lemmas must have `⦃ ⌜ True ⌝ ⦄` as precondition. Move real
preconditions to explicit parameters:

```lean
-- GOOD: mvcgen generates VCs for hi, hj
@[spec] theorem set_spec (st i j v) (hi : i.toNat < 5) (hj : j.toNat < 5) :
    ⦃ ⌜ True ⌝ ⦄ set st i j v ⦃ Q ⦄

-- BAD: mvcgen generates sorry.val for abstract i,j
@[spec] theorem set_spec (st i j v) :
    ⦃ ⌜ i.toNat < 5 ∧ j.toNat < 5 ⌝ ⦄ set st i j v ⦃ Q ⦄
```

mvcgen emits each parameter as a named VC (e.g., `vc3.hi`, `vc4.hj`).

### Pattern 2: Local wrappers for opaque specs

When mvcgen can't match an `@[spec]` against a function call (e.g., type-level
arguments like `Impl_2.set 1 u64`, `get_ij 1 u64`), create a local wrapper:

```lean
private def chi_set (st : KeccakState 1 u64) (i j : usize) (v : u64) :=
  Impl_2.set 1 u64 st i j v
-- Unfold lemma: BEFORE irreducible
private theorem chi_set_unfold ... : chi_set st i j v = Impl_2.set 1 u64 st i j v := rfl
-- Spec: applies underlying spec
@[spec] private theorem chi_set_spec ... (hi : ...) (hj : ...) :
    ⦃ ⌜ True ⌝ ⦄ chi_set st i j v ⦃ Q ⦄ := by
  intro _; rw [chi_set_unfold]; exact Impl_2_set_spec st i j v hi hj trivial
-- THEN make irreducible
attribute [irreducible] chi_set
```

Used in: chi proof (chi_set/chi_get), round (round_iota), keccakf1600 (keccak_round),
sponge (lb_get/lb_set for get_ij/set_ij).

### Pattern 3: define → spec → irreducible (strict ordering)

Once a function has `@[spec]`, **immediately** mark it `@[irreducible]`:
```lean
@[spec] theorem foo_spec ... := by ...
attribute [irreducible] Foo.bar  -- or [local irreducible]
```
Without this, mvcgen/simp unfold the body, causing heartbeat blowups.
The `unfold` in the spec proof itself must happen BEFORE the attribute is set.

### Pattern 4: Unfold → hax_mvcgen → vc_omega

```lean
@[spec] theorem foo_spec ... := by
  intro _
  unfold Foo.bar
  hax_mvcgen
  all_goals (try vc_omega)
  -- Handle remaining VCs
```

### Pattern 5: Loop invariant swap for fold_range

`fold_range` from extraction has trivial invariants `(fun _ _ => pure true)`.
Swap to real invariants before hax_mvcgen:

```lean
-- Outer loop
rw [show fold_range 0 5 trivial_inv st trivial_body trivial_pureInv =
    fold_range 0 5 real_inv st trivial_body real_pureInv
    from fold_range_inv_irrelevant _ _ _ _ _ _ _ _]
-- Inner loop (inside outer body lambda)
conv in (fun (self : α) (i : USize64) => fold_range 0 5 _ self _ _) =>
  ext self i
  rw [fold_range_inv_irrelevant _ _ _ real_inner_inv _ _ _ real_inner_pureInv]
```

The `pureInv` argument has the form:
```lean
⟨fun acc k => my_invariant acc k, fun _ _ => by intro _; rfl⟩
```

### Pattern 6: Bridge lemmas (element-wise → pure function)

Step specs give element-wise `Array.getD` postconditions. Bridge lemmas
connect them to pure `Vector` functions via `Vector.ext`:

```lean
theorem chi_bridge (sv rv : Vector u64 25)
    (h : ∀ k, k < 25 → rv.toArray.getD k 0 = chi_body_arr sv.toArray k) :
    rv = chi_pure sv := by
  apply Vector.ext; intro k; intro hk
  rw [← Vector.toArray_getD_eq rv k 0 hk, h k hk]
  simp only [chi_pure, Vector.getElem_ofFn, chi_body_arr]
  rw [Vector.toArray_getD_eq _ _ _ (by omega), ...]
```

Key bridge: `Vector.toArray_getD_eq v i d hi : v.toArray.getD i d = v[i]`

### Pattern 7: Postcondition strengthening via Triple.of_entails_right

Strengthen element-wise postconditions to pure function equalities:

```lean
@[spec] theorem impl_chi_pure_spec ... :=
  Std.Do.Triple.of_entails_right _ _ _ _ (impl_chi_spec st) (by
    simp only [Std.Do.PostCond.entails]; constructor
    · exact fun r h => chi_bridge _ _ h
    · simp [Std.Do.ExceptConds.entails])
```

### Pattern 8: Composition via hax_mvcgen + bridges

With all sub-functions irreducible + specs, hax_mvcgen composes them:

```lean
hax_mvcgen  -- decomposes theta → rho → pi → chi → iota
-- Single VC: chain bridge lemmas
rename_i _ _ h_θ _ h_ρ _ h_π _ h_χ _ h_ι
obtain ⟨hst_eq, hd⟩ := h_θ; subst hst_eq
unfold round_pure  -- must be irreducible during hax_mvcgen, unfold after
rw [← iota_bridge ..., ← chi_bridge ..., ← pi_bridge ..., ← rho_theta_bridge ...]
```

**Critical**: Make `round_pure` `@[local irreducible]` so hax_mvcgen doesn't
try to reduce it (causes 6.4M+ heartbeat timeout).

### Pattern 9: grind for USize64 arithmetic

`vc_omega` can't handle goals like `x = y % 5 → x < 5` because
`USize64.reduceToNat` doesn't always reduce in all hypotheses. Use `grind`:

```lean
all_goals (try vc_omega)
· grind  -- closes USize64 modular arithmetic that omega can't
```

### Pattern 10: Trait dispatch resolution

For extracted Rust code with type-class dispatch, resolve trait methods to
concrete implementations before mvcgen:
```lean
simp only [
  libcrux_sha3.traits.Absorb.load_block,
  libcrux_sha3.simd.portable.Impl_1,
  libcrux_sha3.traits.Absorb.AssociatedTypes,
  libcrux_sha3.simd.portable.Impl_1.AssociatedTypes]
```

### Pattern 11: flat_perm transposition for set_ij loops

`set_ij(state, i/5, i%5, v)` writes to flat position `5*(i%5) + i/5`, NOT `i`.
This is a transposition permutation. Define:
```lean
def flat_perm (i : Nat) : Nat := 5 * (i % 5) + i / 5
def flat_perm_inv (k : Nat) : Nat := 5 * (k % 5) + k / 5  -- same formula = involution
```
Prove involution by 25-case exhaustion. Loop invariants must use `flat_perm_inv k < i`
not `k < i`.

## vc_omega macro

```lean
local macro "vc_omega" : tactic =>
  `(tactic| (simp only [USize64.reduceToNat, USize64.size, UInt64.size,
      Vector.size, Vector.size_toArray] at *; omega))
```

Handles: overflow checks, modular bounds, index bounds, USize64 literal reduction.

## USize64.toNat for loop variables

For `(i + 1).toNat` where `i : USize64` and `i.toNat < n`:
```lean
rw [USize64.toNat_add_of_lt (x := k) (y := 1) (by vc_omega)]
```

## What does NOT work

- **sorry.val from `⦃ P ⌝ ⦄` preconditions**: Use `P →` form instead
- **sorry.val from type-level args**: Use local wrappers
- **sorry.val from sorry'd spec proofs**: Expected — disappears when proof filled in
- **simp_all in spec proofs**: Too aggressive; use `simp only`
- **grind for ∀ k < 25**: Generates huge case splits; use `rcases` + 25 cases
- **native_decide after rcases**: "free variables" error; use `native_decide +revert`
- **hax_mvcgen with non-irreducible postcondition types**: Heartbeat timeout from
  reducing pure function definitions; make them irreducible first
- **vc_omega for x = y % n → x < n**: Use `grind` instead

## Heartbeat budget reference

| Proof type | Budget | Example |
|-----------|--------|---------|
| Small primitive | 200K (default) | `veor5q_u64_spec` |
| Iota (1 set+get) | 400K | `impl_iota_spec` |
| Pi/rho sub-step | 1.6M-3.2M | `impl_pi_0_spec` |
| Pi/rho composition | 3.2M-6.4M | `impl_pi_spec`, `impl_rho_spec` |
| Theta | 6.4M | `impl_theta_spec` |
| Chi (nested 5×5 loop) | 6.4M | `impl_chi_spec` |
| XOR loop (sponge) | 3.2M | `xor_loop_spec` |

## File structure

| File | Contents | Build time |
|------|----------|------------|
| `Impl_Spec_Mvcgen.lean` | Pure defs + all step proofs (iota, pi, rho, theta) | ~89s |
| `Impl_Spec_Compose.lean` | Chi proof, bridge lemmas, round + keccak_f | ~2.4s |
| `Impl_Spec_Sponge.lean` | Sponge layer: load_block, absorb, squeeze, keccak1 | WIP |
