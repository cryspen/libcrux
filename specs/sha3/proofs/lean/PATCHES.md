# Patches and Infrastructure for Hax Lean Proofs

This document lists local patches, specs, tactics, and workarounds developed
for the SHA-3 purification proofs. These should be upstreamed to hax-lib.

## 1. Extraction Patches (`hax.sh`)

### Remove `@[hax_spec]` from generated specs
The hax-generated `@[hax_spec]` specs have `ensures := fun _ => pure True`
(uninformative postconditions) and `sorry` proofs. They block `mvcgen` from
using user-provided `@[spec]` triples.

**Patch:** Replace `@[hax_spec]` with a comment in the extraction output.
```bash
t = t.replace('@[hax_spec]', '-- @[hax_spec] -- removed by patch')
```

**Upstream:** Either generate useful postconditions in `@[hax_spec]`, or don't
emit `@[hax_spec]` when the proofs are `sorry`.

### Rename `update_at_usize` for `RustSlice`
The Hax library defines `update_at_usize` only for `RustArray α n`.
The extraction calls it on `RustSlice α` (e.g., in `squeeze_state`).

**Patch:** Rename calls inside `squeeze_state` to `update_at_usize_slice`.
**Upstream:** Add `update_at_usize` overload for `RustSlice` in hax-lib.

### Replace `by hax_construct_pure <;> bv_decide` with `by sorry`
Generated proof tactics often fail. Replaced wholesale.
**Upstream:** Fix `hax_construct_pure` or generate better tactics.

### Remove broken `createi` definition
The extracted `createi` has unsupported `Fn` trait constraints.
**Patch:** Remove it; provide in Stubs.lean.
**Upstream:** Fix Lean backend for `Fn` trait extraction.

## 2. Missing Definitions (`Stubs.lean`)

### `update_at_usize_slice`
```lean
def rust_primitives.hax.monomorphized_update_at.update_at_usize_slice {α}
    (s : RustSlice α) (i : usize) (v : α) : RustM (RustSlice α)
```

### `createi` (array from_fn)
```lean
@[irreducible] def hacspec_sha3.createi (T : Type) (N : usize) (F : Type)
    [...] (f : F) : RustM (RustArray T N)
```

### `core_models.num.Impl_9.rotate_left`
```lean
def core_models.num.Impl_9.rotate_left (x : u64) (n : u32) : RustM u64
```

### `core_models.num.Impl_9.from_le_bytes` / `to_le_bytes`
Little-endian byte conversion for u64.

## 3. `@[spec]` Triples for `mvcgen`

These specs let `mvcgen` decompose monadic code into pure Nat VCs.

### Checked arithmetic (toNat-distributing)
```lean
@[spec] theorem usize_div_spec (a b : usize) :
    ⦃ ⌜ b ≠ 0 ⌝ ⦄ (a /? b) ⦃ ⇓ r => ⌜ r.toNat = a.toNat / b.toNat ⌝ ⦄

@[spec] theorem usize_mod_spec (a b : usize) :
    ⦃ ⌜ b ≠ 0 ⌝ ⦄ (a %? b) ⦃ ⇓ r => ⌜ r.toNat = a.toNat % b.toNat ⌝ ⦄

@[spec] theorem usize_mul_spec (a b : usize) :
    ⦃ ⌜ a.toNat * b.toNat < USize64.size ⌝ ⦄ (a *? b)
    ⦃ ⇓ r => ⌜ r.toNat = a.toNat * b.toNat ⌝ ⦄

@[spec] theorem usize_add_spec (a b : usize) :
    ⦃ ⌜ a.toNat + b.toNat < USize64.size ⌝ ⦄ (a +? b)
    ⦃ ⇓ r => ⌜ r.toNat = a.toNat + b.toNat ⌝ ⦄
```
**Key insight:** Postconditions distribute `toNat` over the operation.
Preconditions guarantee no overflow. After `mvcgen`, all VCs are in pure
`Nat` and closable by `omega`.

**Upstream:** Add to hax-lib's `rust_primitives/ops.lean` alongside
the existing `@[specset int]` specs.

### Array access
```lean
@[spec] theorem getElemResult_usize_spec {α} [Inhabited α] {n : usize}
    (xs : RustArray α n) (i : usize) :
    ⦃ ⌜ i.toNat < n.toNat ⌝ ⦄ xs[i]_?
    ⦃ ⇓ r => ⌜ r = xs.toVec.toArray.getD i.toNat default ⌝ ⦄
```
**Upstream:** Add to hax-lib's `GetElemResult` module.

### `createi` (array construction)
```lean
@[spec] axiom createi.spec_triple (T : Type) (N : usize)
    (f : usize → RustM T) (f_pure : Fin N.toNat → T) [...] 
    (hf : ∀ (i : usize) (hi : i.toNat < N.toNat),
      ⦃ ⌜ True ⌝ ⦄ f i ⦃ ⇓ r => ⌜ r = f_pure ⟨i.toNat, hi⟩ ⌝ ⦄) :
    ⦃ ⌜ True ⌝ ⦄ createi T N (usize → RustM T) f
    ⦃ ⇓ r => ⌜ r = ⟨Vector.ofFn f_pure⟩ ⌝ ⦄
```
**Upstream:** Implement `createi` properly and prove this spec.

### Domain-specific: `get` (Keccak state access)
```lean
@[spec] theorem get_spec (st : RustArray u64 25) (x y : usize) :
    ⦃ ⌜ x.toNat < 5 ∧ y.toNat < 5 ⌝ ⦄ get st x y
    ⦃ ⇓ r => ⌜ r = st.toVec.toArray.getD (5 * x.toNat + y.toNat) 0 ⌝ ⦄
```

## 4. Tactics and Macros

### `close_vc` — Universal VC closer
```lean
macro "close_vc" : tactic => `(tactic| (
  try simp only [
    show (0 : USize64).toNat = 0 from by native_decide,
    show (1 : USize64).toNat = 1 from by native_decide,
    -- ... (all USize64 literal constants used in the spec)
    show (25 : USize64).toNat = 25 from by native_decide,
    show USize64.size = 2 ^ 64 from rfl] at *;
  first | omega
    | (intro h; subst h; congr 1; omega)
    | (constructor <;> omega)
    | (intro; subst_vars; rfl)
    | (subst_vars; congr <;> omega)))
```

**What it does:**
1. Normalizes `USize64.toNat` of literal constants to `Nat` values
2. Normalizes `USize64.size` to `2^64`
3. Tries `omega` (most arithmetic VCs)
4. Tries `intro; subst; congr; omega` (postcondition index matching)
5. Tries `constructor <;> omega` (conjunction VCs like `x < 5 ∧ y < 5`)
6. Tries `subst_vars; rfl` (simple equality VCs)
7. Tries `subst_vars; congr <;> omega` (complex equality with index arithmetic)

**Upstream:** Could be a `hax_close_vc` tactic in hax-lib.

### Proof pattern for step functions
```lean
set_option maxHeartbeats 6400000 in
@[spec] theorem step_spec (st : RustArray u64 25) :
    ⦃ ⌜ True ⌝ ⦄ step st ⦃ ⇓ r => ⌜ r = ⟨step_pure st.toVec⟩ ⌝ ⦄ := by
  intro _; unfold step step_pure
  hax_mvcgen [usize_div_spec, usize_mod_spec, usize_mul_spec, usize_add_spec, get_spec]
  all_goals close_vc
```

**Pattern:** unfold both monadic and pure defs → `hax_mvcgen` with arithmetic + get specs → `close_vc` on all VCs.

### Proof pattern for composition
```lean
@[spec] theorem round_spec (...) :
    ⦃ ⌜ True ⌝ ⦄ (do ...) ⦃ ⇓ r => ⌜ r = ⟨round_pure ...⟩ ⌝ ⦄ := by
  intro _; mvcgen  -- picks up @[spec] step specs as black boxes
  all_goals (first | (intro; unfold round_pure; subst_vars; rfl) | close_vc | sorry)
```

## 5. Design Decisions

### `@[irreducible]` on pure definitions
Without this, composing step functions (e.g., `round_pure = iota ∘ chi ∘ pi ∘ rho ∘ theta`) causes the kernel to normalize nested `Vector.ofFn` terms, timing out at 1.6M heartbeats. With `@[irreducible]`, composition runs in ~1.6M heartbeats.

### `getD` instead of `GetElem` in postconditions
Using `xs.toVec[i]` (bounded access) in postconditions requires a bound proof at declaration time, but the bound comes from the precondition which isn't in scope. Using `xs.toVec.toArray.getD i default` avoids this — it's total and equals the bounded version when in bounds.

### Specs as explicit `hax_mvcgen` hints
`@[spec]`-tagged triples ARE picked up by `mvcgen` for top-level function calls. But for operators like `/?`, `%?`, `*?`, `+?`, they must be passed as explicit `hax_mvcgen [spec1, spec2, ...]` hints. This is because the operators are defined via typeclass instances, and `mvcgen` doesn't automatically search for specs on typeclass methods.

## 6. Known Limitations

- `usize_mul_spec` and `usize_add_spec` are axiomatized because the
  precondition `⌜ P ⌝` uses `PLift` which `intro ⟨h⟩` can't destructure
  for `Nat.lt` (two constructors). Provable with manual wp manipulation.

- `keccak_f_spec` needs a `@[spec]` triple for `fold_range` to handle
  the 24-round loop.

- The `close_vc` macro requires listing all USize64 literal constants
  used in the spec. A more robust approach would normalize ALL USize64
  literals via a custom simp procedure.
