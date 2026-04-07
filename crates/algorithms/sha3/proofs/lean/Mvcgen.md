# mvcgen Proof Strategies

## What mvcgen does well

1. **Small self-contained proofs**: For functions that unfold to a short chain of
   checked operations (`*?`, `+?`, `^^^?`, `[i]_?`), mvcgen decomposes the monadic
   chain and produces verification conditions (VCs) that close with `omega` or `simp`.

   Examples: `veor5q_u64_spec`, `vbcaxq_u64_spec`, `veorq_n_u64_spec`.

2. **Iota proof**: After manually unfolding `Impl_2.iota`, `Impl_2.set`, `set_ij`,
   `update_at_usize`, `get_ij`, and the KeccakItem trait to concrete portable
   operations, mvcgen decomposed the ~10-step monadic chain into ~8 VCs, all
   closable with `vc_omega` plus manual `Vector.getElem_set` reasoning.

3. **Composition with irreducible sub-steps**: When sub-functions are `@[irreducible]`
   and have `@[spec]` lemmas, mvcgen sees opaque calls and composes specs directly.
   Pi composition (5 steps) completes at 3.2M heartbeats; rho composition at 6.4M.

## Where mvcgen fails

### 1. Conjunction preconditions produce `sorry.val`

**Problem**: When an `@[spec]` theorem has a conjunction precondition like
`⦃ ⌜ i.toNat < 5 ∧ j.toNat < 5 ⌝ ⦄`, mvcgen matches the spec but can't
auto-discharge the conjunction from separate hypotheses in context.
It generates `sorry.val` as a placeholder.

**Impact**: `sorry.val` appears in two places:
- As a **goal** (the precondition obligation) — closable manually via
  `exact ⟨by vc_omega, by vc_omega⟩`
- As a **hypothesis** on downstream results — `h✝ : sorry.val r✝` — this
  is opaque and makes postcondition proofs impossible.

### 2. Extra parameters on @[spec] theorems cause sorry.val

**Problem**: `sorry.val` is caused by ANY parameter on an `@[spec]` theorem
that mvcgen can't auto-fill — not just conjunction preconditions. Even with
`⌜ True ⌝` precondition, extra explicit parameters like `(hi : i.toNat < 5)`
generate `sorry.val` because mvcgen can't synthesize them.

**Solution**: Remove extra params, embed ALL constraints in `⌜ precondition ⌝`.
Or use conditional postcondition: `⌜ i < 5 → j < 5 → r = val ⌝`.

### 3. Heartbeat budget for large functions

For functions with many sequential operations (e.g., `Impl_2.pi` with 24
`set` + 24 `get` calls), mvcgen times out even at `maxHeartbeats 6400000`.

**Root cause**: mvcgen tries to decompose the entire monadic chain at once.
Each operation generates multiple VCs, leading to exponential growth.

**Solution**: Split into sub-functions, prove specs for each, mark `@[irreducible]`,
then mvcgen composes the opaque sub-steps cheaply.

### 4. USize64 literal reduction

mvcgen leaves `USize64.toNat 5`, `USize64.toNat 25`, etc. unreduced.
`omega` can't reason about these opaque values. Requires `vc_omega`:
```lean
local macro "vc_omega" : tactic =>
  `(tactic| (simp only [USize64.reduceToNat, USize64.size, UInt64.size,
      Vector.size, Vector.size_toArray] at *; omega))
```

**Important**: `USize64.reduceToNat` is a `DSimproc`. It works with both `dsimp`
and `simp`, but in large contexts (60+ hypotheses), `simp only [...] at *` can
run out of heartbeats silently, leaving hypotheses unreduced. Prefer applying
it on the goal only (`simp only [USize64.reduceToNat, ...]` without `at *`)
and using `*` to chain through hypothesis values as rewrite rules.

### 5. Array.getD vs Vector.getElem mismatch

`getElemResult_usize_spec` gives postconditions in terms of `Array.getD`
(with a default value), but `Vector.set`/`Vector.getElem_set` work with
`Vector.getElem`. Bridge with:
```lean
theorem Vector.toArray_getD_eq (v : Vector α n) (i : Nat) (d : α) (hi : i < n) :
    v.toArray.getD i d = v[i]
```

### 6. Composition works best with single-equality postconditions

The legacy `round_spec` composed theta/rho/pi/chi/iota at 1.6M heartbeats because
each step's postcondition was `⌜ r = ⟨pure_fn input⟩ ⌝`. mvcgen chains these by
`subst_vars; rfl`. Conjunction postconditions prevent this substitution.

**Rule**: For functions that will be composed, use `⌜ r = f(input) ⌝` postconditions.
For functions with frame conditions, use conjunction but handle composition manually.

---

## Proven proof patterns

### Pattern 1: Unfold → mvcgen → vc_omega (basic)

For small functions (1-10 monadic operations):
```lean
@[spec] theorem foo_spec ... := by
  intro _
  unfold Foo.bar
  mvcgen
  all_goals (try vc_omega)
  -- Handle remaining VCs individually
```

### Pattern 2: @[irreducible] after spec

Once a function has `@[spec]`, mark it `@[irreducible]`:
```lean
@[spec] theorem foo_spec ... := by ...
attribute [local irreducible] Foo.bar
```
**Why**: Without `@[irreducible]`, `wp_bind`, `mvcgen`, and `simp`/`dsimp` can
unfold the function body, creating huge terms. This causes heartbeat timeouts
in composition proofs. With opaque sub-functions, mvcgen completes instantly.

**Important**: `unfold foo` in the spec proof itself must happen BEFORE the
`@[irreducible]` attribute is set.

### Pattern 3: Trait dispatch simp

For extracted Rust code with type-class dispatch, resolve trait methods to
concrete implementations before mvcgen:
```lean
simp only [
  libcrux_sha3.traits.KeccakItem.xor5,
  libcrux_sha3.traits.KeccakItem.rotate_left1_and_xor,
  libcrux_sha3.simd.portable.Impl]
mvcgen
```
Only unfold trait dispatch — leave everything else opaque for mvcgen to use specs.

### Pattern 4: modifies_only frame conditions

For sub-step proofs that write specific positions, add frame conditions:
```lean
def modifies_only5 (r self : RustArray u64 25) (i₁ i₂ i₃ i₄ i₅ : Nat) : Prop :=
  ∀ k, k < 25 → k ≠ i₁ → k ≠ i₂ → k ≠ i₃ → k ≠ i₄ → k ≠ i₅ →
    r.toVec.toArray.getD k 0 = self.toVec.toArray.getD k 0
```
Postconditions: written position values ∧ `modifies_only` frame.

### Pattern 5: Composition via rcases + frame chain

For composing 5 sub-steps (e.g., pi = pi_0;...;pi_4):

1. Mark sub-steps `@[irreducible]`, run `mvcgen` on the composition
2. `obtain` the postcondition conjuncts from each sub-step
3. `simp only [modifies_only4, modifies_only5]` to unfold frame predicates
4. `rcases k` into all 25 concrete values
5. Chain frame conditions via `.trans`:
```lean
-- Position unchanged through all 5 steps:
exact (h4f k ...).trans ((h3f k ...).trans ((h2f k ...).trans ((h1f k ...).trans (h0f k ...))))
-- Position written by step 2:
exact (h4f k ...).trans ((h3f k ...).trans ((h2f k ...).trans ‹_›))
```

**Rho enhancement**: When sub-step k depends on the output of step k-1 (not on the
original `self`), rewrite written-position hypotheses via frame chains to reference
the original state:
```lean
rw [h0f 5 (by omega) ...] at h1a      -- rewrite rho_1 hyp via rho_0 frame
rw [h1f 10 ..., h0f 10 ...] at h2a    -- 2-step rewrite for rho_2
```

### Pattern 6: Theta d-value closing (complex mvcgen postcondition)

When mvcgen produces a postcondition with unresolved USize64 index chains
and the goal involves `Array.getD` on a concrete array:

```lean
subst_vars
rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 by omega) with
  rfl | rfl | rfl | rfl | rfl <;>
(simp only [*, USize64.reduceToNat, Nat.reduceMul, Nat.reduceAdd, Nat.reduceMod,
  Nat.reduceLT, ↓reduceDIte,
  theta_d_arr, theta_c_arr, rotate_left_pure, Array.getD,
  Vector.size_toArray, List.size_toArray, List.length_cons, List.length_nil]
 <;> rfl)
```

Key lemmas for reducing concrete array operations:
- `USize64.reduceToNat` — reduce `USize64.toNat (literal)` to Nat
- `Nat.reduceLT` + `↓reduceDIte` — decide `dite` conditions like `0 < 25`
- `List.size_toArray` + `List.length_cons` + `List.length_nil` — compute
  `#[a,b,c,d,e].size = 5` (array literals are `List.toArray`)
- `Vector.size_toArray` — compute `v.toArray.size = n` for `v : Vector α n`
- `rfl` as final closer — `Array.getInternal` on a concrete literal with
  concrete index reduces by definitional computation

**Important**: `simp only [*, ...]` (without `at *`) uses hypotheses as rewrite
rules on the goal. This chains through `USize64.toNat` hypothesis equalities:
```
h₁ : USize64.toNat r₁ = USize64.toNat 0 + USize64.toNat 4
h₂ : USize64.toNat r₂ = USize64.toNat r₁ % USize64.toNat 5
```
simp rewrites `r₂ → chain → 4` in the goal, then `USize64.reduceToNat` reduces
the resulting USize64 literals.

### Pattern 7: Assertion failure VCs

When the Rust code has `debug_assert!(LEFT + RIGHT == 64)`, mvcgen produces
two branches: success and failure. The failure branch goal is
`wp⟦RustM.fail⟧ (postcond)` with a hypothesis `¬(LEFT+RIGHT == 64) = true`.

Close with: `exfalso; simp_all [BEq.beq]` (concrete check contradicts).
Or the catch-all: `all_goals (first | vc_omega | sorry)`.

### Pattern 8: Reusable tactic macros

For repetitive sub-step proofs (e.g., pi_0..pi_4, rho_0..rho_4), define macros:
```lean
local macro "pi_step_proof" : tactic => `(tactic| (
  intro _; unfold Impl_2.pi_0 -- or pi_1, etc.
  simp only [libcrux_sha3.traits.set_ij, ...]
  mvcgen
  all_goals (try vc_omega)
  ...))
```
Each macro encapsulates the full proof pattern. Different step proofs share the
same structure but differ in which function is unfolded and which positions are written.

---

## What does NOT work

### simp_all in spec proofs
`simp_all` is too aggressive when `@[spec]` and `@[simp]` interact. It can
unfold things it shouldn't or loop. Always use `simp only` with targeted lemma lists.

### grind for ∀ k < 25 frame composition
`grind` can close frame condition chains at **concrete** index values
(k=1, k=5 etc.) and small conjunctions of 3-4 such equalities. But it **fails**
on `∀ k < 25, r[k] = st[perm[k]]` — it generates huge Int8/Int16/Int32/Int64
case splits. Use `rcases` into concrete values instead.

### dsimp only [USize64.reduceToNat] at *
Despite `USize64.reduceToNat` being a `DSimproc`, `dsimp only [USize64.reduceToNat] at *`
does NOT reliably reduce `USize64.toNat` literals in large contexts (60+ hypotheses).
It seems to silently exhaust heartbeats. Use `simp only [USize64.reduceToNat]` instead,
or better, avoid `at *` entirely and let `simp only [*, USize64.reduceToNat, ...]`
chain through hypotheses on the goal.

### simp only [USize64.reduceToNat, ...] at * for large contexts
Even `simp only` with `at *` can fail to reduce all USize64 literals when there
are 60+ hypotheses — the heartbeat budget is consumed processing earlier hypotheses.
The fix: don't use `at *`. Use `simp only [*, USize64.reduceToNat, ...]` on the
goal only. The `*` makes hypotheses available as rewrite rules without processing
each one independently.

### Array.getD without dite reduction
`simp only [Array.getD]` unfolds to `if h : i < a.size then a.getInternal i h else default`.
Without `Nat.reduceLT` + `↓reduceDIte`, the `dite` condition is not decided and
the proof gets stuck with `if h : 0 < 25 then ... else ...`.

### Array literal size without List lemmas
`#[a,b,c,d,e].size` is `[a,b,c,d,e].toArray.size`. This does NOT reduce with
`Array.size_push` + `Array.size_empty` (wrong decomposition). Instead need:
`List.size_toArray` + `List.length_cons` + `List.length_nil`.

### Single-pass simp for definition unfolding + hypothesis chaining
Trying to do everything in one `simp only [*, theta_d_arr, ..., Array.getD, ...]`
call often creates huge intermediate terms (dite + getInternal chains) without
closing. Better: case-split first (`rcases j`), then per-case simp + `rfl`.

---

## Heartbeat budget reference

| Proof type | Budget | Example |
|-----------|--------|---------|
| Small primitive | 200K (default) | `veor5q_u64_spec` |
| Iota (1 set+get) | 400K | `impl_iota_spec` |
| Pi/rho sub-step | 1.6M-3.2M | `impl_pi_0_spec`, `impl_rho_0_spec` |
| Pi composition | 3.2M | `impl_pi_spec` |
| Rho composition | 6.4M | `impl_rho_spec` |
| Theta | 6.4M | `impl_theta_spec` |

## File structure

| File | Contents | Build time |
|------|----------|------------|
| `Impl_Spec_Mvcgen.lean` | Pure defs + all step proofs (iota, pi, rho, theta) | ~90s |
| `Impl_Spec_Compose.lean` | Imports above; chi, round, keccak_f (TODO) | <1s |

Editing `Impl_Spec_Compose.lean` does not recompile `Impl_Spec_Mvcgen.lean`.
