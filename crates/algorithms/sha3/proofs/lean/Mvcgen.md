# mvcgen Observations

## What mvcgen does well

1. **Small self-contained proofs**: For functions that unfold to a short chain of
   checked operations (`*?`, `+?`, `^^^?`, `[i]_?`), mvcgen decomposes the monadic
   chain and produces verification conditions (VCs) that close with `omega` or `simp`.

   Examples: `veor5q_u64_spec`, `vbcaxq_u64_spec`, `veorq_n_u64_spec`.

2. **Iota proof**: After manually unfolding `Impl_2.iota`, `Impl_2.set`, `set_ij`,
   `update_at_usize`, `get_ij`, and the KeccakItem trait to concrete portable
   operations, mvcgen decomposed the ~10-step monadic chain into ~8 VCs, all
   closable with `vc_omega` (a macro for `simp only [...] at *; omega`) plus
   manual `Vector.getElem_set` reasoning for the result equality VC.

## Where mvcgen fails

### 1. Conjunction preconditions produce `sorry.val`

**Problem**: When an `@[spec]` theorem has a conjunction precondition like
`⦃ ⌜ i.toNat < 5 ∧ j.toNat < 5 ⌝ ⦄`, mvcgen matches the spec but can't
auto-discharge the conjunction from separate hypotheses in context
(`hi : i.toNat < 5` and `hj : j.toNat < 5`). It generates `sorry.val` as
a placeholder.

**Impact**: `sorry.val` appears in two places:
- As a **goal** (the precondition obligation) — closable manually via
  `exact ⟨by vc_omega, by vc_omega⟩`
- As a **hypothesis** on downstream results — `h✝ : sorry.val r✝` — this
  is opaque and makes postcondition proofs impossible.

**Example**: In `impl_pi_0_spec`, after `unfold Impl_2.pi_0; mvcgen`, the
final postcondition VC has hypotheses like:
```
r✝ : KeccakState 1 u64
h✝ : sorry.val r✝   -- ← opaque, we don't know anything about r✝.st
⊢ r✝.st.toVec.toArray.getD 1 0 = old.st.toVec.toArray.getD 15 0
```
The `sorry.val r✝` hypothesis is supposed to be the postcondition of
`Impl_2_set_spec`, but because mvcgen failed to resolve the precondition,
the entire postcondition is also `sorry.val` and provides no information.

**Affected specs**: `set_ij_spec`, `Impl_2_set_spec`, `KeccakState_getElem_spec`
— all have `⌜ i.toNat < 5 ∧ j.toNat < 5 ⌝` preconditions.

### 2. Heartbeat budget for large functions

**Problem**: For functions with many sequential operations (e.g., `Impl_2.pi`
with 24 `set` + 24 `get` calls), mvcgen times out even at `maxHeartbeats 6400000`.

**Root cause**: mvcgen tries to decompose the entire monadic chain at once.
Each operation generates multiple VCs (arithmetic overflow, bounds check,
result equality), leading to exponential growth.

### 3. USize64 literal reduction

**Problem**: mvcgen leaves `USize64.toNat 5`, `USize64.toNat 25`, etc. unreduced.
`omega` can't reason about these opaque values. Requires post-mvcgen `simp only
[USize64.reduceToNat]` or `vc_omega` to reduce literals.

Similarly, `USize64.size` doesn't reduce for overflow VCs. Need `simp only
[USize64.size, UInt64.size]` to get the concrete bound `18446744073709551616`.

### 4. Array.getD vs Vector.getElem mismatch

**Problem**: `getElemResult_usize_spec` gives postconditions in terms of
`Array.getD` (with a default value), but `Vector.set`/`Vector.getElem_set`
work with `Vector.getElem`. Bridging these requires manual `simp [Array.getD, h]`
proofs that are tedious.

## Recommended approach

For **small proofs** (1-3 monadic operations): use mvcgen.

For **composite proofs** (chaining multiple `@[spec]` functions): use
`Triple.bind`/`Triple.pure` to compose specs directly, avoiding mvcgen's
precondition resolution issues entirely.
