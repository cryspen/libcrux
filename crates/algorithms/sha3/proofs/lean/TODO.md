# Plan: Prove keccak1_spec — remove all 12 remaining sorries

## Context

`keccak1_spec` has 12 remaining goals after `hax_mvcgen`:
- **9 arithmetic VCs** (bounds, overflow, size) — closeable with better tactics
- **3 composition VCs** (vc20, vc35, vc36) — fundamentally unprovable because the absorb loop and squeeze loop have `True` invariants, so mvcgen can't propagate postconditions through them

**Root cause**: The extracted code's `fold_range` calls use trivial invariants `⟨fun _ _ => True, sorry⟩`. After mvcgen decomposes the function, the loop results are free variables with no constraints. The composition VCs need to connect the implementation output to `keccak1_pure`, but can't without knowing what the loops computed.

**Fix**: Use `fold_range_inv_irrelevant` (Mvcgen.md Pattern 5) to swap real invariants into both loops BEFORE `hax_mvcgen`. Then mvcgen can propagate postconditions and the composition VCs become provable.

## Critical files

- **Main file**: `Impl_Spec_Sponge.lean` — all edits here
- **Reference**: `Impl_Spec_Compose.lean` — `fold_range_inv_irrelevant`, `fold_range_usize_spec` (lines 90-141)
- **Extracted code**: `extraction/libcrux_sha3.lean` — `keccak1` at line 3747
- **Patterns**: `Mvcgen.md` — Pattern 2 (wrappers), Pattern 5 (invariant swap)

## Implementation plan

### Phase 1: Helper definitions and lemmas (~line 96, after pure defs)

1. **`keccak1_absorb_state`** — pure function computing state after absorb phase:
   ```lean
   private noncomputable def keccak1_absorb_state (RATE : Nat) (DELIM : u8) (input : List u8) : Vector u64 25 :=
     let n := input.length / RATE
     let st0 := Vector.replicate 25 (0 : u64)
     let st1 := absorb_all_pure RATE st0 input n
     absorb_final_pure RATE DELIM st1 input (input.length - input.length % RATE) (input.length % RATE)
   ```

2. **`absorb_all_pure_zero`**: `absorb_all_pure RATE state input 0 = state`
   - Proof: `simp [absorb_all_pure]`

3. **`absorb_all_pure_succ`**: `absorb_all_pure RATE state input (i+1) = absorb_block_pure RATE (absorb_all_pure RATE state input i) input (i * RATE)`
   - Proof: unfold, `List.range_succ`, `List.foldl_append`, simp

4. **`new_state_is_replicate`**: bridge `(∀ k < 25, v.toArray.getD k 0 = 0) → v = Vector.replicate 25 0`
   - Proof: `Vector.ext` + `Vector.toArray_getD_eq`

### Phase 2: Strengthen store_block/squeeze with byte preservation

5. **`store_block_preserves`** — separate theorem (not @[spec]):
   ```lean
   theorem store_block_preserves (RATE : usize) (s : RustArray u64 25) (out : RustSlice u8) (start len : usize) ... :
     ⦃ ⌜ True ⌝ ⦄ store_block RATE s out start len
     ⦃ ⇓ r => ⌜ ... ∧ (∀ b, b < out.val.size → (b < start.toNat ∨ b ≥ start.toNat + len.toNat) → 
       r.val.toList.getD b 0 = out.val.toList.getD b 0) ⌝ ⦄
   ```
   - Proof: extend existing store_block_spec proof using `splice_seq_getD`'s else case

6. **`squeeze_preserves`** — wraps store_block_preserves for Squeeze.squeeze

### Phase 3: Absorb loop wrapper (~line 980, before keccak1_spec helpers)

7. **Define `keccak1_absorb_loop`**: wraps the absorb fold_range with a real invariant
   ```lean
   private def keccak1_absorb_loop (RATE : usize) (s : KeccakState 1 u64) 
       (input : RustSlice u8) (n_blocks : usize) : RustM (KeccakState 1 u64) :=
     fold_range 0 n_blocks
       (fun (st : KeccakState 1 u64) (k : USize64) =>
         pure (st.st.toVec = absorb_all_pure RATE.toNat s.st.toVec input.val.toList k.toNat))
       s
       (fun s i => do ...)
       ⟨fun st k => st.st.toVec = ..., fun _ _ => by intro _; rfl⟩
   ```

8. **`keccak1_absorb_loop_eq`**: unfold lemma using `fold_range_inv_irrelevant`
   ```lean
   fold_range 0 n_blocks inv s body pureInv = keccak1_absorb_loop RATE s input n_blocks
   ```

9. **`@[spec] keccak1_absorb_loop_spec`**: prove using `fold_range_inv_irrelevant` + `hax_mvcgen` internally (following byte_loop_spec pattern)
   - Base VC: `absorb_all_pure ... 0 = s.st.toVec` via `absorb_all_pure_zero`
   - Step VC: `absorb_block_pure (absorb_all_pure ... i) ... = absorb_all_pure ... (i+1)` via `absorb_all_pure_succ`
   - Arithmetic VCs: bridge lemmas + omega
   - Postcondition: `r.st.toVec = absorb_all_pure RATE.toNat s.st.toVec input.val.toList n_blocks.toNat`

10. **`attribute [irreducible] keccak1_absorb_loop`**

### Phase 4: Squeeze loop wrapper

11. **Define `keccak1_squeeze_loop`**: wraps the squeeze fold_range. Invariant tracks:
    - `pair._0.val.size = output_size` (size preservation)
    - `pair._1.st.toVec = Function.iterate keccak_f_pure (k-1) state0` (state tracking)
    - `∀ b < k * RATE, pair._0.val.toList.getD b 0 = (keccak1_pure RATE DELIM input output_size).getD b 0` (byte correctness)

    Where `state0` comes from the wrapper's parameter (= keccak1_absorb_state).

12. **`keccak1_squeeze_loop_eq`**: unfold lemma

13. **`@[spec] keccak1_squeeze_loop_spec`**: prove using:
    - Base VC: first squeeze gave correct bytes at [0, RATE)
    - Step VC: keccakf1600_spec → state update; squeeze_preserves → old bytes preserved; squeeze_spec → new bytes correct
    - Bridge: connect lane_byte from squeeze_spec to keccak1_pure bytes (via squeeze_pure unfolding)

14. **`attribute [irreducible] keccak1_squeeze_loop`**

### Phase 5: Rewrite keccak1_spec

```lean
theorem keccak1_spec ... := by
  intro _
  unfold keccak1
  simp only [keccak1_absorb_loop_eq, keccak1_squeeze_loop_eq]
  hax_mvcgen [-Impl_2.absorb_block.spec.contract, -Impl_2.absorb_final.spec.contract]
  -- Phase 1: standard VC closure
  all_goals (try vc_omega)
  all_goals (try grind)
  ...
  -- Composition VCs: now closeable because mvcgen has real loop postconditions
  -- vc20 (single squeeze): unfold keccak1_pure, use absorb + squeeze postconditions
  -- vc35/vc36 (multi squeeze): use squeeze_loop postcondition + optional remainder
```

### Phase 6: List extensionality for composition VCs

15. **`list_eq_of_getD`** or use `List.ext_getElem`:
    - From `h_size : l.length = r.length` and `h_elems : ∀ i < l.length, l.getD i d = r.getD i d`
    - Conclude `l = r`
    - Used to close vc20, vc35, vc36 from pointwise byte match + size equality

16. **`keccak1_pure_squeeze`**: `keccak1_pure RATE DELIM input output_len = squeeze_pure RATE (keccak1_absorb_state RATE DELIM input) output_len` (when RATE > 0)

17. **`squeeze_pure_getD`**: access lemma for squeeze_pure bytes at specific positions, connecting to store_block_pure/lane_byte

## Verification

1. Run `lake env lean Impl_Spec_Sponge.lean 2>&1 | tee /tmp/build_keccak1.txt` and check for errors
2. Grep for `sorry` in `Impl_Spec_Sponge.lean` — should only appear in `load_last_spec` (vc17)
3. Check `lean_diagnostic_messages` for the file — no new errors

## Risk / complexity

- **Highest risk**: Step 13 (squeeze_loop_spec). Proving the byte invariant step requires connecting squeeze_spec's lane_byte output to keccak1_pure's byte positions. This involves unfolding squeeze_pure/store_block_pure and matching. May need 200-400 lines.
- **Medium risk**: Step 9 (absorb_loop_spec). Should follow byte_loop_spec pattern closely. ~50 lines.
- **Low risk**: Steps 1-6, 15-17 (helpers/bridges). Standard. ~100 lines total.
- **Total estimate**: ~400-600 lines of new proof code.
