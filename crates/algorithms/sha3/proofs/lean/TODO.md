# Plan: Close remaining 2 sorries in keccak1_spec

## Current state (2026-04-11)

File `Impl_Spec_Sponge.lean` compiles cleanly with 2 `sorry`s in `keccak1_spec` (lines ~1451, ~1455) plus 1 `sorry` in `load_last_spec` (line ~1039, separate theorem).

### Completed (Steps 1–4)

- **Step 1**: Extended `store_loop_inv` with `orig_out : List u8` parameter and preservation conjunct:
  `∀ b, b < out_size → (b < start ∨ b ≥ start + 8 * i) → cur_out.toList.getD b 0 = orig_out.getD b 0`

- **Step 2**: Strengthened `store_block_spec` postcondition to include preservation:
  `∀ b, b < out.val.size → (b < start ∨ b ≥ start + len) → r.getD b = out.getD b`
  Updated fold_range invariant calls to pass `out.val.toList`. Fixed all VCs (vc3 init, vc18 loop step with preservation branch, vc35 remainder composition with preservation, vc36 no-remainder with preservation passthrough).

- **Step 3**: Strengthened `squeeze_spec` postcondition identically (passthrough from store_block_spec).

- **Step 4**: Deleted `store_block_preserves` (~100 lines) and `squeeze_preserves` (~15 lines) — both subsumed by the strengthened `@[spec]` theorems.

- **Step 5 partial**: Updated `keccak1_spec` to handle the triple conjunction from squeeze_spec:
  - `vc25.hinit`: updated to `obtain ⟨hsize, helems, _⟩ := ‹_ ∧ _ ∧ _›`
  - `vc20` (single squeeze): same update
  - `vc36` (no-remainder composition): updated to pass through preservation

### Remaining: vc30 and vc35 in keccak1_spec

Both are `sorry` and need the squeeze preservation hypothesis to prove byte correctness.

**vc30** (squeeze loop step): Prove `squeeze_loop_inv` at `i+1` from invariant at `i`.
- Size: from squeeze size + IH size
- State: `Nat.repeat_succ` + keccakf + IH state
- Bytes: case split on `b < i*RATE` (preserved → IH) vs `b ≥ i*RATE` (written by squeeze → connect via `squeeze_pure_getD` + `absorb_state_connection`)
- Key arithmetic: `b / RATE = i` when `i*RATE ≤ b < (i+1)*RATE`

**vc35** (composition with remainder): Prove final output = `keccak1_pure`.
- Use `list_eq_of_getD` for list equality
- Old bytes (`b < output_blocks * RATE`): preserved by final squeeze → IH from loop
- New bytes (`b ≥ output_blocks * RATE`): written by final squeeze → connect via `squeeze_pure_getD`
- Key arithmetic: `b / RATE = output_blocks` when `output_blocks * RATE ≤ b < output.size`

### Proof difficulty: hypothesis wrangling

The main challenge is NOT the math but the mvcgen-generated context with ~35 anonymous bindings. `rename_i` is fragile; use type-based matching instead:
```lean
have h_inv := ‹squeeze_loop_inv RATE DELIM input output _ _›
unfold squeeze_loop_inv at h_inv
obtain ⟨h_size, h_state, h_bytes⟩ := h_inv
have hkf : _ = keccak_f_pure _ := ‹_›
obtain ⟨h_new_size, h_new_bytes, h_pres⟩ := ‹_ ∧ _ ∧ _›
```

CAUTION: There are TWO triples in context (init squeeze h✝⁴ and step squeeze h✝¹). After consuming h_inv, `‹_ ∧ _ ∧ _›` should match the most recent (step squeeze), but verify with `lean_goal`.

### Key lemmas

1. `Nat.repeat_succ`: `Nat.repeat f (n+1) x = f (Nat.repeat f n x)`
2. `Sponge.squeeze_pure_getD`: connects squeeze_pure bytes to lane_byte + state iteration
3. `absorb_state_connection`: connects mvcgen variables to `keccak1_absorb_state`
4. `Sponge.keccak1_pure_eq_squeeze`: `keccak1_pure = squeeze_pure ∘ absorb_state`
5. `Nat.div_eq_of_lt_le`: division result when bounds known
6. `usize_add_lt`: USize64 add fits in 2^64

### Build command

```bash
lake build 2>&1 | tee /tmp/build_keccak1.txt
```

Build takes ~90s.
