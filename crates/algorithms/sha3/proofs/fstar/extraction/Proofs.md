# F* Proof Patterns for hax-Extracted Crypto Code

Lessons learned from proving `Impl_Spec_Keccakf.fst` — the equivalence between
the libcrux SHA-3 Keccak-f[1600] implementation (hax-extracted F*) and the
hacspec specification. These patterns apply broadly to F* proofs of
hax-extracted Rust crypto code.

## Project Structure

### Proof Architecture: Phased Equivalence

Break the proof into phases matching the algorithm's structure:

1. **Primitive operations** — show impl's typeclass methods equal spec's operations
2. **State accessors** — show impl's indexing matches spec's indexing (watch for transpositions)
3. **Constants** — show impl's and spec's constant arrays are equal
4. **Per-step equivalence** — one lemma per algorithmic step (theta, rho, pi, chi, iota)
5. **Composition** — chain per-step lemmas into full-round and full-algorithm equivalence

Each phase builds on the previous ones. Keep phases isolated with
`#push-options`/`#pop-options` so solver settings don't leak.

### File Layout

```fstar
module Impl_Spec_Keccakf

#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"  (* conservative global defaults *)

(* Phase 1: primitives — all = () *)
(* Phase 2: accessors — all = () *)
(* Phase 3: constants — assert_norm *)
(* ... *)
(* Phase N: main theorem — composition *)
```

## Solver Settings: fuel, ifuel, z3rlimit

### Defaults

Always start with conservative global defaults:
```fstar
#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"
```

Only raise settings per-lemma with `#push-options` / `#pop-options`.
**Never omit `#pop-options`** — leaked settings (especially `--split_queries always`)
will silently break later lemmas.

### What each setting controls

| Setting | Controls | When to increase |
|---------|----------|-----------------|
| `--fuel N` | How many times recursive functions unfold | Recursive function definitions, `fold_range` |
| `--ifuel N` | How many times inductive types are destructed | Pattern matching, discriminators |
| `--z3rlimit N` | Z3 time budget (N × 2 = rlimit in query-stats) | Complex SMT reasoning |
| `--split_queries always` | Each assertion becomes a separate Z3 query | Large postconditions, `createi`-based specs |

### Fuel guidelines

- **fuel 0**: Definitional equalities, typeclass unfolding, simple SMT
- **fuel 1**: One-step recursive unfolding (e.g., `lemma_fold_range_step`, inductive proofs)
- **fuel 8**: Small loops — `fold_range 0 5` with nested `fold_range 0 5` (25 iterations)
- **fuel 26**: Larger loops — `fold_range 0 24` (24 iterations)
- **fuel > 30**: Almost certainly OOM. Use a different strategy.

### z3rlimit guidelines

- **100**: Most lemmas (the global default)
- **200**: Per-step equivalence lemmas with 25-element arrays
- **300**: `fold_range` bridge lemmas, chi reduction with high fuel
- **> 300**: Avoid. If you need more, the proof approach is wrong.

## Dealing with `fold_range`

hax extracts Rust `for` loops as `Rust_primitives.Hax.Folds.fold_range`.
This is the single biggest obstacle in these proofs.

### The Problem

F*'s normalizer **cannot reduce `fold_range`** automatically because the
recursive guard `v start < v end_` involves machine integer operations that
don't simplify during normalization.

### Strategy 1: High Fuel (preferred when it works)

For loops with concrete, small bounds (≤ 25 iterations), high fuel often works:

```fstar
(* fold_range 0 5 with nested fold_range 0 5 = 25 iterations *)
#push-options "--fuel 8 --z3rlimit 300"
let lemma_chi_fold_reduces (ks: impl_state) (k: usize)
  : Lemma (...) = ()
#pop-options

(* fold_range 0 24 = 24 iterations *)
#push-options "--fuel 26 --z3rlimit 300"
let lemma_keccakf1600_is_impl_rounds (ks: impl_state)
  : Lemma (...) = ()
#pop-options
```

This works because fuel lets the normalizer unfold `fold_range` step by step.
The fuel needed is roughly `iterations + 2`.

### Strategy 2: Recursive Bridge + Induction

When the loop body is too complex for Z3 to handle in one shot at high fuel
(e.g., each iteration calls multiple expensive functions), define a recursive
helper that mirrors the loop and prove equivalence by induction:

```fstar
(* Mirror the fold_range with explicit recursion *)
let rec impl_rounds (ks: impl_state) (r: usize)
  : Pure impl_state
    (requires r <=. mk_usize 24)
    (fun _ -> True)
    (decreases (v (mk_usize 24) - v r)) =
  if r =. mk_usize 24 then ks
  else impl_rounds (impl_one_round ks r) (r +! mk_usize 1)

(* Bridge: fold_range == recursive helper (needs high fuel) *)
#push-options "--fuel 26 --z3rlimit 300"
let lemma_bridge (ks: impl_state)
  : Lemma (keccakf1600 ks == impl_rounds ks (mk_usize 0)) = ()
#pop-options

(* Induction: step equivalence + recursion (needs fuel 1) *)
#push-options "--fuel 1 --z3rlimit 200"
let rec lemma_rounds_equiv (ks: impl_state) (state: spec_state) (r: usize)
  : Lemma
      (requires ks.f_st == state /\ r <=. mk_usize 24)
      (ensures (impl_rounds ks r).f_st == spec_rounds state r)
      (decreases (v (mk_usize 24) - v r))
  = if r =. mk_usize 24 then ()
    else begin
      lemma_one_round_equiv ks state r;
      lemma_rounds_equiv (impl_one_round ks r) (spec_one_round state r) (r +! mk_usize 1)
    end
#pop-options
```

### Strategy 3: Manual Peeling (fallback)

If high fuel causes OOM, prove a one-step unfolding lemma and apply it
repeatedly:

```fstar
#push-options "--fuel 1"
let lemma_fold_range_step (#acc_t: Type0) (start end_: usize) (inv: ...) (init: ...) (f: ...)
  : Lemma
      (requires v start < v end_)
      (ensures fold_range start end_ inv init f ==
               fold_range (start +! mk_usize 1) end_ inv (f init start) f)
  = ()
#pop-options
```

Then in the proof body, call `lemma_fold_range_step` once per iteration and
`assert` intermediate states.

## Array Equality: Element-wise Proofs

For proving two `t_Array T (mk_usize 25)` values are equal:

```fstar
(* 1. Prove per-element equality *)
let aux (idx: nat{idx < 25})
  : Lemma (Seq.index result idx == Seq.index expected idx) =
    (* ... per-element reasoning ... *)
in
(* 2. Lift to array equality *)
FStar.Classical.forall_intro aux;
Rust_primitives.Arrays.eq_intro result expected
```

This pattern is essential when the two sides compute differently (e.g., impl
uses `fold_range` while spec uses `createi`).

## Proving Constant Array Equalities

### Full-array `assert_norm` (preferred)

```fstar
#push-options "--z3rlimit 200"
let lemma_round_constants_equal (i: usize)
  : Lemma (requires i <. mk_usize 24)
          (ensures impl_constants.[i] == spec_constants.[i])
  = assert_norm (impl_constants == spec_constants)
#pop-options
```

This works when both arrays are defined with the same `array_of_list` values.
The normalizer reduces both sides and checks equality.

### Per-element `assert_norm` (when full-array fails)

```fstar
  = assert_norm (arr.[mk_usize 0] == mk_u32 0);
    assert_norm (arr.[mk_usize 1] == mk_u32 36);
    (* ... one per element ... *)
```

### The `--ext context_pruning` Problem

**Critical:** Per-element `assert_norm` on array lookups works in the F* LSP
(IDE mode) but **fails under `--ext context_pruning`** (used in batch/make).
Context pruning removes definitions the SMT solver "shouldn't need," but
`assert_norm` needs access to the array's definition to normalize it.

Workarounds:
1. Use full-array equality (`assert_norm (arr1 == arr2)`) which seems less
   affected
2. Document working LSP proofs with `admit();` before them so they're
   preserved but don't block batch verification:
   ```fstar
   = admit (); (* works in LSP, fails under --ext context_pruning *)
     assert_norm (arr.[mk_usize 0] == expected_0);
     ...
   ```

## LSP vs Batch Mode: Trust but Verify

**A proof that passes in the F* LSP/IDE may fail under `make`.**

Causes:
- `--ext context_pruning`: Prunes definitions needed by `assert_norm`
- `--query_stats` / hint files: Batch mode uses hints that can cache stale results
- Different Z3 random seeds or resource accounting

**Always verify with `make` before considering a proof complete.** Use LSP for
rapid iteration, but the final arbiter is the batch build.

To run batch verification:
```bash
cd proofs/fstar/extraction
rm -f /path/to/.fstar-cache/checked/Module.fst.checked
rm -f /path/to/.fstar-cache/hints/Module.fst.hints  # clear stale hints
make 2>&1 | tee res
```

**Never clear the entire `.fstar-cache`** — only remove the specific `.checked`
and `.hints` files for the module you changed.

## Using fstar-mcp for Incremental Verification

The fstar-mcp server allows incremental typechecking without re-verifying the
entire file:

```bash
# Start the server
FSTAR_MCP_PORT=3001 /path/to/fstar-mcp &

# Create a session (slow — loads all dependencies)
curl -s -X POST http://localhost:3001/ \
  -H "Content-Type: application/json" \
  -H "Accept: application/json" \
  -d '{"jsonrpc":"2.0","method":"tools/call","params":{"name":"create_session","arguments":{...}},"id":1}'

# Re-typecheck after edits (fast — only re-checks changed code)
# Use "kind": "verify-to-position" with "to_line" to verify only up to the lemma you're working on
curl -s -X POST http://localhost:3001/ \
  -H "Content-Type: application/json" \
  -H "Accept: application/json" \
  -d '{"jsonrpc":"2.0","method":"tools/call","params":{"name":"typecheck_buffer","arguments":{"session_id":"...","code":"...","kind":"verify-to-position","to_line":900}},"id":2}'
```

`verify-to-position` is essential for large files — it avoids re-verifying
already-proven lemmas above the one you're working on.

## `#push-options` / `#pop-options` Hygiene

Every `#push-options` **must** have a matching `#pop-options`. Leaked options
cause subtle failures:

- `--split_queries always` leaking into later lemmas causes "incomplete
  quantifiers" errors on proofs that previously worked
- High `--fuel` leaking causes timeouts or OOM on unrelated lemmas
- `--z3rlimit` leaking wastes solver time

Pattern:
```fstar
#push-options "--z3rlimit 200 --split_queries always"
let my_lemma (...) : Lemma (...) = ...
#pop-options
```

## Dealing with Transpositions

hax-extracted code often uses different argument ordering than the spec.
The Keccak impl uses `(i, j)` = `(row, col)` = `(y, x)`, while the spec uses
standard `(x, y)`. This means:

- `impl.get_ij(state, i, j)` = `spec.get(state, j, i)` — arguments transposed
- `impl.set_ij(state, i, j, v)` puts `v` at flat index `5*j + i`
- `spec.get(state, x, y)` reads flat index `5*x + y`

Document the transposition once and build on it throughout:
```fstar
let lemma_get_transposed (s: spec_state) (i j: usize)
  : Lemma (requires i <. mk_usize 5 /\ j <. mk_usize 5)
          (ensures impl_get_ij s i j == spec_get s j i)
  = ()
```

## Common Pitfalls

1. **`normalize_term` on large expressions**: Causes OOM (7+ GB). Never use
   `normalize_term` on a function that contains `fold_range`. Use fuel instead.

2. **Forgetting `#pop-options`**: Causes mysterious failures in later lemmas.
   Search for `#push-options` and count matching `#pop-options`.

3. **Hints caching stale results**: When a proof changes, delete both
   `.fst.checked` and `.fst.hints`. Stale hints cause make to report old
   rlimit values even after changing `#push-options`.

4. **Library-level admits**: Some properties (bitwise commutativity,
   `rotate_left(x, 0) == x`) are true but not provable from the abstract
   machine integer interface in `Rust_primitives.Integers`. These belong
   in the hax-lib library. Mark them clearly:
   ```fstar
   = admit () (* TODO: belongs in hax-lib / Rust_primitives.Integers *)
   ```

5. **`--split_queries always` for spec-side `createi`**: The spec uses
   `Hacspec_sha3.createi` (a wrapper for `Lib.Sequence.createi`) which
   produces quantified postconditions. Z3 handles these better with
   `--split_queries always`.

## Keccak-f Proof Summary

The complete proof in `Impl_Spec_Keccakf.fst` has 8 phases:

| Phase | What | Difficulty | Key technique |
|-------|------|-----------|--------------|
| 1. Primitives | `f_xor5`, `f_and_not_xor`, etc. | Trivial | `= ()` (definitional) |
| 2. Accessors | `get_ij` / `set_ij` transposition | Trivial | `= ()` (definitional) |
| 3. Constants | Round constants, rho offsets | Easy | `assert_norm` on full array |
| 4. Iota | XOR round constant at index 0 | Easy | Compose phases 1-3 |
| 5. Theta+Rho | Combined column parity + rotation | Hard | 25 per-element asserts, `--z3rlimit 200` |
| 6. Pi | Permutation of 25 positions | Medium | `--split_queries always`, `--z3rlimit 200` |
| 7. Chi | Nonlinear step with nested fold_range | Medium | `--fuel 8`, `logand_commutative`, `forall_intro + eq_intro` |
| 8. Full keccak-f | 24-round composition | Medium | Recursive bridge (`--fuel 26`), induction (`--fuel 1`) |

Main theorem: `lemma_keccakf1600_equiv` — chains all phases to show
`keccakf1600(ks).f_st == keccak_f(state)`.
