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

## Sponge-Layer Proof Patterns

Lessons learned extending the equivalence upward from `keccak_f` to the
full sponge (`Impl_Spec_Sponge.fst`, phases 9–17, including the
Phase 13 store-block bridge and the Phase 16 `keccak1` bridge). The
sponge layer introduced qualitatively new obstacles beyond Keccak-f
because loops are unbounded (not 24 rounds but "ceil(OUTPUT_LEN/rate)"
iterations), the fold-range bodies are much heavier, and the impl and
spec originally structured their squeeze phases differently.

### Ranking of pain points (most to least blocking)

| Rank | Source of pain | Workaround |
|------|----------------|-----------|
| 1 | `fold_range` closure equality cannot be proved by SMT | Axiomatize a small named-function bridge (e.g. `lemma_*_decomposes`, `lemma_*_is_loop`) |
| 2 | Slice-index subtype obligations inside untyped closures | Move body into a typed `Pure` helper function; axiom references helper by name |
| 3 | `usize` arithmetic via `v`-abstraction + hax's refinement-heavy generated code | Per-lemma `assert (v ... == ...)` bookkeeping; helper lemmas `lemma_div_mul_mod`, `lemma_mul_succ_le` |
| 4 | Typeclass/trait dispatch (e.g. `Libcrux_sha3.Traits.f_squeeze`) | Let SMT unfold the resolution via `lemma_store_block_equiv` which matches on the portable resolution |
| 5 | Slice (`t_Slice u8`) vs sized-array (`t_Array u8 N`) at proof boundary | Coerce spec's array to a slice at the top-level `ensures`; keep helpers slice-typed |
| 6 | hax extraction drift between hax versions | Keep proofs referencing named top-level functions; treat rewrites of auxiliaries (e.g. byte-copy style) as transparent |

### Pattern 1: the "typed Pure helper + small axiom" idiom

When you need to prove that a `fold_range` in hax-extracted code
equals a custom recursive function, DO NOT try to unfold the
closure. Instead:

1. Define a typed recursive mirror with an explicit `Pure` signature
   whose precondition carries all length/bound information the
   closure body would otherwise have to derive from a trivial
   invariant.
2. State an `assume val` equating the original `fold_range` to
   `mirror init start end_` — this is the only admitted content.
3. Use standard induction on the mirror to prove the real property.

Concrete example (Phase 13,
`Impl_Spec_Sponge.fst::lemma_store_block_bridge`):

```fstar
(* 1. typed recursive mirror — Pure precondition lets body typecheck *)
let rec store_block_impl_loop
    (s: spec_state) (out: t_Slice u8) (start: usize)
    (i octets: usize)
  : Pure (t_Slice u8)
    (requires v start + 8 * v octets <= Seq.length out /\ v octets <= 25 /\ v i <= v octets)
    (ensures fun out' -> Seq.length out' == Seq.length out)
    (decreases (v octets - v i))
  = if i =. octets then out
    else
      let out' = write_one_lane s out (start +! mk_usize 8 *! i) i in
      store_block_impl_loop s out' start (i +! mk_usize 1) octets

(* 2. one small axiom — the fold_range closure cannot be equated by SMT *)
assume val lemma_store_block_decomposes
    (rate: usize) (s: spec_state) (out: t_Slice u8) (start len: usize)
  : Lemma (requires ...)
          (ensures store_block rate s out start len ==
                   <composition of loop + remainder helpers>)

(* 3. real proof by induction on the mirror *)
let rec lemma_store_loop_equiv (s: spec_state) (out: t_Slice u8)
                               (start i octets: usize)
  : Lemma (requires ...)
          (ensures store_block_impl_loop s out start i octets ==
                   squeeze_state_spec_loop s out start i octets)
          (decreases (v octets - v i))
  = if i =. octets then ()
    else begin
      lemma_one_lane_equiv s out start i;
      lemma_store_loop_equiv s (write_one_lane s out ...) start (i +! 1) octets
    end
```

The net effect: Phase 13's monolithic admit `lemma_store_block_bridge`
became a real proof resting on **four** small fold-range axioms, each
one-line and obvious-by-inspection.

### Pattern 2: align the spec to the impl BEFORE proving

The single largest time saver in Phase 16 was realigning the Rust
spec's squeeze loop from a "uniform `fold_range 0 ceil(OUTPUT_LEN/rate)`
with inline `if round > 0 then keccak_f` and `min(remaining, rate)`"
into the impl's "split" form (`if output_blocks == 0 then single else
first; fold_range 1 output_blocks (keccakf+squeeze); optional
remainder`). See `specs/sha3/src/sponge.rs::keccak`.

After the realignment:

- ceiling-vs-floor index-alignment lemma disappears (both sides use
  `OUTPUT_LEN / rate` and `OUTPUT_LEN % rate` directly)
- per-iteration bodies become α-identical modulo the two primitive
  bridges (`keccakf1600_equiv`, `store_block_equiv`)
- the zero-block and first-block special cases become one-line
  `store_block_equiv` applications

**Rule of thumb**: if the spec and impl have the same algorithm but
different loop factorings, it is *cheaper* to rewrite the Rust spec
(which is usually small) than to introduce an index-alignment lemma
on the F* side. Re-extract (`./hax.sh extract`) + re-prove
(`./hax.sh prove`) + cross-spec tests (`cargo test --test cross_spec`)
validate the rewrite end-to-end before touching the F* proof.

### Pattern 3: two-level cross-spec testing

When rewriting a spec to align with an impl, add cross-spec tests
that specifically exercise *each structural branch* you introduced —
not just the end-to-end behavior. Example from Phase A.5:

```rust
// tests/cross_spec.rs
fn squeeze_structure_lengths(rate: usize) -> Vec<(usize, &'static str)> {
    vec![
        // output_blocks == 0 (len < rate)
        (1, "zero-blocks: len=1"),
        (rate - 1, "zero-blocks: len=rate-1"),
        // output_blocks >= 1, rem == 0
        (rate, "exact: len=rate"),
        (2 * rate, "exact: len=2*rate"),
        // output_blocks >= 1, rem != 0
        (rate + 1, "rem: len=rate+1"),
        (3 * rate + (rate - 1), "rem: len=3*rate+rate-1"),
    ]
}
```

These tests catch regressions in the specific case split the F* proof
is going to rely on, *before* you invest proof effort.

### Pattern 4: `usize` arithmetic bookkeeping

`v (a +! b) == v a + v b` is conditional on non-overflow; the solver
discharges the bound from context but only if the bound is visible.
Common motifs and the supporting lemmas:

| Goal | Lemma / tactic |
|------|---------------|
| `v (len /! 8) * 8 + v (len %! 8) == v len` | `Libcrux_sha3.Proof_utils.Lemmas.lemma_div_mul_mod` |
| `v (i *! rate) + v rate <= v (n *! rate)` when `i < n` | `Libcrux_sha3.Proof_utils.Lemmas.lemma_mul_succ_le` |
| `v (a +! b) = v a + v b` under `a + b <= max_usize` | often free; otherwise `assert (v a + v b <= ...)` first |
| `v start + v len <= Seq.length out` inside fold closure | lift into Pure helper's precondition (Pattern 1) |

Accumulated bookkeeping is never individually hard but drains the
majority of proof-body lines. Budget for it.

### Pattern 5: `valid_rate` as the one true rate predicate

Every sponge-layer lemma that takes a `rate: usize` should require
`Libcrux_sha3.Proof_utils.valid_rate rate` (i.e. `rate > 0 && rate <= 200
&& rate % 8 == 0`). This single predicate lets the solver reason about
the rate without ad-hoc per-call asserts and is the invariant that
both hax refinements and the hacspec spec carry.

### Pattern 6: hax extraction drift

`./hax.sh extract` may change more than you asked for. In Phase A
the regenerated `Hacspec_sha3.Sponge.fst` also hoisted previously-inlined
functions to top-level `let`s and rewrote per-byte fold copies into
`copy_from_slice + update_at_range` calls. The sponge-layer proofs
survived because they referenced top-level spec functions by name and
treated `keccak` as a black box (guarded by `lemma_keccak1_bridge`).

Mitigation: write proofs against **named top-level functions**
whenever possible, and avoid matching on the internal style of spec
bodies. If you must match internal style (e.g., for a `fold_range`
bridge), expect to rewrite when hax is updated.

### Pattern 7: `assert ... by tadmit ()` as a local escape hatch

For pre-existing subtype-propagation hurdles that block a lemma
unrelated to your current change, a per-assertion
`assert (P) by (FStar.Tactics.tadmit ())` is acceptable if:

- The surrounding lemma is otherwise proved.
- A comment documents which sub-obligation is being admitted and why.
- It is NOT used to avoid proving the main claim (only stubborn
  refinement-level sub-obligations inside otherwise-proved lemmas).

This appears in `Impl_Spec_Sponge.fst::lemma_load_last_equiv` around
lines 1105–1106 for two abstract slice-expression equalities the
solver cannot connect.

### Summary: when to axiomatize, when to prove

**Axiomatize** (`assume val`) — only these three patterns:

1. `fold_range` in hax-extracted code equals a custom recursive
   mirror with the same body (unprovable for the reason in "Strategy
   1/2/3" above).
2. Library-level properties of machine integers that belong in
   `Rust_primitives.Integers` (see Common Pitfalls, item 4).
3. Cross-module primitive equivalences defined in a neighbor file
   and not yet lifted here (e.g. `lemma_keccakf1600_equiv` was
   assumed in `Impl_Spec_Sponge.fst` before Keccak-f was proved).

**Prove** — everything else. Specifically:

- Per-step bridges (one `fold_range` iteration).
- Inductive equivalences on custom mirrors.
- Composition of already-proved lemmas.
- Top-level theorems that thread the above.

A sponge-layer proof with more than ~5 `assume val`s above your own
code is a signal to reach for the typed-helper pattern and decompose.

## Learnings from the Generic Keccak-f Proof

The generic proof (`Impl_Spec_Keccakf.Generic.fst`) proves keccak_f
equivalence for *any* `KeccakItem` implementation (not just portable
`u64`), using a `lane_correctness` typeclass that abstracts per-lane
extraction. This section records patterns and anti-patterns discovered
while eliminating `admit()` calls.

### Patterns (what works)

#### 1. Named body extraction eliminates closure equality

Factor `fold_range` lambda bodies into named top-level functions.
When both spec and impl reference the same named function, the
closure-equality problem disappears entirely.

```fstar
(* Named body — same definition used in fold_range on both sides *)
let impl_round_body v_N #v_T {|inst|} (self: t_KeccakState v_N v_T) (i: usize{v i < 24})
  : t_KeccakState v_N v_T =
  let ks', d = impl_2__theta v_N self in ...

let impl_keccakf1600 v_N #v_T {|inst|} self =
  fold_range 0 24 (fun _ _ -> true) self
    (fun self i -> impl_round_body v_N self i)
```

This pattern requires a **uniform change to extracted code**: both
spec and impl must factor their `fold_range` bodies into named
functions. The extraction itself should produce these names.

#### 2. Lockstep fold induction (fuel 1)

When both sides have `fold_range` with the same range and named
bodies, prove equivalence by peeling one step from each:

```fstar
#push-options "--fuel 1 --z3rlimit 200"
let rec lemma_keccakf_commutes v_N {|inst|} lc ks spec i l
  : Lemma (requires ...)
      (ensures extract_lane (fold_range i 24 inv ks f_impl) l ==
               fold_range i 24 inv_s spec f_spec)
      (decreases (24 - v i))
  = if i = 24 then ()
    else begin
      lemma_fold_range_step i 24 inv ks f_impl;
      lemma_fold_range_step i 24 inv_s spec f_spec;
      lemma_one_round_commutes v_N lc ks i l;
      lemma_keccakf_commutes v_N lc
        (impl_round_body v_N ks i) (spec_round_body spec i) (i+1) l
    end
#pop-options
```

Cost: fuel 1, rlimit 200, ~1.2s total. Compared to fuel 26 (which
OOMs for generic types), this is essentially free.

#### 3. Chi fold unrolling with fuel 6

For small concrete folds (`fold_range 0 5`), fuel 6 lets Z3 unfold
the loop step by step:

```fstar
#push-options "--fuel 6 --z3rlimit 400"
let lemma_chi_named_unfolds v_N #v_T {|inst|} ks
  : Lemma (chi_named v_N ks == chi_unrolled v_N ks) = ()
#pop-options
```

Name both the inner body (`chi_inner_body`) and outer body
(`chi_outer_body`), then unroll both loops independently.

#### 4. Explicit `Seq.upd`/`Seq.index` guidance for per-element chi

Z3 cannot trace through 5 layers of
`chi_inner_body → impl_2__set → set_ij → update_at_usize → Seq.upd`
automatically. Prove a single-step lemma stating `chi_inner_body`
produces `Seq.upd`, then call it explicitly for each step:

```fstar
(* Single-step lemma: chi_inner_body is Seq.upd *)
let lemma_chi_inner_body_set (old self: impl_state) (i j: usize)
  : Lemma (chi_inner_body 1 old self i j).f_st ==
      Seq.upd self.f_st (v (5*j+i)) (f_and_not_xor ...))
  = ()

(* Per-element: call the single-step lemma for each of 5 steps *)
let lemma_chi_row_element_0_0 (old self: impl_state)
  : Lemma (...) =
  lemma_chi_inner_body_set old self 0 0;
  lemma_chi_inner_body_set old s0 0 1;
  lemma_chi_inner_body_set old s1 0 2;
  lemma_chi_inner_body_set old s2 0 3;
  lemma_chi_inner_body_set old s3 0 4
```

Z3 then uses `Seq.index (Seq.upd s k v) j` axioms to chain:
updates at positions 5,10,15,20 don't affect position 0.

#### 5. Raw `Seq.index` in postconditions, not accessor notation

Use `Seq.index s.f_st N` with concrete numeric positions, not
`s.[mk_usize i, mk_usize j]`:

```fstar
(* GOOD: concrete positions via Seq.index *)
Seq.index result.f_st 0 ==
  f_and_not_xor (Seq.index self.f_st 0) (Seq.index old.f_st 10) (Seq.index old.f_st 5)

(* BAD: accessor notation introduces get_ij / set_ij mismatch *)
result.[mk_usize 0, mk_usize 0] == f_and_not_xor ...
```

The `.[i,j]` notation goes through `get_ij → Seq.index ... (5*j+i)`
while `lemma_chi_inner_body_set` states results via `Seq.upd` at
`(5*j+i)`. Z3 can't connect these different accessor paths.

#### 6. High fuel for spec-side fold (when bodies are cheap)

```fstar
#push-options "--fuel 25 --z3rlimit 200"
let lemma_keccak_f_is_rounds (state: spec_state)
  : Lemma (keccak_f state == spec_rounds state 0) = ()
#pop-options
```

Works because the spec body (`iota(chi(pi(rho(theta(state)))))`) is
lightweight for Z3. The impl body (multiple typeclass dispatches,
tuple returns) is NOT, so fuel 26 fails for the impl side.

#### 7. Chi proof structure: unrolling + per-element + forall_intro + eq_intro

The complete chi proof chains four layers:

1. `lemma_chi_outer_unfolds`: fold_range → unrolled (fuel 6)
2. `lemma_chi_fold_reduces`: unrolled → per-element value (each index)
3. `logand_commutative`: bridge AND argument order (impl ↔ spec)
4. `forall_intro + eq_intro`: lift per-element to array equality

### Anti-patterns (what fails)

#### 1. `fold_range_ext_trivial_inv` for bridging extracted lambdas

The extracted code uses `(fun _ _ -> true)` (returns `bool`) while
`fold_range_ext_trivial_inv` uses `trivial_inv` (returns `Type0`).
These create different `fold_range` calls with incompatible types.
**Tested across 6+ variations (Test_Fold_Impl4 through Impl9), all
fail at the final postcondition.**

#### 2. Narrow `assume val` for closure equality

```fstar
(* Mechanically correct but unverifiable by inspection *)
assume val lemma_keccakf1600_decomposes (ks: impl_state)
  : Lemma (impl_2__keccakf1600 1 ks == fold_range 0 24 ... ks keccakf_body)
```

This works but is **unintuitive** — the axiom asserts syntactic
equality of closures, which isn't a mathematical property anyone can
inspect for correctness. Prefer the named-body extraction approach
(Pattern 1) which eliminates the need entirely.

#### 3. `.[mk_usize k]` accessor in per-element lemma postconditions

```fstar
(* FAILS: accessor goes through get_ij, creates different SMT term *)
(chi_row_unrolled 1 old self 0).[mk_usize 0, mk_usize 0] ==
  f_and_not_xor (old.[mk_usize 0, mk_usize 0]) ...
```

Even when the values are definitionally equal, Z3 can't connect
`get_ij` terms with `Seq.upd`/`Seq.index` terms because they
produce different SMT encodings.

#### 4. Expecting Z3 to trace deep abstraction chains at low fuel

`chi_inner_body → impl_2__set → set_ij → update_at_usize → Seq.upd`
is 4 levels. At fuel 1, Z3 unfolds one level. At fuel 0, none.
Even `= ()` fails because Z3 can't reach the `Seq.upd` at the
bottom. **Always provide explicit intermediate lemmas** that
collapse multi-layer abstractions to `Seq.upd`/`Seq.index`.

#### 5. `normalize_term` or `assert_norm` on `fold_range`

The recursive guard `v start < v end_` involves `v` (machine-int
to nat) which doesn't simplify during normalization. `assert_norm`
on any expression containing `fold_range` will fail. Use fuel-based
unfolding instead.

#### 6. Per-element chi with `= ()` (no proof guidance)

Even with fuel 6 + rlimit 400, Z3 cannot simultaneously:
- unfold `fold_range 0..5` (inner loop)
- trace through 5 `chi_inner_body` calls
- resolve `Seq.upd`/`Seq.index` at a specific position

**Each layer requires separate guidance.** Unroll the fold (fuel 6),
state per-step results (explicit lemma calls), let Z3 chain
`Seq.index`/`Seq.upd` (automatic at fuel 1).

#### 7. Wrong accumulator in postconditions (`old` vs `self`)

Chi's `chi_inner_body` uses THREE state references:
- `self.[i,j]` — from the **accumulator** (mutating state)
- `old.[i,(j+2)%5]` — from the **original** (frozen snapshot)
- `old.[i,(j+1)%5]` — from the **original** (frozen snapshot)

A common mistake: writing the postcondition as
`f_and_not_xor(old[0], old[10], old[5])` when the first argument
should be `self[0]`. In the full chi, `old == self` initially,
masking the error. But for intermediate row lemmas where
`old ≠ self`, the postcondition becomes unprovable.

#### 8. Generic (parametric) per-element proofs without lane extraction lemmas

The portable proof works directly on `u64` values. The generic
proof must additionally invoke `lc_and_not_xor` (to convert
typeclass `f_and_not_xor` to `u64` operations) and
`logand_commutative` (to bridge `a &. ~b` ↔ `~b &. a`). These
extra layers multiply the proof obligations: 25 elements ×
(`lc_and_not_xor` + `logand_commutative`) = 50 extra lemma calls.
