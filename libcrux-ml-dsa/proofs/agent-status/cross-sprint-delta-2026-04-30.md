# Cross-sprint delta — 2026-04-30 (from ml-dsa-proofs)

Generalizable learnings from a single ML-DSA session that should
flow to the ML-KEM and SHA-3 sprints. Append the relevant bits to
your sprint's `sprint-learnings.md` (or equivalent). Source commits
on `ml-dsa-proofs` branch:

- `5d32e16df` — Encoding.Verification_key.generate_serialized closure
- `74922609a` — Makefile flip + Constants_xx promotion
- `9da124ba5` — Shuffle_table revert with diagnosis
- `2420f7555` — agent-prompt freshness fix-up

---

## AP-4 (universal): Don't fight `bits USIZE` opacity

The hax proof-libs `.fsti` keeps
`Rust_primitives.Integers.bits Rust_primitives.Integers.USIZE`
opaque. Z3 cannot derive `v x < bits USIZE` from `v x < 64` under
`fuel 0`, and **`assert_norm` does not unfold it either** (verified
by attempt — the assert_norm itself fails).

Affects any function that does `1 << shift_amount` on a usize. The
shift requires `shift_amount: { v < bits USIZE }` and the
refinement won't discharge.

**Mitigation options**:
- Bound the shift amount tighter (`< 8`) so the obligation falls
  into a different proof path.
- Leave the module admitted rather than burn time on a proof-libs
  detour.
- DO NOT add `assert_norm (bits USIZE == 64)` — it doesn't help.

**First observed**: ml-dsa Shuffle_table promotion attempt
(`9da124ba5`).

---

## AP-5 (universal): `assert_norm` for arithmetic constant chains with subtraction

When a constant extracts to F\* via a chain that includes a
subtraction step, plain `assert (v $C == K)` fails under `fuel 0`
even though Z3 can compute the value. Use `assert_norm`.

**Pattern**:
- `RING_ELEMENT_OF_T0S_SIZE = 13 * 256 / 8` → plain `assert` works.
- `BITS_IN_UPPER_PART_OF_T = FIELD_MODULUS_MINUS_ONE_BIT_LENGTH - BITS_IN_LOWER_PART_OF_T`
  (extra unfold step) → plain `assert` fails, `assert_norm` works.

ML-KEM and SHA-3 likely have analogous constant chains
(`COEFFICIENTS_*`, sponge state sizes derived by subtraction, etc.).
When you hit a "Z3 can't prove `v $CONST == K`" failure on a known
constant, swap to `assert_norm` first.

**First observed**: ml-dsa
`Encoding.Verification_key.generate_serialized` closure
(`5d32e16df`).

---

## Makefile structure: ADMIT-allowlist > VERIFIED-denylist

ML-DSA flipped from
```makefile
VERIFIED_MODULES = (large explicit list)
ADMIT_MODULES = $(filter-out VERIFIED_OR_SLOW, $(wildcard *.fst))
```
to ml-kem-style
```makefile
ADMIT_MODULES = (small explicit list, grouped + commented)
# ROOTS defaults to wildcard, generic Makefile splits CHECK vs ADMIT
```

**Why**: every newly-extracted file now defaults to **verified**
rather than silently admitted. To admit a module, you must add an
explicit Makefile entry with a one-line reason. Forces visibility.

**SHA-3 sprint**: check whether your Makefile is still on the
denylist pattern. If so, the flip is a 1-hour mechanical change:
list current admits, replace `VERIFIED_MODULES` block with
`ADMIT_MODULES`, drop the `filter-out` line, run prove. See
ML-DSA's `74922609a` for the diff.

**ML-KEM sprint**: already on allowlist style — no action.

---

## Agent-prompt staleness — periodic audit pattern

ML-DSA's agent prompt at `proofs/agent-prompt-ml-dsa.md` had a
material factual error: it directed agents to "design
Hacspec_ml_dsa.Ntt from scratch" when in fact
`specs/ml-dsa/proofs/fstar/extraction/Hacspec_ml_dsa.*` already had
4318 lines of spec including `Hacspec_ml_dsa.Ml_dsa.{keygen,sign,
verify}_internal`. Likely cost prior agents real wasted cycles.

**Recommended audit pass for any sprint's agent prompt** (~30 min):
1. Grep the prompt for "design", "create", "scaffold" + spec-module
   names. For each hit, check whether the spec already exists.
2. Add an "Existing spec inventory" section near the top listing
   what's there, with file paths + line counts.
3. Add a "Recently closed (do not redo)" section listing recent
   commits and what they accomplished.
4. Replace any inline "rebuild this thing from scratch" guidance
   with "grep first, design only if missing".
5. Tip SHA in prompts goes stale fast — drop it, point at a
   handoff doc that's actually maintained.

**ML-DSA**: done in `2420f7555`.
**ML-KEM and SHA-3**: high-leverage to do once; same pattern.

---

## Encoding-wrapper closure recipe

For wrapper functions of the shape:
```rust
pub(crate) fn serialize<...>(input: &[T], ..., output: &mut [u8]) {
    output[0..PREFIX_SIZE].copy_from_slice(prefix);
    for i in 0..input.len() {
        let offset = PREFIX_SIZE + i * CHUNK_SIZE;
        callee::serialize(&input[i], &mut output[offset..offset + CHUNK_SIZE]);
    }
}
```
the closure pattern that worked for ml-dsa
`Verification_key.generate_serialized`:

1. Hoist `input.len()` to a nameable binding `let input_len = input.len();`
   so it can appear in `loop_invariant!`.
2. `loop_invariant!` carries: `v i <= input_len`, `input_len <= MAX`,
   length identity on `output`, and the per-element forall from the
   function's `requires`.
3. `assert_norm (v $CHUNK_SIZE == <literal>)` if the constant
   extracts via a subtraction chain (see AP-5).
4. Offset-arithmetic asserts:
   ```
   assert (v i < v $input_len);
   assert (v i * <chunk> <= (MAX - 1) * <chunk>);
   assert ((v i + 1) * <chunk> <= v $input_len * <chunk>)
   ```
5. `--z3rlimit 400 --split_queries always --fuel 0 --ifuel 1`.

ML-KEM analogs likely include `compress_then_serialize_*`,
`serialize_secret_key`. Same recipe should transfer; main variable
is whether the per-element forall is opaque-predicate-style
(easier) or expanded triple-forall (harder, more rlimit).

**First observed**: ml-dsa `5d32e16df`.

---

## Optional: shared anti-pattern catalog

Right now AP-N text is inlined in each per-sprint agent prompt.
Drift is real — AP-2 text in three prompts means three places to
update when it evolves. Consider a top-level
`/proofs/anti-patterns.md` (or `~/libcrux-main/.../anti-patterns.md`)
that's the single source, and per-sprint prompts only `cite` AP-N
by number + first-observed-in commit. Not strictly necessary; minor
maintenance win.
