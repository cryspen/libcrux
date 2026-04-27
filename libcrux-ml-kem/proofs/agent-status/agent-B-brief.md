# Agent B — Phase 7c: Serialize re-root to `Hacspec_ml_kem.Serialize.*`

Brief for the agent originally spawned on branch `agent/phase-7c-serialize`.
Eager-commit log lives at `proofs/agent-status/agent-B.md` on that branch.

## Mission

Add `Hacspec_ml_kem.Serialize.*` post-condition citations **alongside** the
existing `Spec.MLKEM.*` citations in `libcrux-ml-kem/src/serialize.rs` (8
functions cite Spec.MLKEM; 6 trivial-post helpers also need the canonical
spec attached).  This is **post-only and additive** — old `Spec.MLKEM.*`
citations stay (they get removed in a later Phase 7k once Ind_cpa/Ind_cca
migrate downstream).

## Required reading (in order)

1. `libcrux-ml-kem/MLKEM_STATUS.md` — top-level state, esp. Phase 7c table
2. `libcrux-ml-kem/proofs/session-handoff.md`
3. `libcrux-ml-kem/proofs/proof-style-guide.md` — esp. §3.7 post-only invariant
4. `specs/ml-kem/proofs/fstar/extraction/Hacspec_ml_kem.Serialize.fst` — the canonical spec module

## Operating constraints

- **Wall clock**: 90 min.
- **Per-function budget**: ~10 min for additive citation + ~15 min for the
  bridge lemma (if equivalence is non-trivial).  If a bridge proof doesn't
  go through in 15 min, **admit the new conjunct with an English comment**
  describing what was tried, hypothesis why it should hold, and a
  `Hacspec_ml_kem.Serialize.<fn>` identifier the user can search for.  The
  `Spec.MLKEM.*` citation stays in place, so the function's contract is
  not weakened.  Commit and move on.
- **Memory**: `ulimit -v 8388608` before any shell that spawns F\*.  Pass
  `--z3cliopt smt.memory_max_size=8000` in F\* options on any new fstar
  invocation block you write.
- **F\* concurrency**: at most 1 F\* process at a time (you'll mostly be
  running `make Libcrux_ml_kem.Serialize.fst.checked`, which is fine).
- **F\* rlimit**: never exceed 800.  If a query needs more, that's a signal
  to admit-the-conjunct.

## Code change policy

- **Rust function bodies**: do NOT touch.
- **`#[hax_lib::ensures(...)]` blocks**: editable — add new conjunctive
  citations.  Must not weaken any existing condition.
- **`#[hax_lib::requires(...)]` blocks**: do NOT touch.
- **Hand-written F\* helper / bridge lemmas**: add freely in
  `proofs/fstar/spec/` or as inline `fstar::before` blocks; whichever
  matches the existing convention for the file you're editing.
- Spec.MLKEM.* citations: **leave in place**.  Removal is Phase 7k.

## Tooling decision

- **Default**: plain `make Libcrux_ml_kem.Serialize.fst.checked` from
  `libcrux-ml-kem/proofs/fstar/extraction/`.  Use this for every Rust-side
  edit, since `python3 hax.py extract` regenerates the file anyway.
- **fstar-mcp**: use ONLY if you find yourself iterating ≥5 times on the
  same hand-written helper file content (e.g., a bridge-lemma file you're
  refining).  If you do start fstar-mcp, use port **3003**, prefix shell
  with `ulimit -v 8388608`, tear down at end of run.

## Targets — citations to add (8 functions in src/serialize.rs)

Mapping from current `Spec.MLKEM.*` citations to `Hacspec_ml_kem.Serialize.*`:

| Line | Current Spec.MLKEM citation | Add Hacspec_ml_kem.Serialize citation |
|---|---|---|
| 24 | `compress_then_encode_message` | `compress_then_serialize_message` |
| 63 | `decode_then_decompress_message` | `deserialize_then_decompress_message` |
| 89 | `byte_encode 12` | `serialize_uncompressed_ring_element` (or `vector_encode_12_` if shape matches) |
| 119 | `byte_decode 12` | `deserialize_to_uncompressed_ring_element` |
| 193 | `vector_decode_12` | `vector_decode_12_` |
| 264 | `compress_then_byte_encode (v COMPRESSION_FACTOR)` | check `compress_then_serialize_u/v` |
| 351 | `compress_then_encode_v` | `compress_then_serialize_v` |
| 435 | `byte_decode_then_decompress (v COMPRESSION_FACTOR)` | `deserialize_then_decompress_u/v` |
| 514 | `decode_then_decompress_v` | `deserialize_then_decompress_v` |

(The line numbers may shift as you edit; use `grep -n "Spec.MLKEM\." src/serialize.rs` to re-find them.)

For each, the new conjunct shape is:
```
result == Hacspec_ml_kem.Serialize.<fn> ...args...
```
or equivalent — check what arg shape the canonical `Hacspec_ml_kem.Serialize`
function takes.

If the equivalence between the existing `Spec.MLKEM.*` citation and the
new `Hacspec_ml_kem.Serialize.*` citation needs a bridge lemma, add it to
`specs/ml-kem/proofs/fstar/spec/` (or `proofs/fstar/spec/` — match
existing convention).  If the bridge is hard (>15 min), admit it with
comment and move on.

## Trivial-post helpers (6)

The 6 trivial-post functions in `src/serialize.rs` (no `Spec.MLKEM`
citation today) should also gain a `Hacspec_ml_kem.Serialize.*` post if
one exists for them.  Identify them via:
```
grep -n "fn " src/serialize.rs | grep -v "^//" | wc -l
```
should be 14 total (8 cited + 6 trivial).  Skip any whose canonical spec
counterpart isn't obvious — flag in the log, don't guess.

## Eager-commit logging — CRITICAL

Maintain `libcrux-ml-kem/proofs/agent-status/agent-B.md` on your branch
`agent/phase-7c-serialize`.  After every meaningful step (citation
added + verifies, or admitted-with-comment, or scaffold change), append a
timestamped entry to the log, `git add`, `git commit -m "agent-B: ..."`.

Initial log skeleton:

```markdown
# Agent B — Phase 7c Serialize re-root

**Branch**: agent/phase-7c-serialize
**Brief**: see proofs/agent-status/agent-B-brief.md on trait-opacify

## Targets (8 cited + 6 trivial)
- [ ] compress_then_encode_message  → compress_then_serialize_message
- [ ] decode_then_decompress_message  → deserialize_then_decompress_message
- [ ] byte_encode 12  → serialize_uncompressed_ring_element
- [ ] byte_decode 12  → deserialize_to_uncompressed_ring_element
- [ ] vector_decode_12  → vector_decode_12_
- [ ] compress_then_byte_encode  → compress_then_serialize_u
- [ ] compress_then_encode_v  → compress_then_serialize_v
- [ ] byte_decode_then_decompress  → deserialize_then_decompress_u
- [ ] decode_then_decompress_v  → deserialize_then_decompress_v
- [ ] (6 trivial-post helpers — identify and list)

## Progress (append-only, newest at bottom)

### YYYY-MM-DD HH:MM:SS UTC — Started
...
```

Use `[x]` (citation added + verifies), `[~]` (admitted with comment),
`[!]` (blocker), `[?]` (no obvious spec counterpart, skipped).

## Stop conditions

- 90 min wall clock exceeded
- Z3 OOM kill on the same target twice
- F\* segfault on the same target twice
- All 14 functions handled (cited / admitted-with-comment / skipped)

## Final deliverable

1. Final status commit on `agent-B.md` summarizing outcome
2. `make Libcrux_ml_kem.Serialize.fst.checked` final regression run, time recorded
3. Concise summary back to parent: count cited / admitted-with-comment /
   skipped, last commit hash, verification state of `Serialize.fst`,
   any escalations needed

## Hard rules

- DO NOT push to origin.
- DO NOT merge to `trait-opacify`.
- DO NOT touch other agents' branches or files outside the scope above.
- DO NOT remove `Spec.MLKEM.*` citations (Phase 7k handles that).
- DO NOT exceed F\* rlimit 800.
