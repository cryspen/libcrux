# Agent B' — Phase 7c follow-up: body proofs for 4 simple functions

Continuation of agent B's run on branch `agent/phase-7c-serialize`
(tip `06d5e65ff`).  Agent B landed all 9 brief-listed Hacspec citations
via admitted SMTPat axioms in `Libcrux_ml_kem.Serialize.HacspecBridge.fst`.

**User feedback**: bridge admits are throwaway scaffolding (the bridge
gets discarded in Phase 7l when `Spec.MLKEM` is deleted).  Per user
choice of option (b), do real body-proof work for the 4 SIMPLE
functions; leave compress-family bridges in place as scaffolding for
Phase 7a/7k.

## Mission

Replace 4 bridge admits with real body proofs in `Libcrux_ml_kem.Serialize.fst`,
each chaining the trait's `serialize_post_N` / `deserialize_post_N`
(bit-vector equality) up to `Hacspec_ml_kem.Serialize.byte_encode` /
`byte_decode` directly.  After this lands, the corresponding axioms in
`HacspecBridge.fst` get DELETED (not just unused — actually removed).

## Targets (in this order — drop one if it doesn't go in budget)

1. **`serialize_uncompressed_ring_element`** — `byte_encode 12`.  Loop
   over 16 chunks of 16 i16 coefficients each; trait `serialize_12`
   gives 24 bytes per chunk satisfying `serialize_post_N #16 12`.
   Hacspec spec: `bits_to_bytes ∘ bitvector_from_bounded_ints` over
   `t_FieldElement` (u16-wrapper).
2. **`deserialize_to_uncompressed_ring_element`** — `byte_decode 12`.
   Mirror image of (1).  Trait `deserialize_12` gives 16 i16 coefficients
   from 24 bytes.
3. **`compress_then_serialize_message`** — `byte_encode 1` ∘ `compress_d 1`.
   D=1 is special — per-element `compress_message_coefficient` produces
   {0, 1}.  Per-element commute lemma A5
   (`lemma_compress_message_coefficient_fe_commute`) is **already proven**
   in `Hacspec_ml_kem.Commute.Chunk.fst`.  Use it.
4. **`deserialize_then_decompress_message`** — `decompress_d 1` ∘
   `byte_decode 1`.  A6
   (`lemma_decompress_1_fe_commute`) is already proven.  Use it.

## Functions that REMAIN as bridges (do NOT touch)

These five admits in `HacspecBridge.fst` stay (gated on Phase 7a's
Tier-1 chunk-commute lemmas for compress<D> that haven't been written):
- `compress_then_serialize_ring_element_u_post`
- `compress_then_serialize_ring_element_v_post`
- `deserialize_then_decompress_ring_element_u_post`
- `deserialize_then_decompress_ring_element_v_post`
- `compress_then_serialize_post` (the public API wrapper if any)

## Required reading (in order)

1. **THIS BRIEF** + agent B's brief (`agent-B-brief.md`) + B's log
   (`agent-B.md` on the branch)
2. `libcrux-ml-kem/proofs/fstar/spec/Libcrux_ml_kem.Serialize.HacspecBridge.fst`
   on the branch — current state of bridges
3. `Libcrux_ml_kem.Serialize.fst` (extracted on the branch) — current
   body proofs for impl→Spec.MLKEM, including the loop invariants
4. `Hacspec_ml_kem.Serialize.fst` — definitions of `byte_encode` /
   `byte_decode` over `t_FieldElement`
5. `Spec.MLKEM.Math.fst` — `byte_encode` / `byte_decode` definitions
   (for understanding what the existing impl→Spec.MLKEM proof
   establishes)
6. `Hacspec_ml_kem.Commute.Chunk.fst` — existing per-element commute
   lemmas (A5, A6); add new chunk-commute lemmas here
7. `libcrux-ml-kem/proofs/proof-style-guide.md` §3.4–§3.6

## Architectural recipe

For `serialize_uncompressed_ring_element` (call it the template):

**Step 1**: Add Tier-1 chunk-commute lemma to
`Hacspec_ml_kem.Commute.Chunk.fst`:
```fstar
let lemma_byte_encode_12_chunk_commute
    (input: t_Array i16 (sz 16))
    (output: t_Array u8 (sz 24))
  : Lemma
    (requires
      (forall (i: nat). i < 16 ==> bounded (Seq.index input i) 12) /\
      Libcrux_ml_kem.Vector.Traits.Spec.serialize_post_N #(sz 16) 12 input output)
    (ensures
      output ==
        Hacspec_ml_kem.Serialize.byte_encode (sz 24) (sz 192)
          (createi (sz 16) (fun j ->
            { Hacspec_ml_kem.Parameters.f_val = mk_u16 (i16_to_spec_fe (Seq.index input (v j))) }))
          (sz 12))
    = ...
```
The proof goes through `bits_to_bytes ∘ bit_vec_of_nat_array` ↔
`BitVecEq.int_t_array_bitwise_eq` reasoning.  Look for existing
`bits_to_bytes_eq_bitwise_eq` or similar lemma in
`fstar-helpers/fstar-bitvec/`; the chunk-commute follows by argument
massaging.  If no such lemma, write a small one or admit-with-comment.

**Step 2**: Strengthen the loop invariant in `serialize_uncompressed_ring_element`
to maintain a "first-i-chunks-correct" hacspec invariant alongside the
existing Spec.MLKEM invariant.

**Step 3**: At loop exit, conclude `result ==
Hacspec_ml_kem.Serialize.serialize_uncompressed_ring_element ...` via
`Seq.lemma_eq_intro` against the chunk-wise array.

**Step 4**: Delete the corresponding `cite_*_post` predicate AND
`axiom_*` SMTPat lemma from `HacspecBridge.fst`.

Adapt the recipe to the other 3 targets.

## Operating constraints

- **Wall clock**: 180 min (3 h) total, generous because body proofs are
  much heavier than bridges.
- **Per-target budget**: ~40-45 min including the chunk-commute lemma.
  If a target doesn't go through, **restore the bridge axiom** for it,
  add an English comment in `HacspecBridge.fst` explaining what was
  attempted, commit, move on.
- **Memory**: `ulimit -v 8388608`, `--z3cliopt smt.memory_max_size=8000`.
- **F\* concurrency**: at most 1 F\* process at a time.
- **F\* rlimit**: never exceed 800.

## Code change policy

- **Rust function bodies**: editable for **loop invariant strengthening
  only**.  No algorithmic changes; no new branches; no reordering of
  statements.
- **`#[hax_lib::ensures(...)]`**: editable to remove the bridge cite once
  body proof discharges the Hacspec citation directly.  When ensures
  shape changes, update the function's hacspec citation form to match
  what the body proof actually establishes.
- **`HacspecBridge.fst`**: editable to DELETE the cite predicate /
  axiom for each function with a body proof.  DO NOT delete the 5
  remaining bridges.
- **`Hacspec_ml_kem.Commute.Chunk.fst`**: editable to add Tier-1
  chunk-commute lemmas.  Do NOT modify existing lemmas.
- **`Libcrux_ml_kem.Serialize.fst`** (extracted): never edited directly;
  changes flow from Rust source via `python3 hax.py extract`.

## Tooling

Plain `make` workflow:
- Inner loop: edit Rust → `python3 hax.py extract` (~14 s) → `make Libcrux_ml_kem.Serialize.fst.checked` (~30-80 s).
- Bridge / Chunk lemma iterations are F\*-direct: use fstar-mcp on port **3003** if iterating ≥5 times on `Hacspec_ml_kem.Commute.Chunk.fst` or `HacspecBridge.fst` content.

## Eager-commit logging

Continue updating `proofs/agent-status/agent-B.md` on the branch.
Append a `## Phase 7c body-proof follow-up (agent B')` section.
Commit eagerly with `agent-B': ...` prefix.

## Stop conditions

- 180 min wall clock exceeded
- All 4 targets handled (proven, or restored-bridge-with-detail)
- F\* segfault on same target twice
- Z3 OOM kill on same target twice

## Final deliverable

1. Final status commit on `agent-B.md`
2. `make Libcrux_ml_kem.Serialize.fst.checked` final regression, time recorded
3. Concise summary back to parent: count newly body-proven (0–4),
   bridges remaining in `HacspecBridge.fst`, last commit hash, any
   regressions or escalations

## Hard rules

- DO NOT push to origin.
- DO NOT merge to `trait-opacify`.
- DO NOT touch other agents' branches.
- DO NOT touch the 5 compress-family bridges.
- DO NOT regress any function whose body proof you didn't replace.
- DO NOT exceed F\* rlimit 800.
- DO NOT remove existing `Spec.MLKEM.*` citations (Phase 7k handles
  that — body proofs ADD a Hacspec cite; old Spec.MLKEM cites stay
  unless their proof breaks during loop-invariant strengthening, in
  which case both go through the new body proof).
